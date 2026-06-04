/* SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2017-2025 WireGuard LLC. All Rights Reserved.
 */

package device

import (
	"crypto/rand"
	"encoding/binary"
	"errors"
	"fmt"
	"net"
	"net/netip"
	"os"
	"sync"
	"time"

	"github.com/fractal-networking/wireguard-go/conn"
	"github.com/fractal-networking/wireguard-go/tun"
	"golang.org/x/crypto/chacha20poly1305"
	"golang.org/x/net/ipv4"
	"golang.org/x/net/ipv6"
)

/* Outbound flow
 *
 * 1. TUN queue
 * 2. Routing (sequential)
 * 3. Nonce assignment (sequential)
 * 4. Encryption (parallel)
 * 5. Transmission (sequential)
 *
 * The functions in this file occur (roughly) in the order in
 * which the packets are processed.
 *
 * Locking, Producers and Consumers
 *
 * The order of packets (per peer) must be maintained,
 * but encryption of packets happen out-of-order:
 *
 * The sequential consumers will attempt to take the lock,
 * workers release lock when they have completed work (encryption) on the packet.
 *
 * If the element is inserted into the "encryption queue",
 * the content is preceded by enough "junk" to contain the transport header
 * (to allow the construction of transport messages in-place)
 */

type QueueOutboundElement struct {
	buffer []byte // sing-allocated buffer holding the packet data
	// packet is always a slice of "buffer". The starting offset in buffer
	// is either:
	//  a) MessageEncapsulatingTransportSize+MessageTransportHeaderSize (plaintext)
	//  b) 0 (post-encryption)
	packet  []byte
	nonce   uint64   // nonce for encryption
	keypair *Keypair // keypair for encryption
	peer    *Peer    // related peer
}

type QueueOutboundElementsContainer struct {
	// filling is a one-shot barrier signaling encryption→send handoff.
	// SendStagedPackets calls Add(1) before sending the container down
	// the encryption and outbound queues; RoutineEncryption calls Done
	// after encrypting; RoutineSequentialSender calls Wait before
	// reading the encrypted packets.
	filling sync.WaitGroup
	elems   []*QueueOutboundElement
}

func (device *Device) NewOutboundElement() *QueueOutboundElement {
	elem := device.GetOutboundElement()
	elem.buffer = device.GetOutboundBuffer(MaxMessageSize)
	elem.nonce = 0
	// keypair and peer were cleared (if necessary) by clearPointers.
	return elem
}

// clearPointers clears elem fields that contain pointers.
// This makes the garbage collector's life easier and
// avoids accidentally keeping other objects around unnecessarily.
// It also reduces the possible collateral damage from use-after-free bugs.
func (elem *QueueOutboundElement) clearPointers() {
	elem.buffer = nil
	elem.packet = nil
	elem.keypair = nil
	elem.peer = nil
}

/* Queues a keepalive if no packets are queued for peer
 */
func (peer *Peer) SendKeepalive() {
	if len(peer.queue.staged) == 0 && peer.isRunning.Load() {
		peer.device.log.Verbosef("%v - Keepalive packet to endpoint: %s", peer, peer.endpoint.val.DstToString())

		if peer.warp.noise.enableNoiseGen {
			// peer.device.log.Verbosef("%v - Sending noise packets before sending a keepalive to WARP endpoint: %v", peer, peer.endpoint.val.DstToString())
			peer.sendRandomPackets()
		}

		elem := peer.device.NewOutboundElement()
		elemsContainer := peer.device.GetOutboundElementsContainer()
		elemsContainer.elems = append(elemsContainer.elems, elem)
		select {
		case peer.queue.staged <- elemsContainer:
			peer.queuedOutboundPackets.Add(1)
			peer.device.log.Verbosef("%v - Sending keepalive packet", peer)
		default:
			peer.device.PutOutboundBuffer(elem.buffer)
			peer.device.PutOutboundElement(elem)
			peer.device.PutOutboundElementsContainer(elemsContainer)
		}
	}
	peer.SendStagedPackets()
}

// SendPriorityMessage invokes the [PeerPriorityMessageFunc] callback if one is
// set, and queues the returned message for encryption and transmission if the
// current keypair is valid.
func (peer *Peer) SendPriorityMessage() {
	f := peer.device.priorityMsgFn.Load()
	if f == nil {
		return
	}
	keypair := peer.keypairs.Current()
	if keypair == nil || keypair.sendNonce.Load() >= RejectAfterMessages || time.Since(keypair.created) >= RejectAfterTime {
		// SendStagedPackets initializes a handshake when the keypair is invalid,
		// but we explicitly avoid that here. A priority message is only intended
		// to flow around symmetric session establishment, but it should never
		// trigger a new session. Reaching this branch due to nonce exhaustion
		// or keypair expiration is highly unlikely considering where
		// SendPriorityMessage is called (at current keypair establishment).
		return
	}

	// get plaintext message to send
	msg := (*f)(peer.handshake.remoteStatic)
	if len(msg) == 0 {
		return
	}
	if len(msg) > MaxPriorityMessageContentSize {
		peer.device.log.Verbosef("%v - Failed to queue priority message due to size", peer)
		return
	}

	// get pooled elements
	elem := peer.device.NewOutboundElement()
	elemsContainer := peer.device.GetOutboundElementsContainer()
	elemsContainer.elems = append(elemsContainer.elems, elem)
	packetQueued := false
	defer func() {
		if !packetQueued {
			peer.device.PutOutboundBuffer(elem.buffer)
			peer.device.PutOutboundElement(elem)
			peer.device.PutOutboundElementsContainer(elemsContainer)
		}
	}()

	// initialize outbound element
	const offset = MessageEncapsulatingTransportSize + MessageTransportHeaderSize
	n := copy(elem.buffer[offset:], msg)
	elem.packet = elem.buffer[offset : offset+n]
	elem.peer = peer
	elem.nonce = keypair.sendNonce.Add(1) - 1
	if elem.nonce >= RejectAfterMessages {
		keypair.sendNonce.Store(RejectAfterMessages)
		return
	}
	elem.keypair = keypair

	// add to parallel and sequential queue
	if peer.isRunning.Load() {
		elemsContainer.filling.Add(1)
		peer.queuedOutboundPackets.Add(1)
		peer.queue.outbound.c <- elemsContainer
		peer.device.queue.encryption.c <- elemsContainer
		packetQueued = true
	}
}

func (peer *Peer) SendHandshakeInitiation(isRetry bool) error {
	peer.device.log.Verbosef("%v - Handshaking with endpoint %s", peer, peer.endpoint.val.DstToString())

	if peer.warp.noise.enableNoiseGen {
		// peer.device.log.Verbosef("%v - Sending noise packets before handshaking with WARP endpoint: %s", peer, peer.endpoint.val.DstToString())
		peer.sendRandomPackets()
	}

	if !isRetry {
		peer.timers.handshakeAttempts.Store(0)
	}

	peer.handshake.mutex.RLock()
	if time.Since(peer.handshake.lastSentHandshake) < RekeyTimeout {
		peer.handshake.mutex.RUnlock()
		return nil
	}
	peer.handshake.mutex.RUnlock()

	peer.handshake.mutex.Lock()
	if time.Since(peer.handshake.lastSentHandshake) < RekeyTimeout {
		peer.handshake.mutex.Unlock()
		return nil
	}
	peer.handshake.lastSentHandshake = time.Now()
	peer.handshake.mutex.Unlock()

	peer.device.log.Verbosef("%v - Sending handshake initiation", peer)

	candidates := peer.resolveEndpoints()

	msg, err := peer.device.CreateMessageInitiation(peer)
	if err != nil {
		peer.device.log.Errorf("%v - Failed to create initiation message: %v", peer, err)
		return err
	}

	buf := make([]byte, MessageEncapsulatingTransportSize+MessageInitiationSize)
	packet := buf[MessageEncapsulatingTransportSize:]
	_ = msg.marshal(packet)
	peer.cookieGenerator.AddMacs(packet)

	peer.timersAnyAuthenticatedPacketTraversal()
	peer.timersAnyAuthenticatedPacketSent()

	if len(candidates) > 0 {
		err = peer.sendHandshakeBuffers([][]byte{buf}, candidates)
	} else {
		err = peer.SendBuffers([][]byte{buf})
	}
	if err != nil {
		peer.device.log.Errorf("%v - Failed to send handshake initiation: %v", peer, err)
	}
	peer.timersHandshakeInitiated()

	return err
}

func (peer *Peer) SendHandshakeResponse() error {
	peer.handshake.mutex.Lock()
	peer.handshake.lastSentHandshake = time.Now()
	peer.handshake.mutex.Unlock()

	peer.device.log.Verbosef("%v - Sending handshake response to %s", peer, peer.endpoint.val.DstToString())

	response, err := peer.device.CreateMessageResponse(peer)
	if err != nil {
		peer.device.log.Errorf("%v - Failed to create response message: %v", peer, err)
		return err
	}

	buf := make([]byte, MessageEncapsulatingTransportSize+MessageResponseSize)
	packet := buf[MessageEncapsulatingTransportSize:]
	_ = response.marshal(packet)
	peer.cookieGenerator.AddMacs(packet)

	err = peer.BeginSymmetricSession()
	if err != nil {
		peer.device.log.Errorf("%v - Failed to derive keypair: %v", peer, err)
		return err
	}

	peer.timersSessionDerived()
	peer.timersAnyAuthenticatedPacketTraversal()
	peer.timersAnyAuthenticatedPacketSent()

	// TODO: allocation could be avoided
	err = peer.SendBuffers([][]byte{buf})
	if err != nil {
		peer.device.log.Errorf("%v - Failed to send handshake response: %v", peer, err)
	}
	return err
}

func (device *Device) SendHandshakeCookie(initiatingElem *QueueHandshakeElement) error {
	device.log.Verbosef("Sending cookie response for denied handshake message for %v", initiatingElem.endpoint.DstToString())

	sender := binary.LittleEndian.Uint32(initiatingElem.packet[4:8])
	reply, err := device.cookieChecker.CreateReply(initiatingElem.packet, sender, initiatingElem.endpoint.DstToBytes())
	if err != nil {
		device.log.Errorf("Failed to create cookie reply: %v", err)
		return err
	}

	buf := make([]byte, MessageEncapsulatingTransportSize+MessageCookieReplySize)
	packet := buf[MessageEncapsulatingTransportSize:]
	_ = reply.marshal(packet)
	// TODO: allocation could be avoided
	device.net.bind.Send([][]byte{buf}, initiatingElem.endpoint, MessageEncapsulatingTransportSize)

	return nil
}

func (peer *Peer) keepKeyFreshSending() {
	keypair := peer.keypairs.Current()
	if keypair == nil {
		return
	}
	nonce := keypair.sendNonce.Load()
	if nonce > RekeyAfterMessages || (keypair.isInitiator && time.Since(keypair.created) > RekeyAfterTime) {
		peer.SendHandshakeInitiation(false)
	}
}

func (device *Device) RoutineReadFromTUN() {
	defer func() {
		device.log.Verbosef("Routine: TUN reader - stopped")
		device.state.stopping.Done()
		device.queue.encryption.wg.Done()
	}()

	device.log.Verbosef("Routine: TUN reader - started")

	var (
		batchSize   = device.BatchSize()
		readErr     error
		elems       = make([]*QueueOutboundElement, batchSize)
		bufs        = make([][]byte, batchSize)
		elemsByPeer = make(map[*Peer]*QueueOutboundElementsContainer, batchSize)
		count       = 0
		sizes       = make([]int, batchSize)
		offset      = MessageEncapsulatingTransportSize + MessageTransportHeaderSize
	)

	for i := range elems {
		elems[i] = device.NewOutboundElement()
		bufs[i] = elems[i].buffer[:]
	}

	defer func() {
		for _, elem := range elems {
			if elem != nil {
				device.PutOutboundBuffer(elem.buffer)
				device.PutOutboundElement(elem)
			}
		}
	}()

	for {
		// read packets
		count, readErr = device.tun.device.Read(bufs, sizes, offset)
		for i := 0; i < count; i++ {
			if sizes[i] < 1 {
				continue
			}

			elem := elems[i]
			elem.packet = bufs[i][offset : offset+sizes[i]]

			// lookup peer
			var peer *Peer
			switch elem.packet[0] >> 4 {
			case 4:
				if len(elem.packet) < ipv4.HeaderLen {
					continue
				}
				src := netip.AddrFrom4([4]byte(elem.packet[IPv4offsetSrc : IPv4offsetSrc+net.IPv4len]))
				dst := netip.AddrFrom4([4]byte(elem.packet[IPv4offsetDst : IPv4offsetDst+net.IPv4len]))
				peer = device.allowedips.LookupFromPacket(src, dst, elem.packet)

			case 6:
				if len(elem.packet) < ipv6.HeaderLen {
					continue
				}
				src := netip.AddrFrom16([16]byte(elem.packet[IPv6offsetSrc : IPv6offsetSrc+net.IPv6len]))
				dst := netip.AddrFrom16([16]byte(elem.packet[IPv6offsetDst : IPv6offsetDst+net.IPv6len]))
				peer = device.allowedips.LookupFromPacket(src, dst, elem.packet)

			default:
				device.log.Verbosef("Received packet with unknown IP version")
			}

			if peer == nil {
				continue
			}
			elemsForPeer, ok := elemsByPeer[peer]
			if !ok {
				elemsForPeer = device.GetOutboundElementsContainer()
				elemsByPeer[peer] = elemsForPeer
			}
			elemsForPeer.elems = append(elemsForPeer.elems, elem)
			elems[i] = device.NewOutboundElement()
			bufs[i] = elems[i].buffer[:]
		}

		for peer, elemsForPeer := range elemsByPeer {
			if peer.isRunning.Load() {
				peer.StagePackets(elemsForPeer)
				peer.SendStagedPackets()
			} else {
				for _, elem := range elemsForPeer.elems {
					device.PutOutboundBuffer(elem.buffer)
					device.PutOutboundElement(elem)
				}
				device.PutOutboundElementsContainer(elemsForPeer)
			}
			delete(elemsByPeer, peer)
		}

		if readErr != nil {
			if errors.Is(readErr, tun.ErrTooManySegments) {
				// TODO: record stat for this
				// This will happen if MSS is surprisingly small (< 576)
				// coincident with reasonably high throughput.
				device.log.Verbosef("Dropped some packets from multi-segment read: %v", readErr)
				continue
			}
			if !device.isClosed() {
				if !errors.Is(readErr, os.ErrClosed) {
					device.log.Errorf("Failed to read packet from TUN device: %v", readErr)
				}
				go device.Close()
			}
			return
		}
	}
}

// maxQueuedInputPackets bounds the staged+outbound backlog of a peer fed via
// InputPacket/InputPackets. Injected packets beyond it are dropped before they
// are copied into pooled message buffers, like a full qdisc: injection has no
// flow control, and the queues are bounded in containers (up to a full batch
// each), so without this cap a flood is buffered instead of dropped.
const maxQueuedInputPackets = 2048

func (device *Device) inputPacketPeer(destination []byte, packetSlices [][]byte) *Peer {
	var src, dst netip.Addr
	switch len(destination) {
	case net.IPv4len:
		dst = netip.AddrFrom4([4]byte(destination))
		var srcBytes [net.IPv4len]byte
		if !gatherPacketBytes(packetSlices, IPv4offsetSrc, srcBytes[:]) {
			return nil
		}
		src = netip.AddrFrom4(srcBytes)
	case net.IPv6len:
		dst = netip.AddrFrom16([16]byte(destination))
		var srcBytes [net.IPv6len]byte
		if !gatherPacketBytes(packetSlices, IPv6offsetSrc, srcBytes[:]) {
			return nil
		}
		src = netip.AddrFrom16(srcBytes)
	default:
		return nil
	}
	var ipPkt []byte
	if len(packetSlices) == 1 {
		ipPkt = packetSlices[0]
	}
	return device.allowedips.LookupFromPacket(src, dst, ipPkt)
}

func gatherPacketBytes(packetSlices [][]byte, offset int, destination []byte) bool {
	for _, packetSlice := range packetSlices {
		if offset >= len(packetSlice) {
			offset -= len(packetSlice)
			continue
		}
		n := copy(destination, packetSlice[offset:])
		destination = destination[n:]
		offset = 0
		if len(destination) == 0 {
			return true
		}
	}
	return false
}

func (device *Device) InputPacket(destination []byte, packetSlices [][]byte) {
	peer := device.inputPacketPeer(destination, packetSlices)
	if peer == nil {
		return
	}
	if peer.queuedOutboundPackets.Load() >= maxQueuedInputPackets {
		return
	}
	var totalLength int
	for _, packetSlice := range packetSlices {
		totalLength += len(packetSlice)
	}
	allocLength := MessageEncapsulatingTransportSize + MessageTransportHeaderSize + totalLength + PaddingMultiple + chacha20poly1305.Overhead
	if allocLength > MaxMessageSize {
		return
	}
	elem := device.GetOutboundElement()
	elem.buffer = device.GetOutboundBuffer(allocLength)
	elem.nonce = 0
	packet := elem.buffer[MessageEncapsulatingTransportSize+MessageTransportHeaderSize:]
	var n int
	for _, packetSlice := range packetSlices {
		n += copy(packet[n:], packetSlice)
	}
	elem.packet = packet[:n]
	elemsForPeer := device.GetOutboundElementsContainer()
	if peer.isRunning.Load() {
		elemsForPeer.elems = append(elemsForPeer.elems, elem)
		peer.StagePackets(elemsForPeer)
		peer.SendStagedPackets()
	} else {
		device.PutOutboundBuffer(elem.buffer)
		device.PutOutboundElement(elem)
		device.PutOutboundElementsContainer(elemsForPeer)
	}
}

type InputPacketRef struct {
	Destination  []byte
	PacketSlices [][]byte
}

func (device *Device) InputPackets(packets []*InputPacketRef) []*InputPacketRef {
	var unmatched []*InputPacketRef
	elemsByPeer := make(map[*Peer][]*QueueOutboundElementsContainer, len(packets))
	for _, packetRef := range packets {
		peer := device.inputPacketPeer(packetRef.Destination, packetRef.PacketSlices)
		if peer == nil {
			unmatched = append(unmatched, packetRef)
			continue
		}
		if peer.queuedOutboundPackets.Load() >= maxQueuedInputPackets {
			continue
		}
		var totalLength int
		for _, packetSlice := range packetRef.PacketSlices {
			totalLength += len(packetSlice)
		}
		allocLength := MessageEncapsulatingTransportSize + MessageTransportHeaderSize + totalLength + PaddingMultiple + chacha20poly1305.Overhead
		if allocLength > MaxMessageSize {
			continue
		}
		elem := device.GetOutboundElement()
		elem.buffer = device.GetOutboundBuffer(allocLength)
		elem.nonce = 0
		packet := elem.buffer[MessageEncapsulatingTransportSize+MessageTransportHeaderSize:]
		var n int
		for _, packetSlice := range packetRef.PacketSlices {
			n += copy(packet[n:], packetSlice)
		}
		elem.packet = packet[:n]
		containers := elemsByPeer[peer]
		if len(containers) == 0 || len(containers[len(containers)-1].elems) >= conn.IdealBatchSize {
			containers = append(containers, device.GetOutboundElementsContainer())
			elemsByPeer[peer] = containers
		}
		elemsForPeer := containers[len(containers)-1]
		elemsForPeer.elems = append(elemsForPeer.elems, elem)
	}
	for peer, containers := range elemsByPeer {
		if peer.isRunning.Load() {
			for _, elemsForPeer := range containers {
				peer.StagePackets(elemsForPeer)
			}
			peer.SendStagedPackets()
		} else {
			for _, elemsForPeer := range containers {
				for _, elem := range elemsForPeer.elems {
					device.PutOutboundBuffer(elem.buffer)
					device.PutOutboundElement(elem)
				}
				device.PutOutboundElementsContainer(elemsForPeer)
			}
		}
	}
	return unmatched
}

func (peer *Peer) StagePackets(elems *QueueOutboundElementsContainer) {
	peer.queuedOutboundPackets.Add(int32(len(elems.elems)))
	for {
		select {
		case peer.queue.staged <- elems:
			return
		default:
		}
		select {
		case tooOld := <-peer.queue.staged:
			peer.queuedOutboundPackets.Add(-int32(len(tooOld.elems)))
			for _, elem := range tooOld.elems {
				peer.device.PutOutboundBuffer(elem.buffer)
				peer.device.PutOutboundElement(elem)
			}
			peer.device.PutOutboundElementsContainer(tooOld)
		default:
		}
	}
}

func (peer *Peer) SendStagedPackets() {
top:
	if len(peer.queue.staged) == 0 || !peer.device.isUp() {
		return
	}

	keypair := peer.keypairs.Current()
	if keypair == nil || keypair.sendNonce.Load() >= RejectAfterMessages || time.Since(keypair.created) >= RejectAfterTime {
		peer.SendHandshakeInitiation(false)
		return
	}

	for {
		var elemsContainerOOO *QueueOutboundElementsContainer
		select {
		case elemsContainer := <-peer.queue.staged:
			i := 0
			for _, elem := range elemsContainer.elems {
				elem.peer = peer
				elem.nonce = keypair.sendNonce.Add(1) - 1
				if elem.nonce >= RejectAfterMessages {
					keypair.sendNonce.Store(RejectAfterMessages)
					if elemsContainerOOO == nil {
						elemsContainerOOO = peer.device.GetOutboundElementsContainer()
					}
					elemsContainerOOO.elems = append(elemsContainerOOO.elems, elem)
					continue
				} else {
					elemsContainer.elems[i] = elem
					i++
				}

				elem.keypair = keypair
			}
			elemsContainer.elems = elemsContainer.elems[:i]

			if elemsContainerOOO != nil {
				// Already counted at their original staging; StagePackets will count them again.
				peer.queuedOutboundPackets.Add(-int32(len(elemsContainerOOO.elems)))
				peer.StagePackets(elemsContainerOOO) // XXX: Out of order, but we can't front-load go chans
			}

			if len(elemsContainer.elems) == 0 {
				peer.device.PutOutboundElementsContainer(elemsContainer)
				goto top
			}

			// add to parallel and sequential queue
			if peer.isRunning.Load() {
				elemsContainer.filling.Add(1)
				peer.queue.outbound.c <- elemsContainer
				peer.device.queue.encryption.c <- elemsContainer
			} else {
				peer.queuedOutboundPackets.Add(-int32(len(elemsContainer.elems)))
				for _, elem := range elemsContainer.elems {
					peer.device.PutOutboundBuffer(elem.buffer)
					peer.device.PutOutboundElement(elem)
				}
				peer.device.PutOutboundElementsContainer(elemsContainer)
			}

			if elemsContainerOOO != nil {
				goto top
			}
		default:
			return
		}
	}
}

func (peer *Peer) FlushStagedPackets() {
	for {
		select {
		case elemsContainer := <-peer.queue.staged:
			peer.queuedOutboundPackets.Add(-int32(len(elemsContainer.elems)))
			for _, elem := range elemsContainer.elems {
				peer.device.PutOutboundBuffer(elem.buffer)
				peer.device.PutOutboundElement(elem)
			}
			peer.device.PutOutboundElementsContainer(elemsContainer)
		default:
			return
		}
	}
}

func calculatePaddingSize(packetSize, mtu int) int {
	lastUnit := packetSize
	if mtu == 0 {
		return ((lastUnit + PaddingMultiple - 1) & ^(PaddingMultiple - 1)) - lastUnit
	}
	if lastUnit > mtu {
		lastUnit %= mtu
	}
	paddedSize := min(((lastUnit + PaddingMultiple - 1) & ^(PaddingMultiple - 1)), mtu)
	return paddedSize - lastUnit
}

/* Encrypts the elements in the queue
 * and marks them for sequential consumption (by releasing the mutex)
 *
 * Obs. One instance per core
 */
func (device *Device) RoutineEncryption(id int) {
	var paddingZeros [PaddingMultiple]byte
	var nonce [chacha20poly1305.NonceSize]byte

	defer device.log.Verbosef("Routine: encryption worker %d - stopped", id)
	device.log.Verbosef("Routine: encryption worker %d - started", id)

	for elemsContainer := range device.queue.encryption.c {
		for _, elem := range elemsContainer.elems {
			// populate header fields
			header := elem.buffer[MessageEncapsulatingTransportSize : MessageEncapsulatingTransportSize+MessageTransportHeaderSize]

			fieldType := header[0:4]
			fieldReceiver := header[4:8]
			fieldNonce := header[8:16]

			binary.LittleEndian.PutUint32(fieldType, MessageTransportType)
			binary.LittleEndian.PutUint32(fieldReceiver, elem.keypair.remoteIndex)
			binary.LittleEndian.PutUint64(fieldNonce, elem.nonce)

			// pad content to multiple of 16
			paddingSize := calculatePaddingSize(len(elem.packet), int(device.tun.mtu.Load()))
			elem.packet = append(elem.packet, paddingZeros[:paddingSize]...)

			// encrypt content and release to consumer

			binary.LittleEndian.PutUint64(nonce[4:], elem.nonce)
			elem.packet = elem.keypair.send.Seal(
				header,
				nonce[:],
				elem.packet,
				nil,
			)

			// re-slice packet to include encapsulating transport space
			elem.packet = elem.buffer[:MessageEncapsulatingTransportSize+len(elem.packet)]
		}
		elemsContainer.filling.Done()
	}
}

func (peer *Peer) RoutineSequentialSender(maxBatchSize int) {
	device := peer.device
	defer func() {
		defer device.log.Verbosef("%v - Routine: sequential sender - stopped", peer)
		peer.stopping.Done()
	}()
	device.log.Verbosef("%v - Routine: sequential sender - started", peer)

	bufs := make([][]byte, 0, max(maxBatchSize, conn.IdealBatchSize))

	for elemsContainer := range peer.queue.outbound.c {
		if elemsContainer == nil {
			return
		}
		peer.processOutboundContainer(elemsContainer, bufs[:0])
	}
}

// processOutboundContainer waits for the encryption routine to finish
// filling elemsContainer, then sends the batch (or drops it, if the peer
// has been stopped) and returns the container to the pool.
//
// scratch is a length-0 slice used to assemble the per-packet buffers
// passed to SendBuffers; its backing array is reused across calls.
func (peer *Peer) processOutboundContainer(elemsContainer *QueueOutboundElementsContainer, scratch [][]byte) {
	// Invariants from RoutineSequentialSender; all should be unreachable.
	if len(scratch) != 0 || cap(scratch) == 0 {
		panic(fmt.Sprintf("processOutboundContainer: scratch must be empty with non-zero cap; got len=%d cap=%d",
			len(scratch), cap(scratch)))
	}
	if cap(scratch) < len(elemsContainer.elems) {
		panic(fmt.Sprintf("processOutboundContainer: scratch cap %d < elems %d",
			cap(scratch), len(elemsContainer.elems)))
	}

	device := peer.device
	defer device.PutOutboundElementsContainer(elemsContainer)

	// Wait for RoutineEncryption to finish filling the container. After
	// Wait returns we have happens-before with that goroutine and are the
	// sole owner of the container until Put hands it back to the pool.
	elemsContainer.filling.Wait()

	if !peer.isRunning.Load() {
		// peer has been stopped; return re-usable elems to the shared pool.
		// This is an optimization only. It is possible for the peer to be stopped
		// immediately after this check, in which case, elem will get processed.
		// The timers and SendBuffers code are resilient to a few stragglers.
		// TODO: rework peer shutdown order to ensure
		// that we never accidentally keep timers alive longer than necessary.
		peer.queuedOutboundPackets.Add(-int32(len(elemsContainer.elems)))
		for _, elem := range elemsContainer.elems {
			device.PutOutboundBuffer(elem.buffer)
			device.PutOutboundElement(elem)
		}
		return
	}

	dataSent := false
	for _, elem := range elemsContainer.elems {
		if len(elem.packet[MessageEncapsulatingTransportSize:]) != MessageKeepaliveSize {
			dataSent = true
		}
		scratch = append(scratch, elem.packet)
	}

	peer.timersAnyAuthenticatedPacketTraversal()
	peer.timersAnyAuthenticatedPacketSent()

	err := peer.SendBuffers(scratch)
	if dataSent {
		peer.timersDataSent()
	}
	peer.queuedOutboundPackets.Add(-int32(len(elemsContainer.elems)))
	for _, elem := range elemsContainer.elems {
		device.PutOutboundBuffer(elem.buffer)
		device.PutOutboundElement(elem)
	}
	if err != nil {
		if errGSO, ok := errors.AsType[conn.ErrUDPGSODisabled](err); ok {
			device.log.Verbosef(err.Error())
			err = errGSO.RetryErr
		}
	}
	if err != nil {
		device.log.Errorf("%v - Failed to send data packets: %v", peer, err)
		return
	}

	peer.keepKeyFreshSending()
}

// Helper functions for sendRandomPackets
func generateRandomInt(min, max int) int {
	if min >= max {
		return min
	}
	diff := max - min + 1
	randomBytes := make([]byte, 4)
	rand.Read(randomBytes)
	randomNum := int(binary.BigEndian.Uint32(randomBytes))
	if randomNum < 0 {
		randomNum = -randomNum
	}
	return min + (randomNum % diff)
}

func encodeVarInt(value uint64) []byte {
	if value < 64 {
		return []byte{byte(value)}
	} else if value < 16384 {
		bytes := make([]byte, 2)
		binary.BigEndian.PutUint16(bytes, uint16(value)|0x4000)
		return bytes
	} else if value < 1073741824 {
		bytes := make([]byte, 4)
		binary.BigEndian.PutUint32(bytes, uint32(value)|0x80000000)
		return bytes
	} else {
		bytes := make([]byte, 8)
		binary.BigEndian.PutUint64(bytes, value|0xC000000000000000)
		return bytes
	}
}

func generateRandomFloat() float64 {
	randomBytes := make([]byte, 8)
	rand.Read(randomBytes)
	return float64(binary.BigEndian.Uint64(randomBytes)) / float64(^uint64(0))
}

func generateLongHeader(headerByte byte, srcConnID, dstConnID []byte, packetNumber uint64) []byte {
	header := make([]byte, 0, 32)

	// QUIC long header with flags
	flags := byte(generateRandomInt(0, 3))
	header = append(header, headerByte|flags)

	// QUIC version 1
	header = append(header, 0x00, 0x00, 0x00, 0x01)

	// Connection IDs
	header = append(header, byte(len(dstConnID)))
	header = append(header, dstConnID...)
	header = append(header, byte(len(srcConnID)))
	header = append(header, srcConnID...)

	// Token (for Initial packets)
	if headerByte == 0xC0 {
		header = append(header, 0x00)
	}

	// Length placeholder
	header = append(header, 0x40, 0x64)

	// Packet number
	header = append(header, byte(packetNumber&0xFF))

	return header
}

func generateShortHeader(headerByte byte, connID []byte, packetNumber uint64) []byte {
	header := make([]byte, 0, 16)

	// QUIC short header with flags
	flags := byte(generateRandomInt(0, 7))
	header = append(header, headerByte|flags)

	// Connection ID
	header = append(header, connID...)

	// Packet number
	header = append(header, byte(packetNumber&0xFF))

	return header
}

func generateCryptoFrame(maxSize int, packetNumber uint64) []byte {
	if maxSize < 20 {
		return make([]byte, maxSize)
	}

	frame := []byte{0x06} // CRYPTO frame

	offset := packetNumber * 100
	frame = append(frame, encodeVarInt(offset)...)

	dataLen := generateRandomInt(50, maxSize-len(frame)-8)
	frame = append(frame, encodeVarInt(uint64(dataLen))...)

	// TLS 1.3 handshake data
	tlsData := make([]byte, dataLen)
	if dataLen > 5 {
		tlsData[0] = 0x16 // TLS Handshake
		tlsData[1] = 0x03
		tlsData[2] = 0x03
		binary.BigEndian.PutUint16(tlsData[3:5], uint16(dataLen-5))

		if dataLen > 10 {
			// Mix of ClientHello, ServerHello, Certificate, etc.
			handshakeTypes := []byte{0x01, 0x02, 0x0B, 0x14}
			tlsData[5] = handshakeTypes[generateRandomInt(0, len(handshakeTypes)-1)]
			rand.Read(tlsData[6:])
		}
	} else {
		rand.Read(tlsData)
	}

	frame = append(frame, tlsData...)
	return frame
}

func generateHTTP3SetupFrames(maxSize int, streamID uint64) []byte {
	if maxSize < 20 {
		return make([]byte, maxSize)
	}

	frame := []byte{0x08} // STREAM frame, no flags for simplicity
	frame = append(frame, encodeVarInt(streamID)...)

	// HTTP/3 frames can include SETTINGS, HEADERS, DATA
	remainingSpace := maxSize - len(frame) - 10

	if generateRandomFloat() < 0.4 {
		// HTTP/3 SETTINGS frame
		http3Data := generateHTTP3Settings(remainingSpace)
		frame = append(frame, encodeVarInt(uint64(len(http3Data)))...)
		frame = append(frame, http3Data...)
	} else {
		// HTTP/3 HEADERS frame (for initial requests)
		http3Data := generateHTTP3Headers(remainingSpace, false)
		frame = append(frame, encodeVarInt(uint64(len(http3Data)))...)
		frame = append(frame, http3Data...)
	}

	return frame
}

func generateMASQUEConnectFrames(maxSize int, streamID uint64, requestNum int) []byte {
	if maxSize < 30 {
		return make([]byte, maxSize)
	}

	frame := []byte{0x08} // STREAM frame
	frame = append(frame, encodeVarInt(streamID)...)

	remainingSpace := maxSize - len(frame) - 10

	// Generate MASQUE CONNECT-UDP or CONNECT-IP request
	var http3Data []byte
	if requestNum%2 == 0 {
		http3Data = generateMASQUEConnectUDP(remainingSpace)
	} else {
		http3Data = generateMASQUEConnectIP(remainingSpace)
	}

	frame = append(frame, encodeVarInt(uint64(len(http3Data)))...)
	frame = append(frame, http3Data...)

	return frame
}

func generateProxiedTrafficFrames(maxSize int, streamID uint64, packetNumber uint64) []byte {
	if maxSize < 20 {
		return make([]byte, maxSize)
	}

	frame := []byte{0x08} // STREAM frame
	frame = append(frame, encodeVarInt(streamID)...)

	remainingSpace := maxSize - len(frame) - 10

	// Generate proxied packet data (could be UDP or IP)
	proxiedData := generateProxiedPacketData(remainingSpace, packetNumber)

	frame = append(frame, encodeVarInt(uint64(len(proxiedData)))...)
	frame = append(frame, proxiedData...)

	return frame
}

func generateHTTP3Settings(maxSize int) []byte {
	if maxSize < 10 {
		return make([]byte, maxSize)
	}

	data := make([]byte, 0, maxSize)

	// HTTP/3 SETTINGS frame type
	data = append(data, 0x04)

	settingsData := make([]byte, 0, maxSize-5)

	// Common HTTP/3 settings
	settings := []struct{ id, value uint64 }{
		{0x06, 4096}, // SETTINGS_MAX_HEADER_LIST_SIZE
		{0x08, 100},  // SETTINGS_NUM_PLACEHOLDERS
		{0x0a, 1},    // SETTINGS_H3_DATAGRAM
	}

	for _, setting := range settings {
		if len(settingsData)+10 < maxSize-5 {
			settingsData = append(settingsData, encodeVarInt(setting.id)...)
			settingsData = append(settingsData, encodeVarInt(setting.value)...)
		}
	}

	data = append(data, encodeVarInt(uint64(len(settingsData)))...)
	data = append(data, settingsData...)

	return data
}

func generateHTTP3Headers(maxSize int, isResponse bool) []byte {
	if maxSize < 15 {
		return make([]byte, maxSize)
	}

	data := make([]byte, 0, maxSize)

	// HTTP/3 HEADERS frame type
	data = append(data, 0x01)

	var headerData []byte
	if isResponse {
		// MASQUE response headers
		headerData = []byte{
			0x00, 0x00, 0x19, 0x07, // :status 200
			0x00, 0x01, 0x37, // content-type: application/masque-udp-proxying
		}
	} else {
		// MASQUE request headers
		headerData = []byte{
			0x00, 0x00, 0x03, 0x07, // :method CONNECT
			0x00, 0x01, 0x01, // :protocol masque
			0x00, 0x05, 0x16, // :authority proxy.example.com
		}
	}

	// Pad with additional QPACK encoded headers
	if len(headerData) < maxSize-10 {
		padding := generateRandomInt(0, maxSize-len(headerData)-10)
		extraHeaders := make([]byte, padding)
		rand.Read(extraHeaders)
		headerData = append(headerData, extraHeaders...)
	}

	data = append(data, encodeVarInt(uint64(len(headerData)))...)
	data = append(data, headerData...)

	return data
}

func generateMASQUEConnectUDP(maxSize int) []byte {
	// Generate HTTP/3 HEADERS frame for CONNECT-UDP request
	data := generateHTTP3Headers(maxSize/2, false)

	// Add some randomness to simulate different target hosts/ports
	if len(data) < maxSize-20 {
		// Simulate target endpoint variation in headers
		targetInfo := make([]byte, generateRandomInt(10, 20))
		rand.Read(targetInfo)
		data = append(data, targetInfo...)
	}

	return data
}

func generateMASQUEConnectIP(maxSize int) []byte {
	// Similar to CONNECT-UDP but for IP proxying
	data := generateHTTP3Headers(maxSize/2, false)

	// IP-specific header variations
	if len(data) < maxSize-15 {
		ipInfo := make([]byte, generateRandomInt(8, 15))
		rand.Read(ipInfo)
		data = append(data, ipInfo...)
	}

	return data
}

func generateProxiedPacketData(maxSize int, packetNumber uint64) []byte {
	if maxSize < 10 {
		return make([]byte, maxSize)
	}

	data := make([]byte, 0, maxSize)

	// HTTP/3 DATA frame containing proxied packet
	data = append(data, 0x00) // DATA frame type

	// Generate realistic proxied packet content
	proxiedSize := generateRandomInt(20, maxSize-10)
	proxiedPacket := make([]byte, proxiedSize)

	// Sometimes make it look like common protocols
	r := generateRandomFloat()
	if r < 0.3 {
		// Simulate DNS query/response
		if proxiedSize >= 12 {
			binary.BigEndian.PutUint16(proxiedPacket[0:2], uint16(packetNumber&0xFFFF)) // Transaction ID
			proxiedPacket[2] = 0x01                                                     // Standard query
			proxiedPacket[3] = 0x00
			rand.Read(proxiedPacket[4:])
		}
	} else if r < 0.6 {
		// Simulate QUIC-over-MASQUE (nested QUIC)
		if proxiedSize >= 16 {
			proxiedPacket[0] = 0x40 | byte(generateRandomInt(0, 7)) // QUIC short header
			rand.Read(proxiedPacket[1:9])                           // Connection ID
			rand.Read(proxiedPacket[9:])                            // Rest of packet
		}
	} else {
		// Generic UDP/IP data
		rand.Read(proxiedPacket)
	}

	data = append(data, encodeVarInt(uint64(len(proxiedPacket)))...)
	data = append(data, proxiedPacket...)

	return data
}

/* Generates and writes random a amount of dummy packets to mask Cloudflare WARP handshakes and circumvent blockings
 */
func (peer *Peer) sendRandomPackets() {
	// MASQUE operates over HTTP/3, which runs over QUIC
	connectionID := make([]byte, 8)
	peerConnectionID := make([]byte, 8)
	rand.Read(connectionID)
	rand.Read(peerConnectionID)

	// MASQUE connection phases:
	// 1. QUIC/HTTP3 handshake
	// 2. HTTP/3 CONNECT-UDP or CONNECT-IP requests
	// 3. Proxied UDP/IP traffic over HTTP/3 streams
	// 4. Bidirectional data flow

	masquePhases := []struct {
		name        string
		headerByte  byte
		minSize     int
		maxSize     int
		packets     int
		description string
	}{
		{"QUIC_Initial", 0xC0, 1200, 1452, generateRandomInt(2, 4), "QUIC handshake initiation"},
		{"QUIC_Handshake", 0xD0, 200, 1200, generateRandomInt(2, 4), "QUIC handshake completion"},
		{"HTTP3_Setup", 0x40, 100, 800, generateRandomInt(3, 6), "HTTP/3 stream setup and SETTINGS"},
		{"MASQUE_Connect", 0x40, 200, 1000, generateRandomInt(2, 4), "CONNECT-UDP/CONNECT-IP requests"},
		{"Proxied_Traffic", 0x40, 64, 1400, generateRandomInt(10, 30), "Proxied UDP/IP packets over HTTP/3"},
	}

	packetNumber := uint64(0)
	totalPackets := 0
	streamID := uint64(0)

	for phaseIdx, phase := range masquePhases {
		for i := 0; i < phase.packets; i++ {
			if peer.device.isClosed() || !peer.isRunning.Load() {
				return
			}

			totalPackets++
			if totalPackets > peer.warp.noise.packetCountMax {
				return
			}

			packetNumber++
			packetSize := generateRandomInt(phase.minSize, phase.maxSize)

			// Generate QUIC header
			var header []byte
			if phase.headerByte == 0x40 {
				header = generateShortHeader(phase.headerByte, peerConnectionID, packetNumber)
			} else {
				header = generateLongHeader(phase.headerByte, connectionID, peerConnectionID, packetNumber)
			}

			// Generate phase-specific frames
			frameSpace := packetSize - len(header) - 16 // Reserve for auth tag
			var frames []byte

			switch phaseIdx {
			case 0, 1: // QUIC handshake phases
				frames = generateCryptoFrame(frameSpace, packetNumber)
			case 2: // HTTP/3 setup
				streamID += 4 // HTTP/3 uses specific stream ID patterns
				frames = generateHTTP3SetupFrames(frameSpace, streamID)
			case 3: // MASQUE CONNECT requests
				streamID += 4
				frames = generateMASQUEConnectFrames(frameSpace, streamID, i)
			case 4: // Proxied traffic
				streamID += uint64(generateRandomInt(0, 8)) // Multiple concurrent streams
				frames = generateProxiedTrafficFrames(frameSpace, streamID, packetNumber)
			}

			// Build final packet
			packet := make([]byte, 0, packetSize)
			packet = append(packet, header...)
			packet = append(packet, frames...)

			// Add QUIC authentication tag
			authTag := make([]byte, 16)
			rand.Read(authTag)
			packet = append(packet, authTag...)

			// Pad to exact size
			if len(packet) < packetSize {
				padding := make([]byte, packetSize-len(packet))
				packet = append(packet, padding...)
			} else if len(packet) > packetSize {
				packet = packet[:packetSize]
			}

			// Prevent setting reserved on noise packets
			dstAddrPort, err := conn.EndpointDstAddrPort(peer.endpoint.val)
			if err != nil {
				return
			}
			peer.device.net.bind.SetReservedForEndpoint(dstAddrPort, [3]uint8{})
			// Send packet
			err = peer.SendBuffers([][]byte{packet})
			if err != nil {
				return
			}

			// Reset setting reserved for regular packets
			peer.device.net.bind.SetReservedForEndpoint(dstAddrPort, peer.reserved)

			// MASQUE-specific timing patterns
			var baseDelay time.Duration
			switch phaseIdx {
			case 0, 1: // QUIC handshake
				baseDelay = time.Duration(generateRandomInt(20, 150)) * time.Millisecond
			case 2: // HTTP/3 setup
				baseDelay = time.Duration(generateRandomInt(10, 100)) * time.Millisecond
			case 3: // MASQUE CONNECT
				baseDelay = time.Duration(generateRandomInt(50, 200)) * time.Millisecond
			case 4: // Proxied traffic
				// More frequent, bursty patterns typical of proxied traffic
				if generateRandomFloat() < 0.3 {
					baseDelay = time.Duration(generateRandomInt(1, 10)) * time.Millisecond
				} else {
					baseDelay = time.Duration(generateRandomInt(5, 50)) * time.Millisecond
				}
			}

			jitter := time.Duration(generateRandomInt(peer.warp.noise.packetDelayMin, peer.warp.noise.packetDelayMax)) * time.Millisecond
			time.Sleep(baseDelay + jitter)

			// Simulate bursts during proxied traffic phase
			if phaseIdx == 4 && generateRandomFloat() < 0.15 {
				burstSize := generateRandomInt(2, 6)
				for j := 0; j < burstSize && totalPackets < peer.warp.noise.packetCountMax; j++ {
					// Send burst with minimal delay
					time.Sleep(time.Duration(generateRandomInt(1, 5)) * time.Millisecond)
					totalPackets++
				}
			}

			if totalPackets >= peer.warp.noise.packetCountMin && generateRandomFloat() < 0.1 {
				return
			}
		}

		// Longer pause between major phases
		if phaseIdx < len(masquePhases)-1 {
			time.Sleep(time.Duration(generateRandomInt(20, 100)) * time.Millisecond)
		}
	}
}
