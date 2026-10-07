//go:build !linux

package device

import (
	"github.com/fractal-networking/wireguard-go/conn"
	"github.com/fractal-networking/wireguard-go/rwcancel"
)

func (device *Device) startRouteListener(_ conn.Bind) (*rwcancel.RWCancel, error) {
	return nil, nil
}
