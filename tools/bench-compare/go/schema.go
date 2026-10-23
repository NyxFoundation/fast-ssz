package benchcompare

//go:generate go run github.com/ferranbt/fastssz/sszgen -path . -objs Header,Mixed -output encoding.go

type Header struct {
	Slot          uint64
	ProposerIndex uint64
	ParentRoot    [32]byte `ssz-size:"32"`
	StateRoot     [32]byte `ssz-size:"32"`
	BodyRoot      [32]byte `ssz-size:"32"`
}
type Mixed struct {
	Slot    uint64
	Payload []byte   `ssz-max:"4096"`
	Votes   []uint64 `ssz-max:"1024"`
}

func header() *Header {
	value := &Header{Slot: 0x0102030405060708, ProposerIndex: 0x1122334455667788}
	for i := 0; i < 32; i++ {
		value.ParentRoot[i] = byte(i)
		value.StateRoot[i] = byte(128 + i)
		value.BodyRoot[i] = byte(224 + i)
	}
	return value
}
func mixed() *Mixed {
	value := &Mixed{Slot: 42, Payload: make([]byte, 4096), Votes: make([]uint64, 1024)}
	for i := range value.Payload {
		value.Payload[i] = 7
	}
	for i := range value.Votes {
		value.Votes[i] = 1
	}
	return value
}
