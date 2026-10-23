package benchcompare

import "testing"

var wireSink []byte
var rootSink [32]byte
var headerSink Header
var mixedSink Mixed

func BenchmarkHeader(b *testing.B) {
	value := header()
	wire, err := value.MarshalSSZ()
	if err != nil {
		b.Fatal(err)
	}
	b.Run("Encode", func(b *testing.B) { benchHeaderEncode(b, value) })
	b.Run("Decode", func(b *testing.B) { benchHeaderDecode(b, wire) })
	b.Run("Root", func(b *testing.B) { benchHeaderRoot(b, value) })
	b.Run("EncodeReuse", func(b *testing.B) { benchHeaderReuse(b, value, len(wire)) })
}
func benchHeaderEncode(b *testing.B, value *Header) {
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		var err error
		wireSink, err = value.MarshalSSZ()
		if err != nil {
			b.Fatal(err)
		}
	}
}
func benchHeaderDecode(b *testing.B, wire []byte) {
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		var decoded Header
		if err := decoded.UnmarshalSSZ(wire); err != nil {
			b.Fatal(err)
		}
		headerSink = decoded
	}
}
func benchHeaderRoot(b *testing.B, value *Header) {
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		var err error
		rootSink, err = value.HashTreeRoot()
		if err != nil {
			b.Fatal(err)
		}
	}
}
func benchHeaderReuse(b *testing.B, value *Header, size int) {
	buffer := make([]byte, 0, size)
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		var err error
		buffer, err = value.MarshalSSZTo(buffer[:0])
		if err != nil {
			b.Fatal(err)
		}
		wireSink = buffer
	}
}
func BenchmarkMixed(b *testing.B) {
	value := mixed()
	wire, err := value.MarshalSSZ()
	if err != nil {
		b.Fatal(err)
	}
	b.Run("Encode", func(b *testing.B) { benchMixedEncode(b, value) })
	b.Run("Decode", func(b *testing.B) { benchMixedDecode(b, wire) })
	b.Run("Root", func(b *testing.B) { benchMixedRoot(b, value) })
	b.Run("EncodeReuse", func(b *testing.B) { benchMixedReuse(b, value, len(wire)) })
}
func benchMixedEncode(b *testing.B, value *Mixed) {
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		var err error
		wireSink, err = value.MarshalSSZ()
		if err != nil {
			b.Fatal(err)
		}
	}
}
func benchMixedDecode(b *testing.B, wire []byte) {
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		var decoded Mixed
		if err := decoded.UnmarshalSSZ(wire); err != nil {
			b.Fatal(err)
		}
		mixedSink = decoded
	}
}
func benchMixedRoot(b *testing.B, value *Mixed) {
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		var err error
		rootSink, err = value.HashTreeRoot()
		if err != nil {
			b.Fatal(err)
		}
	}
}
func benchMixedReuse(b *testing.B, value *Mixed, size int) {
	buffer := make([]byte, 0, size)
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		var err error
		buffer, err = value.MarshalSSZTo(buffer[:0])
		if err != nil {
			b.Fatal(err)
		}
		wireSink = buffer
	}
}
