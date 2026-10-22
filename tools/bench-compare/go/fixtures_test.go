package benchcompare

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"testing"
)

type fixture struct {
	Name   string `json:"name"`
	Wire   string `json:"wire"`
	Root   string `json:"root"`
	SHA256 string `json:"sha256"`
}

func TestSharedFixtures(t *testing.T) {
	path := os.Getenv("NYX_BENCH_FIXTURES")
	if path == "" {
		t.Fatal("NYX_BENCH_FIXTURES must identify the Rust-verified shared fixtures")
	}
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	var fixtures []fixture
	if err := json.Unmarshal(data, &fixtures); err != nil {
		t.Fatal(err)
	}
	if len(fixtures) != 2 {
		t.Fatal("expected exactly two shared fixtures")
	}
	for index, name := range []string{"header", "mixed"} {
		f := fixtures[index]
		if f.Name != name {
			t.Fatal("fixture order/schema mismatch")
		}
		wire, err := hex.DecodeString(f.Wire)
		if err != nil {
			t.Fatal(err)
		}
		digest := sha256.Sum256(wire)
		if hex.EncodeToString(digest[:]) != f.SHA256 {
			t.Fatal("fixture digest mismatch")
		}
		var actual []byte
		var root [32]byte
		if name == "header" {
			actual, root = checkHeader(t, wire)
		} else {
			actual, root = checkMixed(t, wire)
		}
		if !bytes.Equal(wire, actual) || hex.EncodeToString(root[:]) != f.Root {
			t.Fatal("cross-library wire/root mismatch")
		}
	}
}

func checkHeader(t *testing.T, wire []byte) ([]byte, [32]byte) {
	actual, err := header().MarshalSSZ()
	if err != nil {
		t.Fatal(err)
	}
	root, err := header().HashTreeRoot()
	if err != nil {
		t.Fatal(err)
	}
	var decoded Header
	if err := decoded.UnmarshalSSZ(wire); err != nil {
		t.Fatal(err)
	}
	if decoded != *header() {
		t.Fatal("decoded header differs")
	}
	return actual, root
}

func checkMixed(t *testing.T, wire []byte) ([]byte, [32]byte) {
	actual, err := mixed().MarshalSSZ()
	if err != nil {
		t.Fatal(err)
	}
	root, err := mixed().HashTreeRoot()
	if err != nil {
		t.Fatal(err)
	}
	var decoded Mixed
	if err := decoded.UnmarshalSSZ(wire); err != nil {
		t.Fatal(err)
	}
	if decoded.Slot != 42 || !bytes.Equal(decoded.Payload, mixed().Payload) || len(decoded.Votes) != 1024 {
		t.Fatal("decoded mixed fields differ")
	}
	for _, vote := range decoded.Votes {
		if vote != 1 {
			t.Fatal("decoded vote differs")
		}
	}
	return actual, root
}
