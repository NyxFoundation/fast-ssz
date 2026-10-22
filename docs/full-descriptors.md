---
title: Full descriptor native implementation
last_updated: 2026-10-21
status: native-tested-formal-integration-pending
---
# Full descriptor metadata

This preparatory change implements native metadata for every constructor of
`Ssz.Desc` at specification revision `c68b96a852559284cc4311b6c14105bcf51ac6ce`.
It does **not** complete Container/ProgressiveContainer/CompatibleUnion value
codecs, derive, or generated conversions. No public metadata methods were added;
the existing four `codec` APIs continue to derive metadata from `Ssz::TYPE`.

## Representation and behavior

- Existing Boolean/Uint/Vector/List/ProgressiveList variants are retained.
- ByteVector, ByteList, BitVector, BitList and ProgressiveBitList retain native
  counts and optional bounds, including zero and `usize::MAX`.
- Container stores independent static name and child arrays. ProgressiveContainer
  additionally stores its complete Boolean mask; CompatibleUnion stores independent
  selector and child arrays. Malformed array lengths remain representable.
- Static declarations require no metadata-construction allocation. All four internal
  metadata implementations are const. Name equality compares the complete UTF-8
  encoding safely, preserving embedded NUL, empty names and non-normalized spellings.
- Only Boolean and Uint are basic. ByteVector/ByteList have the same layouts as
  equal-bound Vector/List of exactly Uint(1), not Boolean or ProgressiveList.
- Fixed bit widths use overflow-free byte rounding. Container widths sum children,
  not positions or names. Empty internal field lists have width zero even though
  empty container declarations are invalid. Any variable field cancels an earlier
  or later fixed-width overflow. A zero-count vector cancels fixed overflow but
  never makes a variable child fixed.
- Structural equality preserves optional bounds, names, masks, selectors and every
  child. Compatibility short-circuits structural equality even for malformed
  declarations. It ignores only the capacities the reference ignores.
- Progressive placement zips active positions with names, not children; extra names
  and positions truncate exactly as in the reference. Shared positions need the
  same name and compatible children; distinct positions need distinct names. No
  validation assumptions are used. Union comparison checks every cross-pair;
  compatibility is not transitive.
- Validation follows `Type/Valid.lean`: container empty/count/duplicate/child order;
  progressive width/last-gap/max256/empty/active-count/name-count/duplicate/child
  order; union empty/count/duplicate/range/children/all-pairs order. Selector range
  is exactly 1 through 127. Lists still validate children at zero capacity.

## New error categories

Existing categories and their formal mappings are unchanged. New unit variants
classify only these reference reasons, like existing `CodecError` categories;
reference numeric diagnostics are not a new Rust error-data API.

| Rust variant | Reference constructor | Reason |
| --- | --- | --- |
| EmptyContainer | containerEmpty | CONTAINER_EMPTY |
| BadDeclaration | badDeclaration | BAD_DECLARATION |
| LayoutWidth | layoutWidth | LAYOUT_WIDTH |
| LayoutTrailingGap | layoutTrailingGap | LAYOUT_TRAILING_GAP |
| LayoutTooWide | layoutTooWide | LAYOUT_TOO_WIDE |
| LayoutFieldCount | layoutFieldCount | LAYOUT_FIELD_COUNT |
| EmptyUnion | unionEmpty | UNION_EMPTY |
| UnionSelectorRepeated | unionSelectorRepeated | UNION_SELECTOR_REPEATED |
| UnionSelectorRange | unionSelectorRange | UNION_SELECTOR_RANGE |
| UnionIncompatible | unionIncompatible | UNION_INCOMPATIBLE |

The strict new formal reason pairs must be added during formal integration; the
existing `codecFaultAgrees`/`CodecLaw` files have not been edited in this native phase.

## Native checks

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo llvm-cov --workspace --fail-under-lines 80
python3 scripts/descriptor_reference.py check
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/official_vectors.py check --family boolean --family uints --family basic_vector \
  --family bitvector --family bitlist --family progressive_bitlist --family basic_progressive_list
```

The descriptor tests were written first and failed because constructors/errors
were missing. Targeted tests cover zero/MAX bounds, rounding, nested overflow,
variable fields on both sides of overflowing fields, Unicode/NUL/empty names,
malformed counts, mask boundaries, every selector from 0 through 128 plus MAX,
error precedence, structural equality versus compatibility, invalid reflexivity
shortcuts, nontransitivity and later-option union clashes. Const-evaluation tests
exercise all four helpers; external metadata-only dictionaries exercise existing
public APIs without invoking value codecs.

`descriptor_reference.py` evaluates the actual clean pinned Lean specification,
not a Python reimplementation, and checks the committed native test data. Its 298
declarations include all 13 constructors and exhaustive selected malformed
mask/name/field and selector/option products. All 88,804 ordered compatibility
pairs, widths, classification and validation reasons are compared with Rust.
This is finite differential testing, **not** a universal proof. Native MAX cases
are separately tested without allocating values of those declared sizes.

Checkpoint evidence: fmt and warnings-as-errors Clippy passed; workspace tests
passed (189 native tests and 13 doctests); all 102 Python tests and all 3,412
selected official source cases passed. LLVM library line coverage is 96.05%;
`type_info.rs` line coverage is 99.74% (all 27 functions executed). The one
uncovered metadata line is the Boolean compatibility match arm, already handled
by the preceding exact structural-equality shortcut. No coverage threshold was
lowered or source region excluded.

## Exact outstanding formal dependency

The approved Aeneas repair is being prepared separately. The first private bridge
revision is insufficient: `Str` must enforce valid UTF-8, literal construction
must avoid native-decision axioms, and the final published immutable toolchain
must supply the faithful total `Str` → `String` observation. No candidate pin,
foreign axiom, temporary name observation or UTF-8 premise is introduced here.

Once that immutable repair is supplied, the next stage must re-extract the real
Rust functions, extend `typeDescriptorToSpec` with every name/mask/selector/child
and optional bound, extend only the strict new fault pairs, and prove metadata
for every finite declaration and native bound without validity assumptions.
Then the unchanged 79-operation/10-dictionary proof gate, exact-artifact checks,
all dictionary laws and 3,412 official source cases must be rerun. Existing
proofs/generated artifacts are preserved but stale; no full formal gate is claimed.
The existing cyclic external-static-graph trust boundary is unchanged.
