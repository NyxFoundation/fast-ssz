---
title: Verification scope and trust boundary
last_updated: 2026-10-21
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Verification scope and trust boundary

**Not release complete:** Boolean, uint8/16/32/64/128/256, Bitvector/Bitlist/ProgressiveBitlist and borrowed
ByteVector/ByteList/ProgressiveByteList codecs, SHA-256 node combination and
single-branch Merkle verification, generic node Merkleization and all basic-type
roots, plus borrowed packed byte/bit and Progressive/view roots, are implemented.
`verification/targets.json` links seventy-nine registered operations to proofs over actual
Aeneas output: the thirty-nine existing codec/hash/view operations, six owned collection
storage operations, three generic codec dispatchers, numeric offset-span validation,
fixed/variable-vector/list layout validation, three immutable layout-view projections and typed
body-range decoding, four declaration-derived metadata APIs, eleven generalized-index operations and
seven packed byte/bit root entrypoints. `verification/traits.json` separately
registers every public `Ssz` declaration member and its ten library dictionaries: seven basic
instances and three generic Vector/List/unbounded-ProgressiveList constructors. Each proves the full `CodecLaw`;
methods are not silently excluded. The three generic laws compose with the law of their actual
child dictionary, at every machine-size bound and arbitrary nesting depth.
Every slice/bound yields `RustM.ok`; success contains exact reference bytes/values.
Conversion preserves bits, order and length. Byte codecs validate `Desc.wellFormed`.
Their relation permits only EmptyVector/vectorEmpty, InvalidLength/scope and
OverLimit/overLimit; other outcomes are false. Boolean errors classify scope/non-bit
faults. Bounds cover `usize`, not all naturals. Zero-copy is source/test evidence,
not a cost theorem. Derived error traits are not protocol proof targets.

ProgressiveByteList is checked against `.progressiveList (.uint 1) limit`, not
an opaque-byte descriptor. Its injective value view maps every byte to a uint8,
preserving order and length. The sequence layout and singleton-byte slicing are
proved to encode/decode exactly the borrowed input. `None` imposes no declared
capacity; optional capacities cover every `usize`. Both forms enforce the pinned
reference's sequence size of less than 2^32 bytes. Above that size, serialization
checks capacity first and deserialization checks offset width first; both error
precedences are proved, including inputs too large to allocate in unit tests.

Unsigned native codecs reuse Rust's standard little-endian and checked slice/array
conversions. Their actual models are proved against `Ssz.serialize`/`Ssz.deserialize`
for every value and input slice. Generic bitvector/byte lemmas establish both
encoding order and decoding value; only incorrect lengths are refused.
`U256` is `ruint::Uint<256, 4>` pinned to 1.20.1. Its value view concatenates all
four least-significant-first limbs, preserving all 256 bits. The reached library
getters, constructor, mask/count checks and Rust's `usize::div_ceil` are extracted
as real definitions and their required calls are proved. Ruint's unsafe byte casts
and arithmetic APIs are neither used nor covered. No library-correctness axiom is added.

Bitvector codecs cover every `usize` declaration and typed input, including
zero-length declarations, wrong lengths and noncanonical high padding. Their
actual Vec loops are proved terminating with decreasing natural measures; byte
counts, indices, shifts and increments are proved safe. The value view preserves
Boolean order exactly. Bitlist proofs cover delimiter insertion, empty values,
byte-boundary crossings, every final-byte pattern, capacity violations and the
separate empty-encoding/no-delimiter/trailing-zero error classes. Decoder byte-to-bit
arithmetic is guarded before multiplication/addition; both guards are proved equivalent
to the reference's natural-number count check. The all-zero scan has a decreasing
measure and prefix invariant. Vec allocation uses Aeneas's model; OS/resource failures
remain outside the guarantee.

ProgressiveBitlist accepts optional capacities, including no capacity, without
imposing a new format limit. The borrowed `BitListView` stores only validated,
immutable encoded bytes. Its value view is the reference's packed-bit decoding,
not a projection discarding bit contents. Returned views are proved nonempty and
canonical; their length getter's nonempty precondition is discharged by the decoder
and preserved by private fields and borrowing. The exact storage getter is also
audited. Bit counts use `u128` as an implementation choice to represent up to eight
times a `usize` byte count, not as an SSZ requirement. Widening, arithmetic safety,
all error classes and both bounded/unbounded codecs are proved.

Basic `hash_tree_root` operations cover Boolean and all six unsigned widths, for
every typed value. They refine the unchanged `Ssz.hashTreeRoot`, through its actual
layout, packing, bounded merkleization and depth-zero tree rules. The extracted
array-prefix mutation and standard `copy_from_slice` call are proved safe and
preserve every encoded byte, with zero padding to 32 bytes. A uint256 fills the
node exactly. Basic roots do not SHA-256 hash their single leaf. Generic Vector/List roots
are separately proved below. Packed byte/bit and Progressive roots are also proved; other family
root APIs remain unfinished.

Packed roots cover every native byte/Boolean slice, declaration and machine-size/optional capacity.
The real loop preserves all bytes and masks only a borrowed bitlist's delimiter position, then produces
exact zero-padded nodes. Bounded capacities use ceil(bytes/32) or ceil(bits/256). Progressive recursion
uses capacities 1,4,16,... on the right-hand spine, terminating as the remaining chunk count decreases;
all shifts, depth increments, width multiplication, slices and pushes are proved safe. List mixins retain
the actual count, not capacity. The canonical borrowed-view invariant established by its decoder is the
only view precondition, and its full u128 bit count is not narrowed to usize. Input encoding is immutable;
no intermediate encoding copy or Boolean expansion is required, though a node buffer is allocated.

The pinned upstream root deliberately ignores optional Progressive bounds. The three raw Progressive
APIs therefore refine explicit local reference wrappers composing unchanged `Ssz.boundCheck` with
unchanged `checkedHashTreeRoot`. Counterexample lemmas record why direct equality would be false.
This preserves every input/bound, exact fault category and complete root; it does not alter `CodecLaw`,
`codecFaultAgrees` or the pinned executable. Progressive byte roots do not inherit the unrelated <2^32
serialization-envelope restriction.

`hash_pair_refines` proves termination and exact equality with upstream `Ssz.combine`
for every 512-bit input. This covers SSZ's 32-byte-child/32-byte-child hashing path,
not a general-purpose arbitrary-message SHA-256 API. Schedule, all 64 rounds,
both compression blocks, padding and output encoding are connected to the unchanged
upstream SHA-256 implementation. No external hash-function correctness is assumed.
RustCrypto `sha2` 0.10.9 is used only for differential tests.

`merkleize_refines` covers all complete-node slices and every optional `usize`
capacity against `Ssz.merkleizeBounded`. Empty trees, zero capacity, undersized
capacity errors and rounding up `usize::MAX` are covered. Depth uses overflow-free
halving rather than materializing the next power of two. Recursive calls decrease
the count or depth; every shift and slice boundary is proved safe. Zero subtrees
are computed without allocating padding and proved equal to the reference's cache.
These are correctness/termination guarantees, not allocation or runtime cost theorems.

`calculate_merkle_root_refines` and `verify_merkle_proof_refines` connect the actual
Rust APIs to `Ssz.calculateMerkleRoot` and `Ssz.verifyMerkleProof`. All `u128`
indices and representable branch slices are covered. Node widths are enforced by
`[u8; 32]`; their reference width checks are proved successful. Zero, the root
index and incorrect branch lengths return the corresponding error category;
a well-formed nonmatching proof returns false. Proofs cover index guards, sibling
order, recursive termination, SHA-256 composition and bytewise root comparison.
Error relations classify reasons, not the reference error's numeric diagnostics.
Typed paths, multiproofs and full-library conformance are not yet proved.

`gindex` implements raw numeric tree operations, not typed path resolution. Depth and
branch length refine `Ssz.gindexDepth`/`gindexLength`, distinguishing zero, root and
ordinary indices. Bit queries, truncation, sibling and parent preserve the reference's
raw zero/root semantics and zero extension beyond the word width. Child construction,
concatenation and rebasing return the exact reference natural number when representable;
`IndexOverflow` is permitted only when that number exceeds `u128::MAX`, never on a
representable result. Concatenation splices the inner path rather than multiplying indices.
Bottom-up path and sibling lists refine `getPathIndices` and `getBranchIndices`, preserving
all nodes and their order. Their real Vec loops terminate with bounded shifts, increments
and pushes. Positions/depths use `u32`; indices use every `u128` value. The leading-zero
primitive is the pinned Aeneas standard model, with its exact log2 arithmetic proved here.
Native overflow checks and error precedence are part of these proofs. Typed field/element
paths, progressive chunk positions and multiproof helper-set construction remain separate.

`collections::Vector<T, N>` and `collections::List<T, MAX>` own a private `Vec<T>`.
Their generic constructors are proved for every element type and machine-size bound:
vector declarations must be nonzero and match exactly; list lengths must not exceed
the capacity, including zero capacity. Every success contains the original vector;
every failure returns every original element with the exact error kind. Immutable
projections preserve all elements and their order. Returning rejected storage avoids
invoking user element destructors inside a constructor. Zero-sized unit-array fields
retain const bounds in generic extraction without storing runtime bytes; Debug omits
those markers so formatting is not proportional to the declared bound. Rust tests
check allocation identity, no in-constructor element drops, nested non-Copy elements,
formatting and maximum machine counts for zero-sized elements. These are shape/storage
contracts, not element validity, serialization, tree-root or allocation-cost theorems.
Separate compositional proofs now establish their generic `Ssz` implementations. Parent
observations preserve the full ordered sequence of child observations. Fixed and variable
serialization, offset arithmetic, exact decoded values and packed/composite roots refine the
unchanged checked reference operations. No extra well-formedness or bound restrictions are
assumed: zero vector counts, invalid child declarations, empty/zero-capacity lists and
unrepresentable fixed widths follow the reference error precedence. List roots mix in the
actual element count, not capacity. Every byte and node survives packing; capacity arithmetic
is widened and bounded before narrowing. Declaration/layout failures carry empty owned state;
callback failures forward the exact typed completed prefix and exact nested child state.
These ownership equalities are proved separately from the protocol error observation.

`collections::ProgressiveList<T>` has the exact `.progressiveList child none` declaration.
Its constructor and immutable projection preserve every owner, including machine-maximum zero-sized
storage. Its complete dictionary proves the unchanged `CodecLaw` using only its actual child's law:
canonical fixed/variable serialization, exact decode observations and owned partial state, and the
Progressive root over packed basic elements or complete child roots. Roots mix the element count,
not packed-byte length. Declaration failures and overflowing fixed child widths retain existing error
precedence, including successful empty lists. No context bound is silently encoded in this type;
bounded generic Progressive contexts and other Progressive value families remain separate work.

`codec::Ssz` has a static immutable `TYPE` declaration and encode/decode/tree-root
operations. Boolean and uint8/16/32/64/128/256 dictionaries prove that the complete
declaration maps to their exact reference descriptor, in addition to their value-codec
laws. Size and classification are no longer independently overridable constants. The array-to-Vec copy loop
preserves every byte; a decreasing measure proves termination and all indices/increments
are checked safe. Scalar error conversion preserves exact error classes. Dispatcher proofs
are conditional on `CodecLaw`: an external handwritten dictionary is callable but is not
presumed lawful. Only supported, explicitly registered library instances are certified.
The trait's `DecodeState` associated type is inventoried in declarations and every
implementation. Decoding returns `DecodeFailure<DecodeState>`, whose kind is related
to the reference fault. All seven basic dictionaries have unit state; the unit-state
lemma proves error state is empty. A separate function-equality theorem proves that
dispatch forwards the exact result, including arbitrary owned state, not only its
protocol observation. Element-loop ownership is proved separately below; the wire law
alone would not establish it. Error formatting and external implementations are Rust tests,
not protocol proof targets; a non-Debug state/drop-counter test checks that forwarding
and formatting do not invoke its destructor or expose it.

`codec::fixed_size`, `is_basic`, `validate_type` and `is_compatible` derive metadata
from `Ssz::TYPE` without invoking value codecs. The shared implementations refine
`Desc.fixedSize`, `Desc.isBasic`, `Desc.wellFormed` and `Ssz.isCompatible` over every
represented finite declaration. The descriptor represents Boolean, machine-size integer
widths and recursively nested Vector/List/ProgressiveList declarations. All represented
counts, bounds and widths, including zero, unsupported widths and `usize::MAX`, are covered. Validation rejects illegal widths, while width/classification remain separate
metadata exactly as in the reference. Compatibility distinguishes Boolean from uint8
and does not imply declaration validity. The descriptor view preserves the entire
declaration; a negative fixture rejects a bool dictionary mislabeled uint8 despite their
equal byte widths. Declaration variants for the other SSZ families remain to be added.
Vector width arithmetic reports unrepresentable products without changing the natural-number
specification. A zero outer count cancels an overflowing fixed child width; it does not
make a variable child fixed. Zero vector counts fail validation before child faults;
zero list capacities still validate the child. Progressive-list compatibility ignores
capacities but recursively checks the child layout. These are metadata proofs, not
collection value codecs. External declarations must satisfy the declaration law; cyclic
static graphs have no finite descriptor view and are not certified. Static storage and
no metadata-construction allocation are source/compiler properties, not runtime-cost theorems.

`codec::decode_elements` traverses validated body ranges with any explicitly lawful
child dictionary. The actual Vec loop terminates and preserves element order, with
safe indexing, pushes and increments. Its wire result agrees with per-body checked
deserialization; for a well-formed child declaration this is the unchanged upstream
`Ssz.deserializeEach`. A second, exact callback-trace equality retains all actual typed
values in the successful prefix and the failing child's opaque owned state, not only
their protocol observations. Empty views invoke no callbacks; the first child failure
stops traversal. The parent type/layout declaration remains the caller's responsibility.
This lower-level helper does not itself select a Vector/List type; the new parent dictionaries
perform those checks. Non-Copy/drop-counter Rust tests exercise both the traversal and typed
nested parent failures, verifying no element/state destructor runs before returning ownership.

`sequence::offset_spans` refines `Ssz.offsetSpans` for every representable offset
slice and scope, preserving every span and both exact ordering/scope error categories.
Repeated offsets yield empty bodies. Unordered pairs are checked before the final
scope error, matching reference recursion. The loop's prefix/suffix invariant and
decreasing measure prove termination; indexing, increments, subtraction and pushes
are safe even at machine maxima. This numeric helper does not enforce a four-byte
wire envelope, validate the first offset/header, or parse input bytes; those are
separate layout checks, not silently presumed complete here.

`sequence::variable_vector_view` refines `Ssz.vectorSlices` for every variable-width
element descriptor, machine-size count and input slice. It checks the less-than-2^32
composite envelope, fixed-count header budget and exact first offset before numeric
span validation. Its offset-read and range-construction loops terminate and have safe
arithmetic, indexing and pushes. Successful `SequenceView` values retain the original
input and validated immutable ranges; `len`, `is_empty` and `get` preserve every body
and order, including empty bodies and out-of-range queries. Getter safety uses the
range invariant established by decoding and preserved by private, immutable fields.
Zero-copy is source/pointer-test evidence, not a cost theorem. The helper validates
layout, not the containing type declaration or any element value. A zero count follows
the reference's internal helper, not a legal zero-length Vector declaration.

`sequence::variable_list_view` refines `Ssz.listSlices` for variable-width elements
and every optional machine-size capacity. Empty input gives an empty view. Nonempty
input must supply a complete first offset, at least four, aligned to the table width
and within the byte scope. It determines the element count before checking capacity;
capacity errors precede later offset-order errors. The inferred count and all error
precedences match the reference. Bounded and unbounded forms reuse the proved
fixed-count layout validator and its view invariant, without adding a format limit.

`sequence::fixed_vector_view` and `fixed_list_view` refine the fixed-width branches
of the same `Ssz.vectorSlices` and `Ssz.listSlices`, for every representable width,
count, input and optional capacity. Vector byte-budget multiplication is checked;
unrepresentable or mismatched budgets return the reference scope error class.
The range loop terminates and proves every multiplication, increment, push and slice
safe. Empty lists return no bodies even at zero width; nonempty lists reject zero
width and incomplete elements before capacity. Envelope checks precede all these
checks. Zero-width/count internal slicing does not certify a legal type declaration.
Both paths establish the existing immutable view invariant, so typed element traversal
and getters need no new assumptions. Element validity and collection codecs remain separate.

Checks cover Rust tests/doctests/lints, extraction/API/import coverage, proofs and
pinned source integrity. Generated declarations are partitioned into dependency-ordered
modules with qualified names and declaration bodies preserved. Dependency-aware
canonical ordering and inter-declaration whitespace avoid unrelated extraction
order changes invalidating cached proofs. Registry source-location comments use
portable package-relative paths; executable declaration bodies are unchanged.
Aeneas is source-built through the immutable Nix reference in `sources.lock`, using
NyxFoundation's backport of the nested-static-reference repair to the existing pinned
baseline. Charon, Rust, Lean and the Lean standard-library definitions are unchanged.
The repair retains loans for expanded static shared references, consistently erases
runtime lifetime annotations and preserves the type comparison; invariant checks are
now enabled for every SDK extraction. Rust and Lean regressions cover nested static
declarations. Existing 57-operation extraction was byte-identical with the repair.
The second minimal backport visits nested constant operands during effect analysis, including
aggregates, repeats and call arguments. Trait-associated constant reads must not be classified
as pure while their generated bodies use monadic binds. Native regressions and three regenerated
Lean fixtures pass; all committed extraction artifacts for the existing 70-operation baseline are
byte-identical with this fix. Neither patch changes the standard Lean models or proves the compiler correct.
The standalone Nix target avoids rebuilding Charon's unrelated Rust executable and
keeps a GC-rooted output link. Bootstrap requires Nix; source or build failures stop
verification, with no prebuilt/default-extractor fallback. This changes a trusted
translation component, not a proved compiler-correctness theorem.

Extraction requires the pinned Rust toolchain's Miri and rust-src components. It prepares
the standard-library MIR with `cargo +nightly-2026-08-18 miri setup --print-sysroot`
and passes that sysroot explicitly to Charon. Preparation failures stop extraction;
there is no default-sysroot fallback and no executable-body rewriting. Each extraction
uses a fresh Cargo target directory to avoid reusing artifacts from a different sysroot.
Procedural macros discovered in locked Cargo metadata are first compiled with the normal
host sysroot: they execute during compilation and cannot link against Miri's runtime.
Charon then compiles the library dependencies and implementation against the explicit MIR sysroot.
The former Python `usize::div_ceil` body replacement was not machine-checked and has
been removed; its byte-equality check did not establish equivalence to the original output.
`sources.lock` explicitly names transparent foreign items; opaque foreign axioms
are refused rather than treated as library contracts. The complete module inventory
is checked against fresh extraction. Public inherent methods are discovered from
Rustdoc's implementation/type paths, and unknown or ambiguous paths are refused.
Pinned Charon cannot select inherent methods by explicit paths. They use real call
graphs or explicit `verify::start_from` declaration attributes. The `verification`
Cargo feature enables only tool registration and those attributes; it does not select
alternate executable bodies. Normal consumers do not need the feature. Extraction
selects the annotated methods, while exact Rustdoc registration and concrete-body
checks remain mandatory; opaque declarations cannot satisfy coverage. Unregistered public traits fail. For `Ssz`,
Rustdoc declaration/implementation inventories, including associated types, and
concretely extracted dictionaries must match the registry exactly. Lean checks that each theorem establishes the supported
`CodecLaw` for that precise dictionary: either an unconditional concrete law or a universal
constructor law requiring only laws for its exact child dictionaries. Constructor arguments must
be distinct universal type/dictionary/usize parameters, with independent child shapes and observations.
Specialized bounds, extra data domains (including `Fin 0`), assumed parent laws, unrelated theorems,
impossible premises, reflexive/vacuous predicates and another dictionary's proof are refused. Trait declarations and implementations are
partitioned by their Rust source module while preserving native-type Lean namespaces.
Statement adequacy still requires review. Negative fixtures reject custom/native axioms
and unrelated proofs. Only propext, Classical.choice and Quot.sound are allowed.

Pinned Cryspen Aeneas uses Lean 4.31.0; upstream SSZ pins 4.33.1.
The unchanged executable modules and imported codec lemmas build with 4.31.0 here.
Not all upstream proof modules do (`Codec.Admits` exceeds its recursion limit;
`Proofs.Merkle.Tree` has incompatible monadic simplification). Needed tree cache
and evaluation laws are re-proved locally over the unchanged executable definitions.
Unqualified `lake update` changes the toolchain.
Trust includes Lean's kernel, Charon/Aeneas/models, Rust's compiler/runtime and
downloaded tools/caches. Pins do not prove binary integrity; English/formal-model
alignment remains upstream.
Pinned Aeneas `filter_marker_traits` removes `core::marker::Destruct`, even when
Charon receives `--precise-drops`. A runtime counterexample with a panicking destructor
and the generated model confirmed that this does not verify user destructor execution.
The axiom audit cannot detect this semantic erasure. Generic constructors return rejected
storage, and typed decode errors retain partial ownership rather than silently drop
arbitrary elements inside the operation. The element traversal now proves exact retention
of values and nested state, separately from wire conformance. Before backend translation,
`llbc_drops.py` checks successful precise, undesugared LLBC and rejects local normal-flow
Drop statements except closed standard scalar/reference/array/tuple/Vec types and transparent
local non-generic records with recursively safe fields and no user destructor. Real freshly emitted
LLBC fixtures accept closed bookkeeping and node arrays while rejecting an actual user `Drop`.
It resolves interned types, rejects unknown/generic owned types and
explicit `mem::drop`/`mem::forget` calls, and does not rewrite the artifact. Compiler-generated
destructor bodies and unwind cleanup are excluded: caller cleanup, arbitrary foreign
library models and callback internals are not verified by this syntactic check. This
adds a fail-closed regression guard, not a formal destructor-execution/cost theorem.
The official-vector runner pins `ethereum/consensus-spec-tests` independently of the formal model.
Its external cache is checked against the pinned source, an independently pinned SHA-256 inventory
and actual blob contents. The inventory pin was cross-checked against the authoritative upstream Git tree
API, so locally corrupted nested Git objects cannot redefine the expected fixtures;
local modifications, symlinks and extra fixtures are refused. Git replacement objects are ignored
and cache-local hooks/fsmonitor are disabled. Verification avoids filter-capable worktree commands,
checking files directly instead of consulting index cleanliness. Real repository regressions exercise
replacement refs, fsmonitor and clean-filter execution, corrupt nested objects, and modifications hidden
by index flags. Fresh checkout attributes force raw blobs without filters or text/encoding conversions;
this also avoids host Git LFS settings falsely reporting upstream YAML files as modified.
The current explicit CI selection covers all 3,412 Boolean/unsigned/basic-Vector/Bitvector/Bitlist/
ProgressiveBitlist/basic-ProgressiveList source cases, comparing decoded YAML values, re-encoding,
roots and invalid-input rejection under the explicit current-version profile.
The published 2025 corpus uses the pre-fix left-hand Progressive spine. Its source data and old root
metadata remain immutable; 1,020 current root expectations are regenerated, with 730 differences, by
`ethereum/remerkleable` commit 2f0baeef0082d4278acaef7d822deb7009d7db7e. The official source archive's
SHA-256 is pinned and checked before extraction/execution. Fresh extraction rejects path traversal,
links, duplicate entries and oversized sources; an isolated Python process uses only that authenticated
package. Generated expectations identify both revisions, must match each original metadata root and
must all be consumed exactly once; there is no old-root fallback.

The original basic-ProgressiveList data also has 237 contradictory invalid labels (30 empty, 207
nonempty): every affected compressed blob is exactly equal to a published valid blob of the same
primitive type. The version-2 profile records each concrete valid witness, never edits the corpus and
never skips an invalid case. The runner resolves only published same-type witnesses, rechecks their
original root metadata and decompressed byte equality, then requires the supposedly-invalid input to
produce that valid witness's full value, encoding and current root. Missing, repeated, cross-type,
escaping or unconsumed witnesses fail. All other originally-invalid cases still require rejection.
Two corpus families remain unsupported. This is neither a universal proof of the external oracle nor
full corpus coverage.
OS faults/resource exhaustion and whole-library/cryptographic security are excluded.
x86_64 extraction requires the prepared Miri sysroot. Native aarch64 extraction has not been exercised.
