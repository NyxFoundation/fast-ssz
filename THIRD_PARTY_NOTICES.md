# Third-party notices

## ethereum/ssz-specs

Specification source: https://github.com/ethereum/ssz-specs

Pinned revision: `c68b96a852559284cc4311b6c14105bcf51ac6ce`.

The specification is consumed as a pinned Lean dependency. The transitive axiom
allowlist audit in `verification/FastSszVerification/Audit.lean` is adapted from
its `lean/Ssz/Proofs/Audit.lean`.

```text
MIT License

Copyright (c) 2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

Aeneas and its Lean dependencies retain their respective upstream licenses.
They are fetched by Lake/tool bootstrap, not vendored as this project's source.
