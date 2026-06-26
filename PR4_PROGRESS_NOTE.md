# PR4 progress note

This branch is moving the visible-factor certificate toward a closed Lean checker.

Stable additions so far:

- a pure byte parser core and cursor-based packed-byte parser utilities;
- canonical hex exports for Lean-readable certificate payloads;
- executable parsing of `KMP101`, `KMV101`, and the symmetric closed finish vector payload;
- a first `VerifiedBy`-based metadata certificate for the embedded visible payload;
- an array-based `KMC201` parser and generic CSR residual checker over byte vectors;
- regression examples for the small parsers and the packed sparse-matrix execution path.

The full embedded `Trel_plus.kmc` residual computation is intentionally deferred
from the default Lean library build: it is too heavy for a reviewable CI target
at this stage.  The current checked milestone is therefore:

1. Lean decodes the canonical visible payloads from checked-in hex;
2. Lean parses and checks their binary formats and metadata;
3. Lean contains a generic executable sparse residual checker ready for the
   next certificate-specific instantiation.

Next implementation step: add a small or chunked matrix witness layer that lets
Lean verify the released `Trel_plus` residual without making the ordinary
`lake build` target impractically heavy.
