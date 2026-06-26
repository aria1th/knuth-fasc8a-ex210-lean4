# PR4 progress note

This branch is moving the visible-factor certificate toward a closed Lean checker.

Stable additions so far:

- a pure byte parser core and cursor-based packed-byte parser utilities;
- canonical hex exports for Lean-readable certificate payloads;
- executable parsing of `KMP101`, `KMV101`, and the symmetric closed finish vector payload;
- a first `VerifiedBy`-based metadata certificate for the embedded visible payload;
- an array-based `KMC201` parser and generic CSR residual checker over byte vectors;
- row-block `KRC101` residual chunk format, parser, and checker;
- a semantic soundness theorem for each chunk checker: a successful row-block check yields every local row residual equation in that interval;
- a semantic bridge from local row indices to global row witnesses `startRow + localRow`;
- a theorem that every global row `row < 16831` has some released chunk witness;
- a semantic coverage checker proving that the 17 row intervals cover all `16,831` rows contiguously and exactly once;
- generated Lean modules for all 17 released `Trel+` row-block residual certificates;
- `TrelResidualCertificate`, a semantic wrapper combining row-block residuals with exact coverage;
- `FinalAssembly`, the no-`sorry` final theorem assembly point around the remaining source bridge;
- `BridgeBundles`, a bundle-level decomposition of the remaining bridge into denominator, visible-factor, Trel-residual, and capacity bundles;
- `VisibleBundles`, a further split of the visible-factor bundle into a closed parsed-payload bundle and the remaining algebraic visible-factor bridge;
- a heavy root `KnuthFasc8AEx210Heavy` that imports and checks the semantic `Trel+` residual certificate, final assembly, bundle bridge, and split visible-factor bundle separately from the ordinary proof-kernel root.

Current checked milestone:

1. Lean decodes the canonical visible payloads from checked-in hex.
2. Lean parses and checks their binary formats and metadata.
3. Lean parses and checks generated row-block residual certificates for the released `Trel+` eigenvector.
4. Lean proves that the declared row intervals cover the whole `Trel+` block.
5. Lean packages coverage plus the 17 residual chunks as one semantic certificate.
6. Lean can convert a certified local residual row into a global row witness.
7. Lean proves `∀ row < 16831`, some released chunk provides a residual witness for that row.
8. Lean assembles the final counterexample theorem as soon as a `RemainingSourceBridge` converts current checked evidence into `SourceRepositoryCertificate`.
9. Lean decomposes that remaining bridge into reviewable field-level bundles.
10. Lean separates the visible-factor work into `ParsedVisibleBundle` (closed now) and `VisibleAlgebraBridge` (the remaining algebraic claim).
11. CI builds the ordinary proof kernel and the heavy row-block/final-assembly/bundle target.

What this closes: the `Trel+` restricted eigenvector residual `Trel+ v = 50 v` is now represented by Lean-checked row-block certificates rather than only by the C++ verifier output, and the visible payload metadata is separated from the still-missing visible-factor algebraic bridge.

What remains: the visible polynomial construction `r = g(A^2) beta`, the full-block `A^2 r = 76 r` and `A v = 50 v` checks, the rank/Wiedemann certificates, concrete construction of the remaining bundles, and the transfer-generator semantics are still future layers.
