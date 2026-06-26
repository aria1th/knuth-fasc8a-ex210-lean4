# PR4 bundle plan

This branch now treats the remaining closed-counterexample work as a set of
certificate bundles.  The goal is to replace one monolithic
`RemainingSourceBridge` by small, reviewable units that can be filled by
separate Lean checkers.

## Bundle map

| Bundle | Lean structure | Feeds `SourceRepositoryCertificate` fields | Current status |
|---|---|---|---|
| Denominator / transfer bound | `BridgeBundles.DenominatorBundle` | `closed_constant`, `open_constant`, `open_dvd_transferDet` | Interface only |
| Visible closed factor | `BridgeBundles.VisibleFactorBundle` | `visible_factor` | Metadata payload checked; algebraic visible-factor bridge remains |
| Trel residual | `BridgeBundles.TrelResidualBundle` | Evidence used by the future `closed_simple` checker | Lean-checked row-block residuals, coverage, and global-row witnesses |
| Capacity sectors | `BridgeBundles.CapacityBundle` | `closedSector`, `oneEndpointSector`, `completedSector`, `transferDet_mod101`, `closed_simple`, `oneEndpoint_regular`, `completed_simple` | Interface plus checked `Trel+` residual sub-bundle |
| Source bridge | `BridgeBundles.SourceBridgeBundles` | All fields | Converts bundle evidence to `SourceRepositoryCertificate` |
| Final theorem | `FinalAssembly` and `BridgeBundles.SourceBridgeBundles.widthFiveNondivisibility` | Width-five nondivisibility | Assembled, conditional on bundles |

## Current Lean-checked Trel residual chain

```text
KRC101 row-block bytes
  -> parser/checker
  -> ResidualChunk.Spec
  -> GlobalRowWitness
  -> forall row < 16831, SomeGlobalWitness row
  -> TrelResidualBundle
```

This is the first substantial replacement of old C++ verifier output by a
Lean-checked certificate path.

## Next bundle targets

1. **Visible factor algebraic bridge.**  Connect the parsed `KMP101` polynomial,
   restricted eigenvector, and finish vector to `paperFactor ∣ mod101 Q5`.
2. **Full-block residuals.**  Add row-block certificates for `Tall+` checks:
   `A^2 r = 76 r`, `A v = 50 v`, and the polynomial construction
   `r = g(A^2) beta`.
3. **Closed-sector simplicity.**  Use the `TrelResidualBundle` plus border/rank
   certificates to produce `closed_simple`.
4. **Rank/Wiedemann bundle.**  Prove and instantiate the `.kwc2` recurrence
   checkers.
5. **Permutation and endpoint-sector bundle.**  Move `Wrel ≃ Trel` and the `U`
   regularity checks into Lean-checkable payloads.

## Review rule

Each future commit should try to close one bundle field or add a narrowly
scoped checker plus a soundness theorem.  Avoid adding broad assumptions to the
final theorem: assumptions should live only in the not-yet-filled bundle fields.
