# PR3 target: closed Lean counterexample

## Goal

The target is an unconditional Lean 4 refutation of Knuth's Exercise 210 at
width `m = 5`: no free proposition such as `SourceRepositoryCertificate` should
remain in the final theorem.

The current repository already proves

```lean
theorem SourceRepositoryCertificate.counterexample
    {Q5 Q5Open Delta : ℤ[X]}
    (c : SourceRepositoryCertificate Q5 Q5Open Delta) :
    ¬(Q5.map (Int.castRingHom ℚ)) ^ 3 ∣
      Q5Open.map (Int.castRingHom ℚ)
```

PR3 must replace the argument `c` by data and proofs checked inside Lean.

## Two closure layers

There are two different meanings of "closed" here.

### Layer A: closed from the checked-in finite certificates

Lean parses or generates the finite certificate data and proves that its
Boolean checker implies `SourceRepositoryCertificate`. This removes the current
proposition interface.

This layer should verify, inside Lean:

1. the visible-factor payload `visible76.poly` and `Trel_plus_eigen50.vec`;
2. sparse `.kmc` matrix metadata needed by the certificate checkers;
3. the `.kwc2` Wiedemann/Berlekamp--Massey rank certificates;
4. the `Wrel`/`Trel` permutation-similarity and singleton exclusion claims;
5. the constant-term normalization and transfer determinant divisibility claims
   as concrete data-derived propositions.

The initial code in `KnuthFasc8AEx210/Closed/` introduces the Boolean-certificate
wrapper and the exact theorem shape:

```lean
theorem Closed.counterexample_of_verified_source_certificate
    {Payload : Type u} {Q5 Q5Open Delta : ℤ[X]}
    (v : VerifiedBy Payload (fun _ => SourceRepositoryCertificate Q5 Q5Open Delta)) :
    ¬(Q5.map (Int.castRingHom ℚ)) ^ 3 ∣
      Q5Open.map (Int.castRingHom ℚ)
```

Once `v` is constructed from concrete data, the width-five algebraic
counterexample is closed.

### Layer B: closed from the original knight graph

A stronger target starts from a formal definition of knight moves on an
`m x n` board and proves that the generated frontier-state transfer counts
exactly the closed and open Hamiltonian tours. This requires a full formal
frontier invariant, terminal-state invariant, and proof that the generator's
byte output corresponds to those definitions.

Layer B should be a follow-up once Layer A is in place. Without Layer B, the
proof is closed relative to checked-in finite certificates, not directly from
Knuth's combinatorial definition.

## Current PR3 scope

This PR begins Layer A. It does not yet claim to have parsed all large binary
certificates in Lean. It establishes the Lean-side closure pattern so that
future commits can replace each current `SourceRepositoryCertificate` field by
an executable checker plus a soundness theorem.

## Suggested implementation order

1. **Small binary parsing.** Add byte-level parsers for fixed little-endian
   `UInt32`, vectors over `ZMod 101`, and sparse CSR headers.
2. **Visible factor first.** Verify the small polynomial/eigenvector payload and
   prove the `visible_factor` field of `SourceRepositoryCertificate`.
3. **Finite-field extension.** Define the quadratic extension
   `F_101[t]/(t^2 - 2)` or an isomorphic pair representation, with proved field
   operations.
4. **Berlekamp--Massey soundness.** Prove that a recomputed scalar recurrence of
   degree `N` with nonzero constant coefficient certifies nonsingularity of the
   corresponding matrix.
5. **Sparse matrix checker.** Prove that the CSR multiplication used by the
   checker represents the intended matrix-vector product over the finite field.
6. **Rank certificates.** Instantiate the six `.kwc2` checks.
7. **Permutation and singleton checks.** Move `Wrel ≃ Trel` and diagonal
   singleton exclusion from C++ to Lean.
8. **Concrete closed theorem.** Replace the abstract `VerifiedBy` parameter by a
   concrete payload and `by native_decide` or another kernel-accepted computation.

## Non-goals for this first PR3 slice

- No use of `sorry`, `admit`, or local `axiom`.
- No claim that the original combinatorial semantics are already formalized.
- No trusted extraction of propositions from C++ output in the final target.
