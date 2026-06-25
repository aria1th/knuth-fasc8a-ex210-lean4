# Lean 4 formalization

This Lean project formalizes the algebraic proof kernel behind
[`PROOF.md`](PROOF.md). It targets Lean 4.31.0 and mathlib `v4.31.0`.

The scope decision and the reason for using the shorter second-derivative
argument are recorded in [`FORMALIZATION_DECISION.md`](FORMALIZATION_DECISION.md).

## Main theorem

`KnuthFasc8AEx210.SourceRepositoryCertificate.counterexample` states that the
width-five closed denominator cubed does not divide the width-five open
denominator over `ℚ[X]`, assuming the mathematical propositions exported by
the checked-in sparse-matrix certificates.

```lean
theorem SourceRepositoryCertificate.counterexample
    {Q5 Q5Open Delta : ℤ[X]}
    (c : SourceRepositoryCertificate Q5 Q5Open Delta) :
    ¬(Q5.map (Int.castRingHom ℚ)) ^ 3 ∣ Q5Open.map (Int.castRingHom ℚ)
```

The final contradiction has four steps:

1. Gauss's lemma moves a hypothetical divisibility in `ℚ[X]` to `ℤ[X]`.
2. Reduction modulo `101` transports divisibility.
3. The visible factor `1 - 50z` would therefore occur at least three times in
   the open transfer determinant.
4. At its root `99`, the two closed sectors are simple and the endpoint sector
   is regular, so the determinant's second derivative is nonzero. Hence the
   factor cannot occur three times.

## Modules

- `AlgebraicCore.lean`: modular obstruction, reduced denominators, and Gauss's lemma.
- `DerivativeMultiplicity.lean`: the second-derivative cube obstruction.
- `Border.lean`: generalized border lemma used to prove algebraic simplicity.
- `BlockTriangular.lean`: determinant factorization for three upper-triangular sectors.
- `PaperTheorem.lean`: the factor `1 - 50z` over `F₁₀₁` and the final theorem.
- `CertificateInterfaces.lean`: proposition-level interface for matrix certificates.
- `SourceRepository.lean`: exact mapping from this repository's certificate files to the interface.

## Build

```sh
lake update
lake build
```

CI runs the same build and rejects `sorry` and `admit` in Lean sources.

## Trust boundary and next implementation step

The algebraic proof is kernel checked. The existing C++ programs still parse
and verify the large binary matrix, eigenvector, and Wiedemann/Berlekamp--Massey
certificates. Lean currently consumes their mathematical conclusions through
`SourceRepositoryCertificate`; it does not yet parse `.kmc`, `.vec`, `.poly`,
or `.kwc2` files itself.

The next phase is a Lean certificate reader with proved soundness for:

- `data/certs/visible76.poly` and `Trel_plus_eigen50.vec`;
- the six rank certificates listed by `make rank-check`;
- the `Wrel`/`Trel` permutation-similarity certificate produced by
  `src/extract_blocks.cpp`.

A completely kernel-integrated proof of the original combinatorial statement
would additionally need a formal proof that the generated frontier-state
transfers enumerate exactly the relevant Hamiltonian tours.

Until that phase is complete, this repository contains a fully checked proof
kernel and an explicit, narrow computational interface rather than a wholly
kernel-integrated verification of the large data files.
