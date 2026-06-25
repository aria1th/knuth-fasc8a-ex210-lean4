# Formalization decision

## Verdict

The mathematical endgame of `PROOF.md` is well suited to Lean 4. The full
state generator and the large sparse Wiedemann computations are not suitable
for a line-by-line formalization in the same pull request.

This repository therefore uses a two-layer design:

1. **Lean proof kernel.** All algebraic implications are proved in Lean.
2. **Narrow certificate boundary.** The existing C++ verifiers supply a small
   collection of mathematical propositions to the Lean proof kernel.

This is an intentional scope decision, not a claim that the current pull
request is already a completely kernel-integrated verification of every
binary certificate and every generated transition.

## What is formalization-friendly

The following parts are short, stable, and reusable mathematical statements:

- divisibility transported by a ring homomorphism;
- Gauss's lemma for primitive integer polynomials;
- the reduced-denominator divisibility lemma;
- determinant factorization for an upper-triangular three-block matrix;
- the bordered-matrix kernel/no-generalized-chain argument;
- the final modular contradiction.

These belong in the Lean kernel and are formalized in the modules under
`KnuthFasc8AEx210/`.

## The simpler proof used in Lean

The paper describes the decisive modular multiplicity as `1 + 0 + 1 = 2`.
The final Lean layer does not need to introduce a separate valuation or Jordan
normal-form API.

Let

```text
f(z) = 1 - 50 z  in F_101[z],    a = 99 = 50^{-1}.
```

For the three determinant sectors `D_T`, `D_U`, `D_W`, it is enough to know

```text
D_T(a) = 0,   D_T'(a) != 0,
D_U(a) != 0,
D_W(a) = 0,   D_W'(a) != 0.
```

Then

```text
(D_T D_U D_W)''(a) = 2 D_T'(a) D_U(a) D_W'(a) != 0.
```

Any polynomial divisible by `f^3` has zero second derivative at `a`.
Consequently `f^3` does not divide the transfer determinant. This is the
smallest and most robust Lean proof of the final multiplicity obstruction.

## Why the existing computational strategy should be retained

The denominators have degree in the thousands, while the relevant sparse
matrices have tens of thousands of states. Replacing the local modular
obstruction by explicit denominator computation would make both the
certificate and the formal proof substantially larger.

Finite initial tour counts cannot establish a statement about reduced
rational-function denominators. Likewise, a direct full determinant or full
inverse certificate would be much larger than the existing local eigenvalue
and Wiedemann certificates.

The source repository's strategy is therefore already close to optimal on the
computational side:

- isolate one visible linear factor modulo a small prime;
- prove that it is visible in the closed scalar denominator;
- prove local absence/simplicity in the transfer sectors;
- use one modular divisibility contradiction.

The simplification is made in the **formal proof layer**, not by discarding the
source repository's compact computational certificates.

## What remains outside the Lean kernel

The current C++ programs still establish:

- correctness of the generated frontier-state matrices;
- the `Wrel`/`Trel` permutation similarity;
- the visible eigenvector and reachability/observability calculation;
- the six Wiedemann/Berlekamp--Massey nonsingularity certificates.

`SourceRepositoryCertificate` is the exact proposition-level hand-off for
those results.

A fully end-to-end formalization of the original knight-tour statement must
also verify the semantic link from knight tours to the generated transfer
matrices. Merely parsing the checked-in binary files is not enough for that
stronger claim.

## Recommended follow-up sequence

1. Add a Lean parser and checker for the small visible-factor certificate.
2. Add a proved checker for the fixed finite-field recurrence certificates.
3. Add a proof-producing checker for reflection blocks and permutation
   similarity.
4. In a separate project-sized phase, formalize the frontier-state invariant
   and the correspondence between transfers and Hamiltonian tours.

Keeping these phases separate makes the trust boundary explicit and keeps the
current pull request reviewable.
