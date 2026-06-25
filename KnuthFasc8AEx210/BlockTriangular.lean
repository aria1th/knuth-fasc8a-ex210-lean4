import Mathlib

open Matrix

namespace KnuthFasc8AEx210

/-!
# Three-block upper-triangular determinant

The transfer matrix is ordered by the nondecreasing degree of the auxiliary
vertex `∞`. Its determinant factorization is a purely block-triangular fact.
-/

section

variable {R : Type*} [CommRing R]
variable {ι κ ν : Type*}
variable [Fintype ι] [Fintype κ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

/-- Determinant of a three-sector upper-triangular block matrix. -/
theorem det_threeBlockUpper
    (A : Matrix ι ι R) (B : Matrix ι (κ ⊕ ν) R)
    (U : Matrix κ κ R) (Y : Matrix κ ν R) (W : Matrix ν ν R) :
    (Matrix.fromBlocks A B 0 (Matrix.fromBlocks U Y 0 W)).det =
      A.det * U.det * W.det := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, mul_assoc]

end

end KnuthFasc8AEx210
