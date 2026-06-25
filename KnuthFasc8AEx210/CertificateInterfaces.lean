import KnuthFasc8AEx210.PaperTheorem
import KnuthFasc8AEx210.BlockTriangular

open Polynomial

namespace KnuthFasc8AEx210

noncomputable section

/-!
# Interfaces to the checked-in computational certificates

The repository's C++ programs verify large sparse-matrix certificates. These
structures state exactly the mathematical propositions that a future Lean
binary parser/checker must return. No executable boolean is trusted here:
the final theorem consumes propositions.
-/

/-- Certificate that a determinant sector has a simple root at `a`. -/
structure SimpleDeterminantSector {K : Type*} [Field K] (a : K) where
  determinant : K[X]
  simple : SimpleRootAt a determinant

/-- Certificate that a determinant sector is regular at `a`. -/
structure RegularDeterminantSector {K : Type*} [Field K] (a : K) where
  determinant : K[X]
  regular : NonRootAt a determinant

/-- The three diagonal sectors `T`, `U`, and `Wrel`. -/
structure ThreeSectorCertificate {K : Type*} [Field K] (a : K) where
  factor : K[X]
  factor_root : eval a factor = 0
  two_ne_zero : (2 : K) ≠ 0
  left : SimpleDeterminantSector a
  middle : RegularDeterminantSector a
  right : SimpleDeterminantSector a

namespace ThreeSectorCertificate

variable {K : Type*} [Field K] {a : K}

/-- Product of the three diagonal determinant sectors. -/
noncomputable def delta (c : ThreeSectorCertificate a) : K[X] :=
  c.left.determinant * c.middle.determinant * c.right.determinant

/-- Soundness of the compact three-sector interface. -/
theorem factor_cube_not_dvd_delta (c : ThreeSectorCertificate a) :
    ¬c.factor ^ 3 ∣ c.delta := by
  exact not_cube_dvd_of_two_simple_sectors a c.factor_root c.two_ne_zero
    c.left.simple c.middle.regular c.right.simple

end ThreeSectorCertificate

/--
Paper-specific wrapper connecting the three modular determinant sectors to the
integer transfer determinant `Delta`.
-/
structure PaperThreeSectorCapacity (Delta : ℤ[X]) where
  left : F101[X]
  middle : F101[X]
  right : F101[X]
  delta_eq : mod101 Delta = left * middle * right
  left_simple : SimpleRootAt (99 : F101) left
  middle_regular : NonRootAt (99 : F101) middle
  right_simple : SimpleRootAt (99 : F101) right

namespace PaperThreeSectorCapacity

/-- The wrapper discharges the modular-capacity field of `WidthFiveCertificate`. -/
theorem factor_cube_not_dvd {Delta : ℤ[X]} (c : PaperThreeSectorCapacity Delta) :
    ¬paperFactor ^ 3 ∣ mod101 Delta := by
  rw [c.delta_eq]
  exact paperFactor_not_cube_dvd_of_two_simple_sectors
    c.left_simple c.middle_regular c.right_simple

end PaperThreeSectorCapacity

/--
End-to-end theorem using constant-term normalization and the three-sector
certificate.
-/
theorem widthFive_counterexample_of_three_sector_capacity
    {Q QOpen Delta : ℤ[X]}
    (hQ0 : Q.coeff 0 = 1) (hQOpen0 : QOpen.coeff 0 = 1)
    (hOpenDelta : QOpen ∣ Delta)
    (hVisible : paperFactor ∣ mod101 Q)
    (c : PaperThreeSectorCapacity Delta) :
    ¬(Q.map (Int.castRingHom ℚ)) ^ 3 ∣ QOpen.map (Int.castRingHom ℚ) := by
  exact widthFive_counterexample_of_constant_term_one
    hQ0 hQOpen0 hOpenDelta hVisible c.factor_cube_not_dvd

end

end KnuthFasc8AEx210
