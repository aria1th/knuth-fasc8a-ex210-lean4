import KnuthFasc8AEx210.AlgebraicCore
import KnuthFasc8AEx210.DerivativeMultiplicity
import KnuthFasc8AEx210.Border

open Polynomial

namespace KnuthFasc8AEx210

/-- Primality evidence exposing the field structure on `ZMod 101`. -/
instance factPrime101 : Fact (Nat.Prime 101) := ⟨by norm_num⟩

noncomputable section

abbrev F101 := ZMod 101

/-- Coefficientwise reduction modulo `101`. -/
def mod101 : ℤ[X] →+* F101[X] :=
  Polynomial.mapRingHom (Int.castRingHom F101)

/-- The factor isolated by the source repository. -/
def paperFactor : F101[X] := 1 - C 50 * X

/-- Its root is `99 = 50⁻¹` in `F₁₀₁`. -/
theorem paperFactor_eval_99 : eval (99 : F101) paperFactor = 0 := by
  have h : (50 : F101) * 99 = 1 := by decide
  simp [paperFactor, h]

/-- A direct second-derivative certificate rules out the cube of `paperFactor`. -/
theorem paperFactor_not_cube_dvd_of_secondDerivative
    {p : F101[X]}
    (hsecond : eval (99 : F101) (derivative (derivative p)) ≠ 0) :
    ¬paperFactor ^ 3 ∣ p := by
  exact not_cube_dvd_of_eval_secondDerivative_ne_zero
    (99 : F101) paperFactor_eval_99 hsecond

/--
At the root `99`, two simple determinant sectors and one regular sector rule
out a cubic factor. This is the short final-layer replacement for an explicit
`ord_f` computation.
-/
theorem paperFactor_not_cube_dvd_of_two_simple_sectors
    {p u w : F101[X]}
    (hp : SimpleRootAt (99 : F101) p)
    (hu : NonRootAt (99 : F101) u)
    (hw : SimpleRootAt (99 : F101) w) :
    ¬paperFactor ^ 3 ∣ p * u * w := by
  apply not_cube_dvd_of_two_simple_sectors (99 : F101) paperFactor_eval_99
  · decide
  · exact hp
  · exact hu
  · exact hw

/--
The five mathematical claims that isolate the large computation from the
small algebraic proof.
-/
structure WidthFiveCertificate (Q QOpen Delta : ℤ[X]) : Prop where
  closed_primitive : Q.IsPrimitive
  open_primitive : QOpen.IsPrimitive
  open_dvd_delta : QOpen ∣ Delta
  visible_mod101 : paperFactor ∣ mod101 Q
  capacity_mod101 : ¬paperFactor ^ 3 ∣ mod101 Delta

/-- The algebraic conclusion of the width-five counterexample over `ℚ[X]`. -/
theorem widthFive_counterexample
    {Q QOpen Delta : ℤ[X]} (cert : WidthFiveCertificate Q QOpen Delta) :
    ¬(Q.map (Int.castRingHom ℚ)) ^ 3 ∣ QOpen.map (Int.castRingHom ℚ) := by
  intro hrat
  have hint : Q ^ 3 ∣ QOpen :=
    int_pow_dvd_of_rat_pow_dvd cert.closed_primitive cert.open_primitive 3 hrat
  exact modular_nondivisibility mod101 cert.visible_mod101 cert.open_dvd_delta
    cert.capacity_mod101 hint

/-- Version using the constant-term-one normalization from `PROOF.md`. -/
theorem widthFive_counterexample_of_constant_term_one
    {Q QOpen Delta : ℤ[X]}
    (hQ0 : Q.coeff 0 = 1) (hQOpen0 : QOpen.coeff 0 = 1)
    (hOpenDelta : QOpen ∣ Delta)
    (hVisible : paperFactor ∣ mod101 Q)
    (hCapacity : ¬paperFactor ^ 3 ∣ mod101 Delta) :
    ¬(Q.map (Int.castRingHom ℚ)) ^ 3 ∣ QOpen.map (Int.castRingHom ℚ) := by
  apply widthFive_counterexample
  exact
    { closed_primitive := intPolynomial_isPrimitive_of_coeff_zero_eq_one hQ0
      open_primitive := intPolynomial_isPrimitive_of_coeff_zero_eq_one hQOpen0
      open_dvd_delta := hOpenDelta
      visible_mod101 := hVisible
      capacity_mod101 := hCapacity }

end

end KnuthFasc8AEx210
