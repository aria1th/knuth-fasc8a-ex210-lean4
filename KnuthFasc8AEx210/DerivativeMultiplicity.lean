import Mathlib

open Polynomial

namespace KnuthFasc8AEx210

/-!
# A derivative criterion for the multiplicity-two capacity bound

For exponent three, nonvanishing of the second formal derivative at a root
rules out cubic divisibility.
-/

section DerivativeIdentities

variable {K : Type*} [CommRing K]

/-- Product rule for the second formal derivative, evaluated at a point. -/
theorem eval_secondDerivative_mul (a : K) (p q : K[X]) :
    eval a (derivative (derivative (p * q))) =
      eval a (derivative (derivative p)) * eval a q
        + (2 : K) * eval a (derivative p) * eval a (derivative q)
        + eval a p * eval a (derivative (derivative q)) := by
  rw [derivative_mul, derivative_add, derivative_mul, derivative_mul]
  simp only [eval_add, eval_mul]
  ring

/-- A cube of a polynomial vanishing at `a` has vanishing second derivative at `a`. -/
theorem eval_secondDerivative_eq_zero_of_cube_dvd
    (a : K) {f p : K[X]} (hf : eval a f = 0) (hdiv : f ^ 3 ∣ p) :
    eval a (derivative (derivative p)) = 0 := by
  rcases hdiv with ⟨q, rfl⟩
  have hpow3 : f ^ 3 = f ^ 2 * f := by
    rw [pow_succ]
  have hf2 : eval a (f ^ 2) = 0 := by
    simp [hf]
  have hdf2 : eval a (derivative (f ^ 2)) = 0 := by
    simp [pow_two, derivative_mul, hf]
  have h0 : eval a (f ^ 3) = 0 := by
    simp [hf]
  have h1 : eval a (derivative (f ^ 3)) = 0 := by
    rw [hpow3, derivative_mul]
    simp [hf, hf2, hdf2]
  have h2 : eval a (derivative (derivative (f ^ 3))) = 0 := by
    rw [hpow3, eval_secondDerivative_mul]
    simp [hf, hf2, hdf2]
  rw [eval_secondDerivative_mul]
  simp [h0, h1, h2]

/-- Nonvanishing of the second derivative rules out cubic divisibility. -/
theorem not_cube_dvd_of_eval_secondDerivative_ne_zero
    (a : K) {f p : K[X]} (hf : eval a f = 0)
    (hsecond : eval a (derivative (derivative p)) ≠ 0) :
    ¬f ^ 3 ∣ p := by
  intro hdiv
  exact hsecond (eval_secondDerivative_eq_zero_of_cube_dvd a hf hdiv)

end DerivativeIdentities

section TwoSimpleSectors

variable {K : Type*} [Field K]

/-- `p` has a simple root at `a`. -/
structure SimpleRootAt (a : K) (p : K[X]) : Prop where
  eval_eq_zero : eval a p = 0
  derivative_ne_zero : eval a (derivative p) ≠ 0

/-- `p` does not vanish at `a`. -/
structure NonRootAt (a : K) (p : K[X]) : Prop where
  eval_ne_zero : eval a p ≠ 0

/-- Two simple sectors and one regular sector give a nonzero second derivative. -/
theorem secondDerivative_ne_zero_of_two_simple_sectors
    (a : K) {p u w : K[X]} (h2 : (2 : K) ≠ 0)
    (hp : SimpleRootAt a p) (hu : NonRootAt a u)
    (hw : SimpleRootAt a w) :
    eval a (derivative (derivative (p * u * w))) ≠ 0 := by
  have hformula :
      eval a (derivative (derivative (p * u * w))) =
        (2 : K) * eval a (derivative p) * eval a u * eval a (derivative w) := by
    calc
      eval a (derivative (derivative (p * u * w))) =
          eval a (derivative (derivative (p * u))) * eval a w
            + (2 : K) * eval a (derivative (p * u)) * eval a (derivative w)
            + eval a (p * u) * eval a (derivative (derivative w)) :=
        eval_secondDerivative_mul a (p * u) w
      _ = (2 : K) * eval a (derivative p) * eval a u * eval a (derivative w) := by
        simp [derivative_mul, hp.eval_eq_zero, hw.eval_eq_zero]
        ring
  rw [hformula]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero h2 hp.derivative_ne_zero) hu.eval_ne_zero)
    hw.derivative_ne_zero

/-- The factor cannot divide the three-sector product to exponent three. -/
theorem not_cube_dvd_of_two_simple_sectors
    (a : K) {f p u w : K[X]} (hf : eval a f = 0) (h2 : (2 : K) ≠ 0)
    (hp : SimpleRootAt a p) (hu : NonRootAt a u)
    (hw : SimpleRootAt a w) :
    ¬f ^ 3 ∣ p * u * w := by
  apply not_cube_dvd_of_eval_secondDerivative_ne_zero a hf
  exact secondDerivative_ne_zero_of_two_simple_sectors a h2 hp hu hw

end TwoSimpleSectors

end KnuthFasc8AEx210
