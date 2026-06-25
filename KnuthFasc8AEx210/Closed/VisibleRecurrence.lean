import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Reverse

open Polynomial

namespace KnuthFasc8AEx210
namespace Closed
namespace VisibleRecurrence

/-!
# From a visible geometric mode to a denominator factor

The source verifier constructs a nonzero scalar sequence `c * λ^n` inside the
shift-span of the closed transfer sequence.  Every recurrence for the original
sequence therefore holds for this geometric sequence.  This file formalizes
the purely algebraic final step:

* a nonzero scalar multiple of `λ^n` solves a recurrence iff `λ` is a root of
  its characteristic polynomial;
* therefore `X - λ` divides the characteristic polynomial;
* reversing coefficients gives the generating-function denominator factor
  `1 - λ X`.

This removes that implication from the computational trust boundary.
-/

section

variable {K : Type*} [Field K]

/-- A nonzero scalar multiple of a geometric sequence is a solution exactly
when the underlying geometric sequence is a solution. -/
theorem scaled_geom_isSolution_iff (E : LinearRecurrence K) (c λ : K)
    (hc : c ≠ 0) :
    E.IsSolution (fun n => c * λ ^ n) ↔ E.IsSolution (fun n => λ ^ n) := by
  constructor
  · intro hscaled
    have hmem : (fun n => c * λ ^ n) ∈ E.solSpace := hscaled
    have hinv := E.solSpace.smul_mem (c⁻¹) hmem
    simpa [Pi.smul_apply, hc] using hinv
  · intro hgeom
    have hmem : (fun n => λ ^ n) ∈ E.solSpace := hgeom
    have hscaled := E.solSpace.smul_mem c hmem
    simpa [Pi.smul_apply] using hscaled

/-- A visible nonzero geometric mode forces the corresponding root of the
recurrence characteristic polynomial. -/
theorem isRoot_charPoly_of_scaled_geom (E : LinearRecurrence K) (c λ : K)
    (hc : c ≠ 0) (hsol : E.IsSolution (fun n => c * λ ^ n)) :
    E.charPoly.IsRoot λ := by
  exact (E.geom_sol_iff_root_charPoly λ).1
    ((scaled_geom_isSolution_iff E c λ hc).1 hsol)

/-- The characteristic linear factor divides the recurrence polynomial. -/
theorem X_sub_C_dvd_charPoly_of_scaled_geom (E : LinearRecurrence K) (c λ : K)
    (hc : c ≠ 0) (hsol : E.IsSolution (fun n => c * λ ^ n)) :
    X - C λ ∣ E.charPoly := by
  exact Polynomial.dvd_iff_isRoot.mpr
    (isRoot_charPoly_of_scaled_geom E c λ hc hsol)

/-- Reversing `X - λ` gives the denominator factor `1 - λ X`. -/
theorem reverse_X_sub_C (λ : K) :
    (X - C λ : K[X]).reverse = 1 - C λ * X := by
  rw [sub_eq_add_neg, ← C_neg, Polynomial.reverse_add_C]
  simp [Polynomial.reverse, sub_eq_add_neg]

/--
A visible nonzero geometric solution forces `1 - λX` to divide the reversed
characteristic polynomial, i.e. the standard generating-function denominator
attached to the recurrence.
-/
theorem denominatorFactor_dvd_of_scaled_geom (E : LinearRecurrence K) (c λ : K)
    (hc : c ≠ 0) (hsol : E.IsSolution (fun n => c * λ ^ n)) :
    1 - C λ * X ∣ E.charPoly.reverse := by
  rcases X_sub_C_dvd_charPoly_of_scaled_geom E c λ hc hsol with ⟨r, hr⟩
  refine ⟨r.reverse, ?_⟩
  rw [hr, Polynomial.reverse_mul_of_domain, reverse_X_sub_C]

end

end VisibleRecurrence
end Closed
end KnuthFasc8AEx210
