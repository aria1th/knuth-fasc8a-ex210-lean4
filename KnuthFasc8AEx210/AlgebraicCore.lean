import Mathlib

open Polynomial

namespace KnuthFasc8AEx210

/-!
# Algebraic core of the width-five counterexample

The final contradiction uses only divisibility, reduction modulo a prime, and
Gauss's lemma. It is independent of the transfer-matrix construction and of
the concrete certificate verifier.
-/

section Divisibility

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- A ring homomorphism transports divisibility. -/
theorem map_dvd_of_dvd (φ : R →+* S) {a b : R} (h : a ∣ b) : φ a ∣ φ b := by
  rcases h with ⟨c, rfl⟩
  exact ⟨φ c, by simp⟩

/-- Divisibility is preserved by taking equal powers. -/
theorem pow_dvd_pow_of_dvd {a b : R} (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n := by
  rcases h with ⟨c, rfl⟩
  exact ⟨c ^ n, by simp [mul_pow]⟩

/--
The general modular obstruction.

If `f^a` divides the image of the closed denominator, a conjectured `r`-th
power divisibility forces `f^(a*r)` to divide the image of every common upper
bound for the open denominator.
-/
theorem modular_power_obstruction
    (φ : R →+* S) {q qOpen delta : R} {f : S} {a r : ℕ}
    (hvisible : f ^ a ∣ φ q)
    (hconjecture : q ^ r ∣ qOpen)
    (hbound : qOpen ∣ delta)
    (hcapacity : ¬f ^ (a * r) ∣ φ delta) : False := by
  apply hcapacity
  have h₁ : f ^ (a * r) ∣ (φ q) ^ r := by
    simpa [pow_mul] using pow_dvd_pow_of_dvd hvisible r
  have h₂ : (φ q) ^ r ∣ φ qOpen := by
    simpa using map_dvd_of_dvd φ hconjecture
  have h₃ : φ qOpen ∣ φ delta := map_dvd_of_dvd φ hbound
  exact h₁.trans (h₂.trans h₃)

/-- The exponent-one specialization used for the factor `1 - 50z`. -/
theorem modular_obstruction
    (φ : R →+* S) {q qOpen delta : R} {f : S} {r : ℕ}
    (hvisible : f ∣ φ q)
    (hconjecture : q ^ r ∣ qOpen)
    (hbound : qOpen ∣ delta)
    (hcapacity : ¬f ^ r ∣ φ delta) : False := by
  exact modular_power_obstruction φ (a := 1) (r := r)
    (by simpa using hvisible) hconjecture hbound (by simpa using hcapacity)

/-- The modular obstruction packaged directly as a nondivisibility theorem. -/
theorem modular_nondivisibility
    (φ : R →+* S) {q qOpen delta : R} {f : S} {r : ℕ}
    (hvisible : f ∣ φ q)
    (hbound : qOpen ∣ delta)
    (hcapacity : ¬f ^ r ∣ φ delta) : ¬q ^ r ∣ qOpen := by
  intro hconjecture
  exact modular_obstruction φ hvisible hconjecture hbound hcapacity

/-- Reusable data sufficient to refute a proposed power divisibility. -/
structure ModularCounterexampleCertificate
    (φ : R →+* S) (q qOpen delta : R) (f : S) (r : ℕ) : Prop where
  visible : f ∣ φ q
  upperBound : qOpen ∣ delta
  capacity : ¬f ^ r ∣ φ delta

/-- Soundness of `ModularCounterexampleCertificate`. -/
theorem ModularCounterexampleCertificate.sound
    (φ : R →+* S) {q qOpen delta : R} {f : S} {r : ℕ}
    (c : ModularCounterexampleCertificate φ q qOpen delta f r) :
    ¬q ^ r ∣ qOpen :=
  modular_nondivisibility φ c.visible c.upperBound c.capacity

end Divisibility

section ReducedDenominator

variable {R : Type*} [CommSemiring R]

/--
If `P/Q = A/E` after cross multiplication and `P,Q` are coprime, then the
reduced denominator `Q` divides the exhibited denominator `E`.
-/
theorem reduced_denominator_dvd_of_cross_mul
    {P Q A E : R[X]} (hcoprime : IsCoprime P Q)
    (hcross : P * E = A * Q) : Q ∣ E := by
  have hQE : Q ∣ P * E := by
    refine ⟨A, ?_⟩
    simpa [mul_comm] using hcross
  exact hcoprime.symm.dvd_of_dvd_mul_left hQE

end ReducedDenominator

section GaussBridge

/-- Constant coefficient `1` makes an integer polynomial primitive. -/
theorem intPolynomial_isPrimitive_of_coeff_zero_eq_one
    {p : ℤ[X]} (h0 : p.coeff 0 = 1) : p.IsPrimitive := by
  intro r hr
  have hdiv : r ∣ p.coeff 0 := ((C_dvd_iff_dvd_coeff).mp hr) 0
  rw [h0] at hdiv
  exact isUnit_of_dvd_one hdiv

/-- Powers of a primitive integer polynomial are primitive. -/
theorem intPolynomial_isPrimitive_pow {p : ℤ[X]}
    (hp : p.IsPrimitive) : ∀ n : ℕ, (p ^ n).IsPrimitive
  | 0 => by simpa using (Polynomial.isPrimitive_one : (1 : ℤ[X]).IsPrimitive)
  | n + 1 => by
      simpa [pow_succ] using (intPolynomial_isPrimitive_pow hp n).mul hp

/-- Gauss's lemma: divisibility over `ℚ[X]` descends to primitive polynomials in `ℤ[X]`. -/
theorem int_dvd_of_rat_dvd_of_primitive
    {p q : ℤ[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive)
    (h : p.map (Int.castRingHom ℚ) ∣ q.map (Int.castRingHom ℚ)) : p ∣ q := by
  exact (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast p q hp hq).2 h

/-- Power form of the Gauss-lemma bridge. -/
theorem int_pow_dvd_of_rat_pow_dvd
    {p q : ℤ[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) (n : ℕ)
    (h : (p.map (Int.castRingHom ℚ)) ^ n ∣ q.map (Int.castRingHom ℚ)) :
    p ^ n ∣ q := by
  apply int_dvd_of_rat_dvd_of_primitive (intPolynomial_isPrimitive_pow hp n) hq
  simpa using h

end GaussBridge

end KnuthFasc8AEx210
