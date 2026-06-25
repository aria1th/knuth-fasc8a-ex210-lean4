import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.RingTheory.Polynomial.GaussLemma

open Polynomial

namespace KnuthFasc8AEx210

/-!
# Knuth's original knight-tour denominator question

This file fixes the statement that the end-to-end formalization must refute.
Tours are counted as spanning edge sets, not as based or oriented walks. Thus a
cycle or path is counted exactly once, matching the graph-theoretic convention
in Exercise 210.
-/

/-- The vertices of an `m × n` board. -/
abbrev KnightBoard (m n : ℕ) := Fin m × Fin n

/-- Two board squares differ by a knight move. -/
def KnightAdjacent {m n : ℕ} (u v : KnightBoard m n) : Prop :=
  (Nat.dist u.1.1 v.1.1 = 1 ∧ Nat.dist u.2.1 v.2.1 = 2) ∨
  (Nat.dist u.1.1 v.1.1 = 2 ∧ Nat.dist u.2.1 v.2.1 = 1)

instance {m n : ℕ} : DecidableRel (@KnightAdjacent m n) := fun _ _ => inferInstance

/-- The simple graph of knight moves on an `m × n` board. -/
def knightGraph (m n : ℕ) : SimpleGraph (KnightBoard m n) where
  Adj := KnightAdjacent
  symm := by
    intro u v h
    simpa [KnightAdjacent, Nat.dist_comm] using h
  loopless := by
    intro u
    simp [KnightAdjacent]

@[simp]
theorem knightGraph_adj {m n : ℕ} (u v : KnightBoard m n) :
    (knightGraph m n).Adj u v ↔ KnightAdjacent u v := Iff.rfl

/-- The degree of a vertex, stated without introducing a decidable adjacency relation. -/
noncomputable def graphDegree {V : Type*} [Finite V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  Nat.card {w : V // G.Adj v w}

/-- A spanning subgraph that is one Hamiltonian cycle. -/
def IsClosedTour {V : Type*} [Finite V]
    (G H : SimpleGraph V) : Prop :=
  H ≤ G ∧ H.Connected ∧ ∀ v, graphDegree H v = 2

/-- A spanning subgraph that is one Hamiltonian path. -/
def IsOpenTour {V : Type*} [Finite V]
    (G H : SimpleGraph V) : Prop :=
  H ≤ G ∧ H.Connected ∧
    ∃ a b, a ≠ b ∧
      graphDegree H a = 1 ∧ graphDegree H b = 1 ∧
      ∀ v, v ≠ a → v ≠ b → graphDegree H v = 2

/-- Number of Hamiltonian cycles in a finite simple graph, counted as edge sets. -/
noncomputable def closedTourCountOf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact Fintype.card {H : SimpleGraph V // IsClosedTour G H}

/-- Number of Hamiltonian paths in a finite simple graph, counted as edge sets. -/
noncomputable def openTourCountOf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact Fintype.card {H : SimpleGraph V // IsOpenTour G H}

/-- `S_{m,n}` from Exercise 210. -/
noncomputable def closedKnightTourCount (m n : ℕ) : ℕ :=
  closedTourCountOf (knightGraph m n)

/-- `S⁺_{m,n}` from Exercise 210. -/
noncomputable def openKnightTourCount (m n : ℕ) : ℕ :=
  openTourCountOf (knightGraph m n)

/-- Coefficient of `z^n` in `Q(z) * ∑ a_k z^k`. -/
def convolutionCoeff (Q : ℚ[X]) (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), Q.coeff i * a (n - i)

/-- A polynomial quotient `P/Q` represents the ordinary generating function of `a`. -/
def IsGeneratingFunctionPresentation (a : ℕ → ℚ) (P Q : ℚ[X]) : Prop :=
  ∀ n, convolutionCoeff Q a n = P.coeff n

/--
A normalized reduced integer denominator for an integer sequence.

The equality is interpreted over `ℚ`; the integer numerator and denominator
are required to be coprime and the denominator has constant coefficient one.
-/
def IsNormalizedReducedDenominator (a : ℕ → ℕ) (Q : ℤ[X]) : Prop :=
  Q.coeff 0 = 1 ∧ Q.IsPrimitive ∧
    ∃ P : ℤ[X], IsCoprime P Q ∧
      IsGeneratingFunctionPresentation
        (fun n => (a n : ℚ))
        (P.map (Int.castRingHom ℚ))
        (Q.map (Int.castRingHom ℚ))

/-- The universal assertion posed in Exercise 210. -/
def KnuthExercise210 : Prop :=
  ∀ m : ℕ, 5 ≤ m →
    ∀ Q QOpen : ℤ[X],
      IsNormalizedReducedDenominator (closedKnightTourCount m) Q →
      IsNormalizedReducedDenominator (openKnightTourCount m) QOpen →
      (Q.map (Int.castRingHom ℚ)) ^ 3 ∣ QOpen.map (Int.castRingHom ℚ)

/-- A concrete width-five pair of reduced denominators refutes the universal assertion. -/
theorem not_knuthExercise210_of_widthFive
    {Q QOpen : ℤ[X]}
    (hQ : IsNormalizedReducedDenominator (closedKnightTourCount 5) Q)
    (hQOpen : IsNormalizedReducedDenominator (openKnightTourCount 5) QOpen)
    (hnot : ¬(Q.map (Int.castRingHom ℚ)) ^ 3 ∣
      QOpen.map (Int.castRingHom ℚ)) :
    ¬KnuthExercise210 := by
  intro h
  exact hnot (h 5 (by omega) Q QOpen hQ hQOpen)

end KnuthFasc8AEx210
