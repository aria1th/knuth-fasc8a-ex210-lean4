import KnuthFasc8AEx210.SourceRepository
import KnuthFasc8AEx210.Closed.TrelResidualCertificate
import KnuthFasc8AEx210.Closed.TrelResidualRows

open Polynomial

namespace KnuthFasc8AEx210
namespace Closed
namespace FinalAssembly

noncomputable section

/-!
# Final theorem assembly point

This file deliberately contains no `sorry`.  It records the final theorem shape
and the currently kernel-checked evidence that will feed the remaining source
bridge.

Once the still-missing certificate readers produce a `RemainingSourceBridge`,
the final width-five nondivisibility theorem is obtained immediately.
-/

/-- The nondivisibility statement for the two width-five denominators. -/
def WidthFiveNondivisibility (Q5 Q5Open : ℤ[X]) : Prop :=
  ¬(Q5.map (Int.castRingHom ℚ)) ^ 3 ∣ Q5Open.map (Int.castRingHom ℚ)

/-- Existential form of the width-five counterexample. -/
def WidthFiveCounterexampleStatement : Prop :=
  ∃ Q5 Q5Open : ℤ[X], WidthFiveNondivisibility Q5 Q5Open

/--
The Lean-checked evidence currently available on this PR branch.

The row-block residual evidence is separated from the remaining source bridge
so that later commits can consume it instead of trusting the old C++ output.
-/
structure CurrentVerifiedEvidence : Prop where
  trelResidual : TrelResidualCertificate.Certificate
  trelGlobalRows : TrelResidualRows.GlobalWitnesses
  trelEveryRow : ∀ row, row < 16831 → TrelResidualRows.SomeGlobalWitness row

/-- The current evidence is closed by existing Lean certificates. -/
theorem currentVerifiedEvidence : CurrentVerifiedEvidence where
  trelResidual := TrelResidualCertificate.released
  trelGlobalRows := TrelResidualRows.released
  trelEveryRow := TrelResidualRows.someGlobalWitness_of_lt_16831

/--
The one remaining bridge needed by the algebraic endgame.

This is intentionally a `Type`, not a `Prop`, because
`SourceRepositoryCertificate` contains concrete polynomial data such as the
three modular determinant sectors.
-/
structure RemainingSourceBridge (Q5 Q5Open Delta : ℤ[X]) where
  toSource : CurrentVerifiedEvidence → SourceRepositoryCertificate Q5 Q5Open Delta

/-- The conditional final theorem: once the bridge is filled, the counterexample is closed. -/
theorem widthFiveNondivisibility_of_remainingBridge
    {Q5 Q5Open Delta : ℤ[X]} (bridge : RemainingSourceBridge Q5 Q5Open Delta) :
    WidthFiveNondivisibility Q5 Q5Open := by
  exact SourceRepositoryCertificate.counterexample
    (bridge.toSource currentVerifiedEvidence)

/-- Existential final theorem form from the same remaining bridge. -/
theorem widthFiveCounterexampleStatement_of_remainingBridge
    {Q5 Q5Open Delta : ℤ[X]} (bridge : RemainingSourceBridge Q5 Q5Open Delta) :
    WidthFiveCounterexampleStatement := by
  exact ⟨Q5, Q5Open, widthFiveNondivisibility_of_remainingBridge bridge⟩

end

end FinalAssembly
end Closed
end KnuthFasc8AEx210
