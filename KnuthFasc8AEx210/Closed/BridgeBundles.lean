import KnuthFasc8AEx210.Closed.FinalAssembly
import KnuthFasc8AEx210.Closed.VisiblePayload

open Polynomial

namespace KnuthFasc8AEx210
namespace Closed
namespace BridgeBundles

noncomputable section

/-!
# Bundle-level bridge decomposition

`FinalAssembly.RemainingSourceBridge` is the single remaining input needed by
the algebraic counterexample theorem.  This module decomposes that bridge into
reviewable certificate bundles.  Each future checker can target one bundle
without changing the final theorem statement.
-/

/-- Constant-term normalization and the transfer determinant upper bound. -/
structure DenominatorBundle (Q5 Q5Open Delta : ℤ[X]) : Prop where
  closed_constant : Q5.coeff 0 = 1
  open_constant : Q5Open.coeff 0 = 1
  open_dvd_transferDet : Q5Open ∣ Delta

/-- Evidence for the visible factor in the closed denominator. -/
structure VisibleFactorBundle (Q5 : ℤ[X]) : Prop where
  payload : VisiblePayload.Spec VisiblePayload.released
  visible_factor : paperFactor ∣ mod101 Q5

/-- The Lean-checked `Trel+` residual evidence available in this PR. -/
structure TrelResidualBundle : Prop where
  certificate : TrelResidualCertificate.Certificate
  globalRows : TrelResidualRows.GlobalWitnesses
  everyRow : ∀ row, row < 16831 → TrelResidualRows.SomeGlobalWitness row

/-- The current `Trel+` residual bundle is fully checked in Lean. -/
theorem currentTrelResidualBundle : TrelResidualBundle where
  certificate := TrelResidualCertificate.released
  globalRows := TrelResidualRows.released
  everyRow := TrelResidualRows.someGlobalWitness_of_lt_16831

/--
The three-sector modular-capacity bundle.

This bundle contains concrete sector polynomials, so it lives in `Type`.  The
`trelResidual` field records that the closed-sector simplicity proof should
consume the Lean-checked `Trel+` residual evidence rather than re-trusting the
old C++ residual output.
-/
structure CapacityBundle (Delta : ℤ[X]) where
  closedSector : F101[X]
  oneEndpointSector : F101[X]
  completedSector : F101[X]
  transferDet_mod101 :
    mod101 Delta = closedSector * oneEndpointSector * completedSector
  closed_simple : SimpleRootAt (99 : F101) closedSector
  oneEndpoint_regular : NonRootAt (99 : F101) oneEndpointSector
  completed_simple : SimpleRootAt (99 : F101) completedSector
  trelResidual : TrelResidualBundle

/-- All source-bridge bundles needed to construct `SourceRepositoryCertificate`. -/
structure SourceBridgeBundles (Q5 Q5Open Delta : ℤ[X]) where
  denominator : DenominatorBundle Q5 Q5Open Delta
  visible : VisibleFactorBundle Q5
  capacity : CapacityBundle Delta

namespace SourceBridgeBundles

/-- Convert bundle-level evidence into the original source-repository interface. -/
def toSourceRepositoryCertificate {Q5 Q5Open Delta : ℤ[X]}
    (b : SourceBridgeBundles Q5 Q5Open Delta) :
    SourceRepositoryCertificate Q5 Q5Open Delta where
  closed_constant := b.denominator.closed_constant
  open_constant := b.denominator.open_constant
  open_dvd_transferDet := b.denominator.open_dvd_transferDet
  visible_factor := b.visible.visible_factor
  closedSector := b.capacity.closedSector
  oneEndpointSector := b.capacity.oneEndpointSector
  completedSector := b.capacity.completedSector
  transferDet_mod101 := b.capacity.transferDet_mod101
  closed_simple := b.capacity.closed_simple
  oneEndpoint_regular := b.capacity.oneEndpoint_regular
  completed_simple := b.capacity.completed_simple

/-- Bundle evidence gives the remaining bridge used by `FinalAssembly`. -/
def toRemainingSourceBridge {Q5 Q5Open Delta : ℤ[X]}
    (b : SourceBridgeBundles Q5 Q5Open Delta) :
    FinalAssembly.RemainingSourceBridge Q5 Q5Open Delta where
  toSource := fun _ => b.toSourceRepositoryCertificate

/-- Final nondivisibility theorem from bundle-level evidence. -/
theorem widthFiveNondivisibility {Q5 Q5Open Delta : ℤ[X]}
    (b : SourceBridgeBundles Q5 Q5Open Delta) :
    FinalAssembly.WidthFiveNondivisibility Q5 Q5Open := by
  exact FinalAssembly.widthFiveNondivisibility_of_remainingBridge
    b.toRemainingSourceBridge

/-- Existential counterexample theorem from bundle-level evidence. -/
theorem widthFiveCounterexampleStatement {Q5 Q5Open Delta : ℤ[X]}
    (b : SourceBridgeBundles Q5 Q5Open Delta) :
    FinalAssembly.WidthFiveCounterexampleStatement := by
  exact FinalAssembly.widthFiveCounterexampleStatement_of_remainingBridge
    b.toRemainingSourceBridge

end SourceBridgeBundles

end

end BridgeBundles
end Closed
end KnuthFasc8AEx210
