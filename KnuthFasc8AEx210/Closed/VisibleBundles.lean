import KnuthFasc8AEx210.Closed.BridgeBundles
import KnuthFasc8AEx210.Closed.EmbeddedVisible

open Polynomial

namespace KnuthFasc8AEx210
namespace Closed
namespace VisibleBundles

noncomputable section

/-!
# Visible-factor bundle split

`BridgeBundles.VisibleFactorBundle` still contains the actual algebraic claim
`paperFactor ∣ mod101 Q5`.  This file separates the part that is already
closed in Lean -- parsing and checking the visible-factor payloads -- from the
remaining algebraic bridge.
-/

/--
The parsed visible payload metadata currently checked by Lean.

This is deliberately independent of the unknown integer polynomial `Q5`: it is
about the released finite certificate data only.
-/
structure ParsedVisibleBundle : Prop where
  payload : VisiblePayload.Spec VisiblePayload.released
  polynomial_coeff_count : EmbeddedVisible.visible76.coeffs.length = 4107
  eigen_dimension : EmbeddedVisible.eigen50.dimension = 16831
  eigen_packed_size : EmbeddedVisible.eigen50Packed.size = 16831
  finish_dimension : EmbeddedVisible.finish.dimension = 18325
  pivot_index : EmbeddedVisible.eigen50.pivot = 0
  pivot_value : EmbeddedVisible.eigen50.entries.getD EmbeddedVisible.eigen50.pivot 0 = 37
  polynomial_file_size : EmbeddedVisible.visible76ByteArray.size = 4119
  eigen_file_size : EmbeddedVisible.eigen50ByteArray.size = 16847
  finish_file_size : EmbeddedVisible.finishByteArray.size = 18329

/-- The visible-payload metadata bundle is closed by existing Lean checks. -/
theorem currentParsedVisibleBundle : ParsedVisibleBundle where
  payload := VisiblePayload.released_spec
  polynomial_coeff_count := EmbeddedVisible.visible76_coefficient_count
  eigen_dimension := EmbeddedVisible.eigen50_dimension
  eigen_packed_size := EmbeddedVisible.eigen50Packed_size
  finish_dimension := EmbeddedVisible.finish_dimension
  pivot_index := EmbeddedVisible.eigen50_pivot
  pivot_value := EmbeddedVisible.eigen50_pivot_value
  polynomial_file_size := EmbeddedVisible.visible76_file_size
  eigen_file_size := EmbeddedVisible.eigen50_file_size
  finish_file_size := EmbeddedVisible.finish_file_size

/-- If `99` is a root of a modular denominator, then the paper factor divides it. -/
theorem paperFactor_dvd_of_eval_99_eq_zero {p : F101[X]}
    (hroot : eval (99 : F101) p = 0) : paperFactor ∣ p := by
  have hx : X - C (99 : F101) ∣ p := by
    exact Polynomial.dvd_iff_isRoot.mpr (by simpa [Polynomial.IsRoot] using hroot)
  have hfac : paperFactor ∣ X - C (99 : F101) := by
    refine ⟨C (2 : F101), ?_⟩
    norm_num [paperFactor]
  exact hfac.trans hx

/--
The remaining visible-factor bridge.

Future commits should replace the `visible_factor` field by proved checkers for
`r = g(A^2) beta`, `A^2 r = 76 r`, `A v = 50 v`, and the nonzero visibility
functional.
-/
structure VisibleAlgebraBridge (Q5 : ℤ[X]) : Prop where
  parsed : ParsedVisibleBundle
  visible_factor : paperFactor ∣ mod101 Q5

/--
A lower-level visible bridge: it is enough to prove root vanishing at `99`.

The finite certificate checkers should ultimately target this structure before
it is converted to the divisibility form.
-/
structure VisibleRootBridge (Q5 : ℤ[X]) : Prop where
  parsed : ParsedVisibleBundle
  root_at_99 : eval (99 : F101) (mod101 Q5) = 0

/-- Convert root vanishing into the algebraic visible-factor bridge. -/
def VisibleRootBridge.toVisibleAlgebraBridge {Q5 : ℤ[X]}
    (b : VisibleRootBridge Q5) : VisibleAlgebraBridge Q5 where
  parsed := b.parsed
  visible_factor := paperFactor_dvd_of_eval_99_eq_zero b.root_at_99

/-- Convert the split visible bridge to the bundle consumed by final assembly. -/
def VisibleAlgebraBridge.toVisibleFactorBundle {Q5 : ℤ[X]}
    (b : VisibleAlgebraBridge Q5) : BridgeBundles.VisibleFactorBundle Q5 where
  payload := b.parsed.payload
  visible_factor := b.visible_factor

/-- A version of the final theorem using root-vanishing as the visible bridge. -/
theorem widthFiveNondivisibility_of_visibleRootBridge
    {Q5 Q5Open Delta : ℤ[X]}
    (den : BridgeBundles.DenominatorBundle Q5 Q5Open Delta)
    (vis : VisibleRootBridge Q5)
    (cap : BridgeBundles.CapacityBundle Delta) :
    FinalAssembly.WidthFiveNondivisibility Q5 Q5Open := by
  exact BridgeBundles.SourceBridgeBundles.widthFiveNondivisibility
    { denominator := den
      visible := vis.toVisibleAlgebraBridge.toVisibleFactorBundle
      capacity := cap }

/-- A version of the final theorem using the split visible bridge. -/
theorem widthFiveNondivisibility_of_visibleBridge
    {Q5 Q5Open Delta : ℤ[X]}
    (den : BridgeBundles.DenominatorBundle Q5 Q5Open Delta)
    (vis : VisibleAlgebraBridge Q5)
    (cap : BridgeBundles.CapacityBundle Delta) :
    FinalAssembly.WidthFiveNondivisibility Q5 Q5Open := by
  exact BridgeBundles.SourceBridgeBundles.widthFiveNondivisibility
    { denominator := den
      visible := vis.toVisibleFactorBundle
      capacity := cap }

/-- Existential theorem form using the split visible bridge. -/
theorem widthFiveCounterexampleStatement_of_visibleBridge
    {Q5 Q5Open Delta : ℤ[X]}
    (den : BridgeBundles.DenominatorBundle Q5 Q5Open Delta)
    (vis : VisibleAlgebraBridge Q5)
    (cap : BridgeBundles.CapacityBundle Delta) :
    FinalAssembly.WidthFiveCounterexampleStatement := by
  exact BridgeBundles.SourceBridgeBundles.widthFiveCounterexampleStatement
    { denominator := den
      visible := vis.toVisibleFactorBundle
      capacity := cap }

end

end VisibleBundles
end Closed
end KnuthFasc8AEx210
