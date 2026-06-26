import Mathlib
import KnuthFasc8AEx210.Closed.BooleanCertificate

namespace KnuthFasc8AEx210
namespace Closed
namespace ResidualCoverage

/-!
# Coverage of contiguous residual row blocks

The released `Trel+` residual is split into 1,024-row certificates. This module
checks the inexpensive global invariant: the declared intervals are nonempty,
ordered, contiguous, and cover every row exactly once.
-/

structure RowRange where
  startRow : Nat
  rowCount : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Check a list of ranges beginning at `nextRow` and ending at `dimension`. -/
def coversFrom : Nat → Nat → List RowRange → Bool
  | dimension, nextRow, [] => nextRow == dimension
  | dimension, nextRow, range :: ranges =>
      (range.startRow == nextRow) &&
      (0 < range.rowCount) &&
      (range.startRow + range.rowCount ≤ dimension) &&
      coversFrom dimension (range.startRow + range.rowCount) ranges

/-- Check exact coverage of rows `0, ..., dimension - 1`. -/
def covers (dimension : Nat) (ranges : List RowRange) : Bool :=
  coversFrom dimension 0 ranges

/-- Semantic version of `coversFrom`. -/
def CoversFromSpec : Nat → Nat → List RowRange → Prop
  | dimension, nextRow, [] => nextRow = dimension
  | dimension, nextRow, range :: ranges =>
      range.startRow = nextRow ∧
      0 < range.rowCount ∧
      range.startRow + range.rowCount ≤ dimension ∧
      CoversFromSpec dimension (range.startRow + range.rowCount) ranges

/-- Semantic exact coverage of rows `0, ..., dimension - 1`. -/
def CoversSpec (dimension : Nat) (ranges : List RowRange) : Prop :=
  CoversFromSpec dimension 0 ranges

/-- Soundness of the executable coverage checker. -/
theorem coversFrom_sound (dimension nextRow : Nat) (ranges : List RowRange)
    (h : coversFrom dimension nextRow ranges = true) :
    CoversFromSpec dimension nextRow ranges := by
  induction ranges generalizing nextRow with
  | nil =>
      simpa [coversFrom, CoversFromSpec] using h
  | cons range ranges ih =>
      have parts :
          range.startRow = nextRow ∧
          0 < range.rowCount ∧
          range.startRow + range.rowCount ≤ dimension ∧
          coversFrom dimension (range.startRow + range.rowCount) ranges = true := by
        simpa [coversFrom, Bool.and_eq_true] using h
      exact ⟨parts.1, parts.2.1, parts.2.2.1,
        ih (range.startRow + range.rowCount) parts.2.2.2⟩

/-- Soundness of the exact-coverage checker. -/
theorem covers_sound (dimension : Nat) (ranges : List RowRange)
    (h : covers dimension ranges = true) : CoversSpec dimension ranges :=
  coversFrom_sound dimension 0 ranges h

/-- Row intervals emitted by the deterministic `Trel+` chunk exporter. -/
def trelRanges : List RowRange :=
  [ ⟨0, 1024⟩,
    ⟨1024, 1024⟩,
    ⟨2048, 1024⟩,
    ⟨3072, 1024⟩,
    ⟨4096, 1024⟩,
    ⟨5120, 1024⟩,
    ⟨6144, 1024⟩,
    ⟨7168, 1024⟩,
    ⟨8192, 1024⟩,
    ⟨9216, 1024⟩,
    ⟨10240, 1024⟩,
    ⟨11264, 1024⟩,
    ⟨12288, 1024⟩,
    ⟨13312, 1024⟩,
    ⟨14336, 1024⟩,
    ⟨15360, 1024⟩,
    ⟨16384, 447⟩ ]

/-- Executable check for the exact released row-block plan. -/
def trelCoverageCheck (ranges : List RowRange) : Bool :=
  covers 16831 ranges && (ranges.length == 17)

/-- Semantic specification of the exact released row-block plan. -/
def TrelCoverageSpec (ranges : List RowRange) : Prop :=
  CoversSpec 16831 ranges ∧ ranges.length = 17

/-- Soundness of the released coverage checker. -/
theorem trelCoverageCheck_sound (ranges : List RowRange)
    (h : trelCoverageCheck ranges = true) : TrelCoverageSpec ranges := by
  have parts : covers 16831 ranges = true ∧ ranges.length = 17 := by
    simpa [trelCoverageCheck, Bool.and_eq_true] using h
  exact ⟨covers_sound 16831 ranges parts.1, parts.2⟩

/-- The generated row intervals cover all `16831` rows exactly once. -/
theorem trelRanges_cover : covers 16831 trelRanges = true := by
  native_decide

/-- The number of expected independently checked row blocks. -/
theorem trelRanges_length : trelRanges.length = 17 := by
  native_decide

/-- Boolean form of the released row-block coverage check. -/
theorem trelCoverageCheck_ok : trelCoverageCheck trelRanges = true := by
  native_decide

/-- Verified certificate for the released row-block coverage plan. -/
def trelCoverageVerified : VerifiedBy (List RowRange) TrelCoverageSpec where
  payload := trelRanges
  check := trelCoverageCheck
  sound := trelCoverageCheck_sound
  checked := trelCoverageCheck_ok

/-- Semantic row-block coverage facts extracted from the closed Boolean certificate. -/
theorem trelCoverageSpec : TrelCoverageSpec trelRanges :=
  VerifiedBy.proof trelCoverageVerified

end ResidualCoverage
end Closed
end KnuthFasc8AEx210
