import Mathlib

namespace KnuthFasc8AEx210
namespace Closed
namespace ResidualCoverage

/-!
# Coverage of contiguous residual row blocks

The released `Trel+` residual is split into 1,024-row certificates.  This module
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

/-- The generated row intervals cover all `16831` rows exactly once. -/
theorem trelRanges_cover : covers 16831 trelRanges = true := by
  native_decide

/-- The number of expected independently checked row blocks. -/
theorem trelRanges_length : trelRanges.length = 17 := by
  native_decide

end ResidualCoverage
end Closed
end KnuthFasc8AEx210
