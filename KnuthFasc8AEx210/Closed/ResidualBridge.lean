import KnuthFasc8AEx210.Closed.ResidualChunk

namespace KnuthFasc8AEx210
namespace Closed
namespace ResidualBridge

open ResidualChunk

/-!
# Bridge from local row-block residuals to global row witnesses

A row-block certificate proves residual equations for local row indices
`0, ..., rowCount - 1`. Later matrix-level lemmas need to talk about global
row numbers. This file provides the small semantic bridge from a local row
inside a chunk to the corresponding global row `startRow + localRow`.
-/

/-- A residual equation for a global row as witnessed by one row-block chunk. -/
def GlobalRowWitness (c : Chunk) (eigenvalue : Nat) (x : ByteArray)
    (globalRow : Nat) : Prop :=
  ∃ localRow,
    localRow < c.rowCount ∧
    globalRow = c.startRow + localRow ∧
    rowDotMod101 c x localRow =
      UInt8.ofNat ((eigenvalue * x.data[c.startRow + localRow]!.toNat) % 101)

/-- The local row theorem stored in `ResidualChunk.Spec`. -/
theorem rows_of_spec {c : Chunk} {eigenvalue : Nat} {x : ByteArray}
    (h : Spec c eigenvalue x) : RowsSpec c eigenvalue x :=
  h.rows

/-- A certified local row gives a witnessed residual equation for its global row. -/
theorem globalWitness_of_local {c : Chunk} {eigenvalue : Nat} {x : ByteArray}
    (h : Spec c eigenvalue x) {localRow : Nat} (hlocal : localRow < c.rowCount) :
    GlobalRowWitness c eigenvalue x (c.startRow + localRow) := by
  exact ⟨localRow, hlocal, rfl, h.rows localRow hlocal⟩

/-- A successful executable chunk check gives global row witnesses for all local rows. -/
theorem globalWitness_of_check {c : Chunk} {eigenvalue : Nat} {x : ByteArray}
    (hcheck : check c eigenvalue x = true) {localRow : Nat}
    (hlocal : localRow < c.rowCount) :
    GlobalRowWitness c eigenvalue x (c.startRow + localRow) :=
  globalWitness_of_local (check_sound c eigenvalue x hcheck) hlocal

/-- Regression theorem for the identity test chunk. -/
example : GlobalRowWitness identity2 1 (⟨#[7, 9]⟩) 1 := by
  exact globalWitness_of_check (c := identity2) (eigenvalue := 1) (x := ⟨#[7, 9]⟩)
    (by native_decide) (localRow := 1) (by native_decide)

end ResidualBridge
end Closed
end KnuthFasc8AEx210
