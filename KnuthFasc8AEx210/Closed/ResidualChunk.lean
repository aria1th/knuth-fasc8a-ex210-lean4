import KnuthFasc8AEx210.Closed.ByteCursor

namespace KnuthFasc8AEx210
namespace Closed
namespace ResidualChunk

open ByteCursor

/-!
# Row-block certificates for sparse eigenvector residuals

A full released matrix is too large to elaborate and execute as one ordinary
Lean declaration. The deterministic exporter therefore splits its CSR rows
into independent blocks. Each block contains all nonzero entries of a
contiguous row interval, while column indices still refer to the full vector.
-/

def krc101Tag : ByteArray := ⟨#[75, 82, 67, 49, 48, 49, 0, 0]⟩

structure Chunk where
  dimension : Nat
  startRow : Nat
  rowCount : Nat
  nnz : Nat
  rowPtr : Array Nat
  columns : Array Nat
  values : ByteArray
  deriving Inhabited

def nondecreasing (xs : Array Nat) : Bool := Id.run do
  let mut ok := true
  for i in [0:xs.size - 1] do
    if xs[i]! > xs[i + 1]! then
      ok := false
  return ok

def Chunk.valid (c : Chunk) : Bool :=
  (c.startRow + c.rowCount ≤ c.dimension) &&
  (c.rowPtr.size == c.rowCount + 1) &&
  (c.columns.size == c.nnz) &&
  (c.values.size == c.nnz) &&
  (c.rowPtr[0]! == 0) &&
  (c.rowPtr[c.rowCount]! == c.nnz) &&
  nondecreasing c.rowPtr &&
  c.columns.all (fun column => column < c.dimension) &&
  c.values.data.all (fun value => value.toNat < 101)

def parseChunk? (bytes : ByteArray) : Option Chunk := do
  let c₀ := Cursor.start bytes
  let c₁ ← c₀.readTag? krc101Tag
  let (dimension, c₂) ← c₁.readU32?
  let (startRow, c₃) ← c₂.readU32?
  let (rowCount, c₄) ← c₃.readU32?
  let (nnz, c₅) ← c₄.readU64?
  let (rowPtr, c₆) ← c₅.readNatArrayLE? 8 (rowCount + 1)
  let (columns, c₇) ← c₆.readNatArrayLE? 4 nnz
  let (values, c₈) ← c₇.readBytes? nnz
  if c₈.atEnd then
    let chunk : Chunk :=
      { dimension, startRow, rowCount, nnz, rowPtr, columns, values }
    if chunk.valid then some chunk else none
  else
    none

def rowDotMod101 (c : Chunk) (x : ByteArray) (localRow : Nat) : UInt8 := Id.run do
  let first := c.rowPtr[localRow]!
  let stop := c.rowPtr[localRow + 1]!
  let mut acc := 0
  for k in [first:stop] do
    let column := c.columns[k]!
    acc := (acc + c.values.data[k]!.toNat * x.data[column]!.toNat) % 101
  return UInt8.ofNat acc

/-- Boolean form of one local residual equation. -/
def rowResidualOk (c : Chunk) (eigenvalue : Nat) (x : ByteArray)
    (localRow : Nat) : Bool :=
  rowDotMod101 c x localRow ==
    UInt8.ofNat ((eigenvalue * x.data[c.startRow + localRow]!.toNat) % 101)

/-- Check every residual equation in this row block. -/
def rowsResidualOk (c : Chunk) (eigenvalue : Nat) (x : ByteArray) : Bool :=
  (List.range c.rowCount).all (rowResidualOk c eigenvalue x)

/-- Semantic statement represented by `rowsResidualOk`. -/
def RowsSpec (c : Chunk) (eigenvalue : Nat) (x : ByteArray) : Prop :=
  ∀ localRow, localRow < c.rowCount →
    rowDotMod101 c x localRow =
      UInt8.ofNat ((eigenvalue * x.data[c.startRow + localRow]!.toNat) % 101)

/-- A successful row checker yields every individual residual equation. -/
theorem rowsResidualOk_sound (c : Chunk) (eigenvalue : Nat) (x : ByteArray)
    (h : rowsResidualOk c eigenvalue x = true) : RowsSpec c eigenvalue x := by
  intro localRow hlocal
  have hmem : localRow ∈ List.range c.rowCount := List.mem_range.mpr hlocal
  have hall : ∀ i ∈ List.range c.rowCount, rowResidualOk c eigenvalue x i = true := by
    simpa [rowsResidualOk] using h
  have hi := hall localRow hmem
  simpa [rowResidualOk] using hi

/-- Executable structural and residual checker for one row block. -/
def check (c : Chunk) (eigenvalue : Nat) (x : ByteArray) : Bool :=
  c.valid &&
  ((x.size == c.dimension) &&
    (x.data.all (fun value => value.toNat < 101) &&
      rowsResidualOk c eigenvalue x))

/-- Semantic proposition certified by a successful chunk check. -/
structure Spec (c : Chunk) (eigenvalue : Nat) (x : ByteArray) : Prop where
  valid : c.valid = true
  vectorSize : x.size = c.dimension
  vectorValues : x.data.all (fun value => value.toNat < 101) = true
  rows : RowsSpec c eigenvalue x

/-- Soundness of the executable chunk checker. -/
theorem check_sound (c : Chunk) (eigenvalue : Nat) (x : ByteArray)
    (h : check c eigenvalue x = true) : Spec c eigenvalue x := by
  have parts :
      c.valid = true ∧
        (x.size = c.dimension ∧
          (x.data.all (fun value => value.toNat < 101) = true ∧
            rowsResidualOk c eigenvalue x = true)) := by
    simpa [check, Bool.and_eq_true] using h
  exact
    { valid := parts.1
      vectorSize := parts.2.1
      vectorValues := parts.2.2.1
      rows := rowsResidualOk_sound c eigenvalue x parts.2.2.2 }

def identity2 : Chunk where
  dimension := 2
  startRow := 0
  rowCount := 2
  nnz := 2
  rowPtr := #[0, 1, 2]
  columns := #[0, 1]
  values := ⟨#[1, 1]⟩

private def vector79 : ByteArray := ⟨#[7, 9]⟩

example : identity2.valid = true := by native_decide

example : rowsResidualOk identity2 1 vector79 = true := by native_decide

example : check identity2 1 vector79 = true := by native_decide

example : Spec identity2 1 vector79 :=
  check_sound identity2 1 vector79 (by native_decide)

end ResidualChunk
end Closed
end KnuthFasc8AEx210
