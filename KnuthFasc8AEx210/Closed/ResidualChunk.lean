import KnuthFasc8AEx210.Closed.ByteCursor

namespace KnuthFasc8AEx210
namespace Closed
namespace ResidualChunk

open ByteCursor

/-!
# Row-block certificates for sparse eigenvector residuals

A full released matrix is too large to elaborate and execute as one ordinary
Lean declaration.  The deterministic exporter therefore splits its CSR rows
into independent blocks.  Each block contains all nonzero entries of a
contiguous row interval, while column indices still refer to the full vector.
-/

/-- Magic bytes for the row-chunk format `KRC101`. -/
def krc101Tag : ByteArray := ⟨#[75, 82, 67, 49, 48, 49, 0, 0]⟩

/-- A contiguous block of rows from a sparse matrix over `F_101`. -/
structure Chunk where
  dimension : Nat
  startRow : Nat
  rowCount : Nat
  nnz : Nat
  rowPtr : Array Nat
  columns : Array Nat
  values : ByteArray
  deriving Inhabited

/-- Check that an array is nondecreasing. -/
def nondecreasing (xs : Array Nat) : Bool := Id.run do
  let mut ok := true
  for i in [0:xs.size - 1] do
    if xs[i]! > xs[i + 1]! then
      ok := false
  return ok

/-- Structural conditions required by the row-block checker. -/
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

/-- Parse a complete `KRC101` row-block payload. -/
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

/-- Dot product of one local row with a full byte vector, reduced modulo `101`. -/
def rowDotMod101 (c : Chunk) (x : ByteArray) (localRow : Nat) : UInt8 := Id.run do
  let first := c.rowPtr[localRow]!
  let stop := c.rowPtr[localRow + 1]!
  let mut acc := 0
  for k in [first:stop] do
    let column := c.columns[k]!
    acc := (acc + c.values.data[k]!.toNat * x.data[column]!.toNat) % 101
  return UInt8.ofNat acc

/-- Check every residual equation in this row block. -/
def rowsResidualOk (c : Chunk) (eigenvalue : Nat) (x : ByteArray) : Bool := Id.run do
  let mut ok := true
  for localRow in [0:c.rowCount] do
    let globalRow := c.startRow + localRow
    let lhs := rowDotMod101 c x localRow
    let rhs := UInt8.ofNat ((eigenvalue * x.data[globalRow]!.toNat) % 101)
    if lhs != rhs then
      ok := false
  return ok

/-- Executable structural and residual checker for one row block. -/
def check (c : Chunk) (eigenvalue : Nat) (x : ByteArray) : Bool :=
  c.valid &&
  (x.size == c.dimension) &&
  x.data.all (fun value => value.toNat < 101) &&
  rowsResidualOk c eigenvalue x

/-- Proposition-level wrapper used by the closed-certificate layer. -/
def Spec (c : Chunk) (eigenvalue : Nat) (x : ByteArray) : Prop :=
  check c eigenvalue x = true

/-- Soundness is definitional at the executable-certificate boundary. -/
theorem check_sound (c : Chunk) (eigenvalue : Nat) (x : ByteArray)
    (h : check c eigenvalue x = true) : Spec c eigenvalue x := h

/-- A two-row identity block used to regression-test parsing and checking. -/
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

end ResidualChunk
end Closed
end KnuthFasc8AEx210
