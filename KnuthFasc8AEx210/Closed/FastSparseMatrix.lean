import KnuthFasc8AEx210.Closed.ByteCursor

namespace KnuthFasc8AEx210
namespace Closed
namespace FastSparseMatrix

open ByteCursor

/-!
# Array-based `KMC201` parser and residual checker

This module keeps multi-megabyte matrices packed in arrays. It is the execution
path meant for the released `Tall_plus.kmc` and `Trel_plus.kmc` files.
-/

def kmc201Tag : ByteArray := ⟨#[75, 77, 67, 50, 48, 49, 0, 0]⟩

structure KMC201 where
  dimension : Nat
  prime : Nat
  nnz : Nat
  reserved₁ : Nat
  reserved₂ : Nat
  rowPtr : Array Nat
  columns : Array Nat
  values : ByteArray
  representatives : Array Nat
  deriving Inhabited

/-- Check that an array is nondecreasing. -/
def nondecreasing (xs : Array Nat) : Bool := Id.run do
  let mut ok := true
  for i in [0:xs.size - 1] do
    if xs[i]! > xs[i + 1]! then
      ok := false
  return ok

/-- Structural checks needed by the executable CSR multiplication. -/
def KMC201.valid (m : KMC201) : Bool :=
  (m.prime == 101) &&
  (m.rowPtr.size == m.dimension + 1) &&
  (m.columns.size == m.nnz) &&
  (m.values.size == m.nnz) &&
  (m.representatives.size == m.dimension) &&
  (m.rowPtr[0]! == 0) &&
  (m.rowPtr[m.dimension]! == m.nnz) &&
  nondecreasing m.rowPtr &&
  m.columns.all (fun c => c < m.dimension) &&
  m.values.data.all (fun a => a.toNat < 101)

/-- Parse one complete visible-check `KMC201` matrix from packed bytes. -/
def parseKMC201? (bytes : ByteArray) : Option KMC201 := do
  let c₀ := Cursor.start bytes
  let c₁ ← c₀.readTag? kmc201Tag
  let (dimension, c₂) ← c₁.readU32?
  let (prime, c₃) ← c₂.readU32?
  let (nnz, c₄) ← c₃.readU64?
  let (reserved₁, c₅) ← c₄.readU32?
  let (reserved₂, c₆) ← c₅.readU32?
  let (rowPtr, c₇) ← c₆.readNatArrayLE? 8 (dimension + 1)
  let (columns, c₈) ← c₇.readNatArrayLE? 4 nnz
  let (values, c₉) ← c₈.readBytes? nnz
  let (representatives, c₁₀) ← c₉.readNatArrayLE? 8 dimension
  if c₁₀.atEnd then
    let matrix : KMC201 :=
      { dimension, prime, nnz, reserved₁, reserved₂,
        rowPtr, columns, values, representatives }
    if matrix.valid then some matrix else none
  else
    none

/-- Dot product of one CSR row with a byte vector, reduced modulo `101`. -/
def rowDotMod101 (m : KMC201) (x : ByteArray) (row : Nat) : UInt8 := Id.run do
  let start := m.rowPtr[row]!
  let stop := m.rowPtr[row + 1]!
  let mut acc := 0
  for k in [start:stop] do
    let column := m.columns[k]!
    acc := (acc + m.values.data[k]!.toNat * x.data[column]!.toNat) % 101
  return UInt8.ofNat acc

/-- Sparse matrix-vector multiplication modulo `101`. -/
def mulVecMod101 (m : KMC201) (x : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for row in [0:m.dimension] do
    out := out.push (rowDotMod101 m x row)
  return out

/-- Scalar multiplication modulo `101`. -/
def smulVecMod101 (lam : Nat) (x : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:x.size] do
    out := out.push (UInt8.ofNat ((lam * x.data[i]!.toNat) % 101))
  return out

/-- Proposition certified by the executable eigenvector check. -/
def EigenSpec (m : KMC201) (lam : Nat) (x : ByteArray) : Prop :=
  m.valid = true ∧
  x.size = m.dimension ∧
  x.data.all (fun a => a.toNat < 101) = true ∧
  mulVecMod101 m x = smulVecMod101 lam x

/-- Executable eigenvector residual check. -/
def checkEigenMod101 (m : KMC201) (lam : Nat) (x : ByteArray) : Bool :=
  decide (EigenSpec m lam x)

/-- Soundness of `checkEigenMod101`. -/
theorem checkEigenMod101_sound (m : KMC201) (lam : Nat) (x : ByteArray)
    (h : checkEigenMod101 m lam x = true) : EigenSpec m lam x := by
  have h' : decide (EigenSpec m lam x) = true := by
    simpa [checkEigenMod101] using h
  exact of_decide_eq_true h'

/-- A small identity matrix used to regression-test the packed execution path. -/
def identity2 : KMC201 where
  dimension := 2
  prime := 101
  nnz := 2
  reserved₁ := 0
  reserved₂ := 0
  rowPtr := #[0, 1, 2]
  columns := #[0, 1]
  values := ⟨#[1, 1]⟩
  representatives := #[10, 20]

private def vector79 : ByteArray := ⟨#[7, 9]⟩

example : identity2.valid = true := by native_decide

example : mulVecMod101 identity2 vector79 = vector79 := by native_decide

example : checkEigenMod101 identity2 1 vector79 = true := by native_decide

end FastSparseMatrix
end Closed
end KnuthFasc8AEx210
