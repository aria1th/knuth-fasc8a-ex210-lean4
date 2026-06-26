import KnuthFasc8AEx210.Closed.ByteParsing

namespace KnuthFasc8AEx210
namespace Closed
namespace SparseMatrix

open ByteParsing

/-!
# `KMC201` sparse matrices and executable residual checks

This mirrors the CSR layout consumed by `verify_visible.cpp`: an eight-byte
magic tag; dimension, prime, edge count, and two reserved words; row pointers;
column indices; byte-valued coefficients; and canonical state representatives.
-/

def kmc201Tag : Bytes := [75, 77, 67, 50, 48, 49, 0, 0]

structure KMC201 where
  dimension : Nat
  prime : Nat
  nnz : Nat
  reserved₁ : Nat
  reserved₂ : Nat
  rowPtr : List Nat
  columns : List Nat
  values : List Nat
  representatives : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Structural well-formedness needed by the CSR multiplication checker. -/
def KMC201.Valid (m : KMC201) : Prop :=
  m.prime = 101 ∧
  m.rowPtr.length = m.dimension + 1 ∧
  m.columns.length = m.nnz ∧
  m.values.length = m.nnz ∧
  m.representatives.length = m.dimension ∧
  m.rowPtr.getD 0 1 = 0 ∧
  m.rowPtr.getD m.dimension 0 = m.nnz ∧
  m.rowPtr.Pairwise (· ≤ ·) ∧
  (∀ c ∈ m.columns, c < m.dimension) ∧
  (∀ a ∈ m.values, a < 101)

/-- Executable matrix well-formedness checker. -/
def KMC201.valid (m : KMC201) : Bool :=
  decide m.Valid

/-- Soundness of the executable matrix checker. -/
theorem KMC201.valid_sound (m : KMC201) (h : m.valid = true) : m.Valid := by
  exact of_decide_eq_true h

/-- Parse the full payload of a visible-check `KMC201` matrix. -/
def parseKMC201? : Parser KMC201 := fun input =>
  match tag? kmc201Tag input with
  | none => none
  | some (_, rest₀) =>
      match u32LE? rest₀ with
      | none => none
      | some (dimension, rest₁) =>
          match u32LE? rest₁ with
          | none => none
          | some (prime, rest₂) =>
              match u64LE? rest₂ with
              | none => none
              | some (nnz, rest₃) =>
                  match u32LE? rest₃ with
                  | none => none
                  | some (reserved₁, rest₄) =>
                      match u32LE? rest₄ with
                      | none => none
                      | some (reserved₂, rest₅) =>
                          match manyN? u64LE? (dimension + 1) rest₅ with
                          | none => none
                          | some (rowPtr, rest₆) =>
                              match manyN? u32LE? nnz rest₆ with
                              | none => none
                              | some (columns, rest₇) =>
                                  match take? nnz rest₇ with
                                  | none => none
                                  | some (values, rest₈) =>
                                      match manyN? u64LE? dimension rest₈ with
                                      | none => none
                                      | some (representatives, rest₉) =>
                                          some ({ dimension, prime, nnz, reserved₁, reserved₂,
                                            rowPtr, columns, values, representatives }, rest₉)

/-- Parse a complete matrix file and reject invalid or trailing data. -/
def parseKMC201File? (input : Bytes) : Option KMC201 :=
  match parseKMC201? input with
  | some (m, []) => if m.valid then some m else none
  | _ => none

/-- Dot product for one CSR row, reduced modulo `101`. -/
def rowDotMod101 (m : KMC201) (x : List Nat) (row : Nat) : Nat :=
  let start := m.rowPtr.getD row 0
  let stop := m.rowPtr.getD (row + 1) start
  (List.range (stop - start)).foldl
    (fun acc offset =>
      let k := start + offset
      let column := m.columns.getD k 0
      (acc + m.values.getD k 0 * x.getD column 0) % 101)
    0

/-- CSR matrix-vector multiplication modulo `101`. -/
def mulVecMod101 (m : KMC201) (x : List Nat) : List Nat :=
  (List.range m.dimension).map (rowDotMod101 m x)

/-- Scalar multiplication modulo `101`. -/
def smulVecMod101 (lam : Nat) (x : List Nat) : List Nat :=
  x.map (fun a => (lam * a) % 101)

/-- Mathematical specification checked by `checkEigenMod101`. -/
def EigenSpec (m : KMC201) (lam : Nat) (x : List Nat) : Prop :=
  m.Valid ∧ x.length = m.dimension ∧
    (∀ a ∈ x, a < 101) ∧
    mulVecMod101 m x = smulVecMod101 lam x

/-- Executable eigenvector residual checker modulo `101`. -/
def checkEigenMod101 (m : KMC201) (lam : Nat) (x : List Nat) : Bool :=
  decide (EigenSpec m lam x)

/-- Soundness of the executable residual checker. -/
theorem checkEigenMod101_sound (m : KMC201) (lam : Nat) (x : List Nat)
    (h : checkEigenMod101 m lam x = true) : EigenSpec m lam x := by
  exact of_decide_eq_true h

/-- A small identity matrix used to regression-test parsing and residual checks. -/
def identity2 : KMC201 where
  dimension := 2
  prime := 101
  nnz := 2
  reserved₁ := 0
  reserved₂ := 0
  rowPtr := [0, 1, 2]
  columns := [0, 1]
  values := [1, 1]
  representatives := [10, 20]

example : identity2.valid = true := by native_decide

example : mulVecMod101 identity2 [7, 9] = [7, 9] := by native_decide

example : checkEigenMod101 identity2 1 [7, 9] = true := by native_decide

end SparseMatrix
end Closed
end KnuthFasc8AEx210
