import KnuthFasc8AEx210.Closed.ByteParsing

namespace KnuthFasc8AEx210
namespace Closed
namespace Formats

open ByteParsing

/-!
# Parsers for the small certificate formats

These definitions mirror the binary layouts read by `verify_visible.cpp` and
`verify_rank_cert.cpp`.  They are deliberately pure and executable.
-/

/-- ASCII bytes for an eight-byte magic tag, including the two zero bytes used
by the source formats. -/
def kmp101Tag : Bytes := [75, 77, 80, 49, 48, 49, 0, 0]

def kmv101Tag : Bytes := [75, 77, 86, 49, 48, 49, 0, 0]

/-- Polynomial payload from a `KMP101` file.  Coefficients are stored in
ascending order. -/
structure KMP101 where
  coeffs : Bytes
  deriving DecidableEq, Repr

/-- Eigenvector payload from a `KMV101` file. -/
structure KMV101 where
  dimension : Nat
  pivot : Nat
  entries : Bytes
  deriving DecidableEq, Repr

/-- All coefficients belong to `F_101`, and the polynomial is nonempty. -/
def KMP101.valid (p : KMP101) : Bool :=
  (!p.coeffs.isEmpty) && p.coeffs.all (fun c => c < 101)

/-- The vector length agrees with its header, its pivot is in range and nonzero,
and all entries belong to `F_101`. -/
def KMV101.valid (v : KMV101) : Bool :=
  (v.entries.length == v.dimension) &&
    (v.pivot < v.dimension) &&
    (v.entries.getD v.pivot 0 != 0) &&
    v.entries.all (fun c => c < 101)

/-- Parse the payload of a `KMP101` file, leaving any trailing bytes visible. -/
def parseKMP101? : Parser KMP101 := fun input =>
  match tag? kmp101Tag input with
  | none => none
  | some (_, afterTag) =>
      match u32LE? afterTag with
      | none => none
      | some (n, afterLength) =>
          match take? n afterLength with
          | none => none
          | some (coeffs, rest) => some (⟨coeffs⟩, rest)

/-- Parse the payload of a `KMV101` file, leaving any trailing bytes visible. -/
def parseKMV101? : Parser KMV101 := fun input =>
  match tag? kmv101Tag input with
  | none => none
  | some (_, afterTag) =>
      match u32LE? afterTag with
      | none => none
      | some (n, afterDimension) =>
          match u32LE? afterDimension with
          | none => none
          | some (pivot, afterPivot) =>
              match take? n afterPivot with
              | none => none
              | some (entries, rest) => some (⟨n, pivot, entries⟩, rest)

/-- Parse a complete polynomial file and reject invalid or trailing data. -/
def checkKMP101File (input : Bytes) : Bool :=
  match parseKMP101? input with
  | some (p, []) => p.valid
  | _ => false

/-- Parse a complete eigenvector file and reject invalid or trailing data. -/
def checkKMV101File (input : Bytes) : Bool :=
  match parseKMV101? input with
  | some (v, []) => v.valid
  | _ => false

/-- A tiny synthetic `KMP101` file used to regression-test the parser. -/
def kmp101Example : Bytes :=
  kmp101Tag ++ [3, 0, 0, 0] ++ [1, 2, 3]

/-- A tiny synthetic `KMV101` file used to regression-test the parser. -/
def kmv101Example : Bytes :=
  kmv101Tag ++ [3, 0, 0, 0] ++ [1, 0, 0, 0] ++ [0, 7, 9]

example : parseKMP101? kmp101Example = some (⟨[1, 2, 3]⟩, []) := by
  native_decide

example : checkKMP101File kmp101Example = true := by
  native_decide

example : parseKMV101? kmv101Example = some (⟨3, 1, [0, 7, 9]⟩, []) := by
  native_decide

example : checkKMV101File kmv101Example = true := by
  native_decide

end Formats
end Closed
end KnuthFasc8AEx210
