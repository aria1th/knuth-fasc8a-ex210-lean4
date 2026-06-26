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
  deriving DecidableEq, Repr, Inhabited

/-- Eigenvector payload from a `KMV101` file. -/
structure KMV101 where
  dimension : Nat
  pivot : Nat
  entries : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- All coefficients belong to `F_101`, and the polynomial is nonempty. -/
def KMP101.valid (p : KMP101) : Bool :=
  (!p.coeffs.isEmpty) && p.coeffs.all (fun c => c < 101)

/-- Proposition-level validity corresponding to `KMP101.valid`. -/
def KMP101.Valid (p : KMP101) : Prop :=
  p.valid = true

/-- The vector length agrees with its header, its pivot is in range and nonzero,
and all entries belong to `F_101`. -/
def KMV101.valid (v : KMV101) : Bool :=
  (v.entries.length == v.dimension) &&
    (v.pivot < v.dimension) &&
    (v.entries.getD v.pivot 0 != 0) &&
    v.entries.all (fun c => c < 101)

/-- Proposition-level validity corresponding to `KMV101.valid`. -/
def KMV101.Valid (v : KMV101) : Prop :=
  v.valid = true

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
def parseKMP101File? (input : Bytes) : Option KMP101 :=
  match parseKMP101? input with
  | some (p, []) => if p.valid then some p else none
  | _ => none

/-- Parse a complete eigenvector file and reject invalid or trailing data. -/
def parseKMV101File? (input : Bytes) : Option KMV101 :=
  match parseKMV101? input with
  | some (v, []) => if v.valid then some v else none
  | _ => none

/-- A successful complete `KMP101` parse is valid by construction. -/
theorem parseKMP101File?_sound {input : Bytes} {p : KMP101}
    (h : parseKMP101File? input = some p) : p.Valid := by
  unfold parseKMP101File? at h
  cases hparse : parseKMP101? input with
  | none => simp [hparse] at h
  | some parsed =>
      rcases parsed with ⟨q, rest⟩
      cases rest with
      | nil =>
          cases hvalid : q.valid
          · simp [hparse, hvalid] at h
          · simp [hparse, hvalid, KMP101.Valid] at h ⊢
            exact h.symm ▸ hvalid
      | cons b rest =>
          simp [hparse] at h

/-- A successful complete `KMV101` parse is valid by construction. -/
theorem parseKMV101File?_sound {input : Bytes} {v : KMV101}
    (h : parseKMV101File? input = some v) : v.Valid := by
  unfold parseKMV101File? at h
  cases hparse : parseKMV101? input with
  | none => simp [hparse] at h
  | some parsed =>
      rcases parsed with ⟨w, rest⟩
      cases rest with
      | nil =>
          cases hvalid : w.valid
          · simp [hparse, hvalid] at h
          · simp [hparse, hvalid, KMV101.Valid] at h ⊢
            exact h.symm ▸ hvalid
      | cons b rest =>
          simp [hparse] at h

/-- Boolean form of `parseKMP101File?`. -/
def checkKMP101File (input : Bytes) : Bool :=
  (parseKMP101File? input).isSome

/-- Boolean form of `parseKMV101File?`. -/
def checkKMV101File (input : Bytes) : Bool :=
  (parseKMV101File? input).isSome

/-- Soundness of the Boolean complete-file check for `KMP101`. -/
theorem checkKMP101File_sound {input : Bytes} (h : checkKMP101File input = true) :
    ∃ p, parseKMP101File? input = some p ∧ p.Valid := by
  unfold checkKMP101File at h
  cases hparse : parseKMP101File? input with
  | none => simp [hparse] at h
  | some p => exact ⟨p, hparse, parseKMP101File?_sound hparse⟩

/-- Soundness of the Boolean complete-file check for `KMV101`. -/
theorem checkKMV101File_sound {input : Bytes} (h : checkKMV101File input = true) :
    ∃ v, parseKMV101File? input = some v ∧ v.Valid := by
  unfold checkKMV101File at h
  cases hparse : parseKMV101File? input with
  | none => simp [hparse] at h
  | some v => exact ⟨v, hparse, parseKMV101File?_sound hparse⟩

/-- A tiny synthetic `KMP101` file used to regression-test the parser. -/
def kmp101Example : Bytes :=
  kmp101Tag ++ [3, 0, 0, 0] ++ [1, 2, 3]

/-- A tiny synthetic `KMV101` file used to regression-test the parser. -/
def kmv101Example : Bytes :=
  kmv101Tag ++ [3, 0, 0, 0] ++ [1, 0, 0, 0] ++ [0, 7, 9]

example : parseKMP101? kmp101Example = some (⟨[1, 2, 3]⟩, []) := by
  native_decide

example : parseKMP101File? kmp101Example = some ⟨[1, 2, 3]⟩ := by
  native_decide

example : checkKMP101File kmp101Example = true := by
  native_decide

example : parseKMV101? kmv101Example = some (⟨3, 1, [0, 7, 9]⟩, []) := by
  native_decide

example : parseKMV101File? kmv101Example = some ⟨3, 1, [0, 7, 9]⟩ := by
  native_decide

example : checkKMV101File kmv101Example = true := by
  native_decide

end Formats
end Closed
end KnuthFasc8AEx210
