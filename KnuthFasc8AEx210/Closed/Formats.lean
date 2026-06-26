import KnuthFasc8AEx210.Closed.ByteParsing

namespace KnuthFasc8AEx210
namespace Closed
namespace Formats

open ByteParsing

/-! Pure parsers for the small visible-factor certificate formats. -/

def kmp101Tag : Bytes := [75, 77, 80, 49, 48, 49, 0, 0]

def kmv101Tag : Bytes := [75, 77, 86, 49, 48, 49, 0, 0]

structure KMP101 where
  coeffs : Bytes
  deriving DecidableEq, Repr, Inhabited

structure KMV101 where
  dimension : Nat
  pivot : Nat
  entries : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- The closed terminal vector format is a dimension followed by that many bytes. -/
structure FinishVector where
  dimension : Nat
  entries : Bytes
  deriving DecidableEq, Repr, Inhabited

def KMP101.valid (p : KMP101) : Bool :=
  (!p.coeffs.isEmpty) && p.coeffs.all (fun c => c < 101)

def KMV101.valid (v : KMV101) : Bool :=
  (v.entries.length == v.dimension) &&
    (v.pivot < v.dimension) &&
    (v.entries.getD v.pivot 0 != 0) &&
    v.entries.all (fun c => c < 101)

def FinishVector.valid (v : FinishVector) : Bool :=
  (v.entries.length == v.dimension) && v.entries.all (fun c => c < 101)

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

def parseFinishVector? : Parser FinishVector := fun input =>
  match u32LE? input with
  | none => none
  | some (n, afterDimension) =>
      match take? n afterDimension with
      | none => none
      | some (entries, rest) => some (⟨n, entries⟩, rest)

def parseKMP101File? (input : Bytes) : Option KMP101 :=
  match parseKMP101? input with
  | some (p, []) => if p.valid then some p else none
  | _ => none

def parseKMV101File? (input : Bytes) : Option KMV101 :=
  match parseKMV101? input with
  | some (v, []) => if v.valid then some v else none
  | _ => none

def parseFinishVectorFile? (input : Bytes) : Option FinishVector :=
  match parseFinishVector? input with
  | some (v, []) => if v.valid then some v else none
  | _ => none

def checkKMP101File (input : Bytes) : Bool :=
  (parseKMP101File? input).isSome

def checkKMV101File (input : Bytes) : Bool :=
  (parseKMV101File? input).isSome

def checkFinishVectorFile (input : Bytes) : Bool :=
  (parseFinishVectorFile? input).isSome

def kmp101Example : Bytes :=
  kmp101Tag ++ [3, 0, 0, 0] ++ [1, 2, 3]

def kmv101Example : Bytes :=
  kmv101Tag ++ [3, 0, 0, 0] ++ [1, 0, 0, 0] ++ [0, 7, 9]

def finishVectorExample : Bytes :=
  [3, 0, 0, 0] ++ [4, 5, 6]

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

example : parseFinishVector? finishVectorExample = some (⟨3, [4, 5, 6]⟩, []) := by
  native_decide

example : parseFinishVectorFile? finishVectorExample = some ⟨3, [4, 5, 6]⟩ := by
  native_decide

example : checkFinishVectorFile finishVectorExample = true := by
  native_decide

end Formats
end Closed
end KnuthFasc8AEx210
