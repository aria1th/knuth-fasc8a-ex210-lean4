import KnuthFasc8AEx210.Closed.ByteParsing

namespace KnuthFasc8AEx210
namespace Closed
namespace FileFormats

open ByteParsing

/-!
# Parsers for the small certificate file formats

The first Layer-A closure target is the visible-factor certificate.  The C++
checker reads two small binary formats there:

* `KMP101`: a polynomial over `F_101`, stored as a coefficient count followed by
  that many bytes;
* `KMV101`: a vector over `F_101`, stored as dimension, distinguished pivot,
  and that many bytes.

The parsers here are intentionally pure Lean functions over byte lists.  Later
commits can attach the concrete checked-in byte payloads and prove that the
visible-factor checker over these parsed objects implies the corresponding
field of `SourceRepositoryCertificate`.
-/

/-- ASCII bytes for `KMP101\0\0`.  The C++ verifier checks the first six bytes. -/
def kmp101Tag : Bytes := [75, 77, 80, 49, 48, 49, 0, 0]

/-- ASCII bytes for `KMV101\0\0`.  The C++ verifier checks the first six bytes. -/
def kmv101Tag : Bytes := [75, 77, 86, 49, 48, 49, 0, 0]

/-- Polynomial payload from a `KMP101` file. -/
structure KMP101 where
  count : Nat
  coeffs : List Nat
  deriving Repr, DecidableEq

namespace KMP101

/-- Well-formedness of the parsed polynomial payload. -/
def Valid (p : KMP101) : Prop :=
  p.coeffs.length = p.count ∧ ∀ b ∈ p.coeffs, b < 101

/-- Executable well-formedness check for `KMP101`. -/
def check (p : KMP101) : Bool :=
  decide p.Valid

/-- Soundness of the executable well-formedness check. -/
theorem check_sound (p : KMP101) (h : p.check = true) : p.Valid := by
  simpa [check] using h

end KMP101

/-- Eigenvector payload from a `KMV101` file. -/
structure KMV101 where
  n : Nat
  pivot : Nat
  values : List Nat
  deriving Repr, DecidableEq

namespace KMV101

/-- Well-formedness of the parsed eigenvector payload. -/
def Valid (v : KMV101) : Prop :=
  v.values.length = v.n ∧ v.pivot < v.n ∧ v.values.get? v.pivot ≠ some 0 ∧
    ∀ b ∈ v.values, b < 101

/-- Executable well-formedness check for `KMV101`. -/
def check (v : KMV101) : Bool :=
  decide v.Valid

/-- Soundness of the executable well-formedness check. -/
theorem check_sound (v : KMV101) (h : v.check = true) : v.Valid := by
  simpa [check] using h

end KMV101

/-- Parse a `KMP101` polynomial payload, leaving any unused bytes as the parser rest. -/
def parseKMP101? : Parser KMP101 := fun input =>
  match tag? kmp101Tag input with
  | none => none
  | some (_, rest₁) =>
      match u32LE? rest₁ with
      | none => none
      | some (count, rest₂) =>
          match take? count rest₂ with
          | none => none
          | some (coeffs, rest₃) => some ({ count, coeffs }, rest₃)

/-- Parse a whole `KMP101` file with no trailing bytes. -/
def parseKMP101Exact? (input : Bytes) : Option KMP101 :=
  match parseKMP101? input with
  | some (p, []) => some p
  | _ => none

/-- Parse a `KMV101` eigenvector payload, leaving any unused bytes as the parser rest. -/
def parseKMV101? : Parser KMV101 := fun input =>
  match tag? kmv101Tag input with
  | none => none
  | some (_, rest₁) =>
      match u32LE? rest₁ with
      | none => none
      | some (n, rest₂) =>
          match u32LE? rest₂ with
          | none => none
          | some (pivot, rest₃) =>
              match take? n rest₃ with
              | none => none
              | some (values, rest₄) => some ({ n, pivot, values }, rest₄)

/-- Parse a whole `KMV101` file with no trailing bytes. -/
def parseKMV101Exact? (input : Bytes) : Option KMV101 :=
  match parseKMV101? input with
  | some (v, []) => some v
  | _ => none

/-- A checked `KMP101` parse yields a valid polynomial payload. -/
theorem parseKMP101Exact_check_sound {input : Bytes} {p : KMP101}
    (hparse : parseKMP101Exact? input = some p) (hcheck : p.check = true) :
    p.Valid :=
  KMP101.check_sound p hcheck

/-- A checked `KMV101` parse yields a valid eigenvector payload. -/
theorem parseKMV101Exact_check_sound {input : Bytes} {v : KMV101}
    (hparse : parseKMV101Exact? input = some v) (hcheck : v.check = true) :
    v.Valid :=
  KMV101.check_sound v hcheck

end FileFormats
end Closed
end KnuthFasc8AEx210
