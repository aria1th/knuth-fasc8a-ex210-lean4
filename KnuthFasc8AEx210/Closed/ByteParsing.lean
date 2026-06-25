import Mathlib

namespace KnuthFasc8AEx210
namespace Closed
namespace ByteParsing

universe u v

/-!
# Small pure parsers for checked-in binary certificates

The C++ verifiers read fixed little-endian binary formats.  A closed Lean
certificate checker should parse the same byte streams inside Lean.  This file
contains a small pure parser core over `List Nat`; later commits can attach
file-specific invariants such as `KMP101`, `KMV101`, `KMC201`, and `KMW2CERT`.
-/

/-- A byte stream represented as natural numbers.  File-specific parsers should
separately require every entry to be `< 256`. -/
abbrev Bytes := List Nat

/-- Parser type used for small certificate formats. -/
abbrev Parser (α : Type u) := Bytes → Option (α × Bytes)

namespace Parser

/-- Run two parsers in sequence. -/
def bind {α : Type u} {β : Type v} (p : Parser α) (q : α → Parser β) : Parser β :=
  fun input =>
    match p input with
    | none => none
    | some (a, rest) => q a rest

/-- Parser that returns a fixed value without consuming input. -/
def pure {α : Type u} (a : α) : Parser α := fun input => some (a, input)

/-- Parser failure. -/
def fail {α : Type u} : Parser α := fun _ => none

end Parser

/-- Take `n` bytes from the front of a stream. -/
def take? : Nat → Bytes → Option (Bytes × Bytes)
  | 0, bs => some ([], bs)
  | _ + 1, [] => none
  | n + 1, b :: bs =>
      match take? n bs with
      | none => none
      | some (pre, rest) => some (b :: pre, rest)

/-- Little-endian value of a byte list, interpreted without reducing modulo anything. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b + 256 * leNat bs

@[simp] theorem leNat_nil : leNat [] = 0 := rfl

@[simp] theorem leNat_cons (b : Nat) (bs : Bytes) :
    leNat (b :: bs) = b + 256 * leNat bs := rfl

/-- Parse exactly one byte. -/
def byte? : Parser Nat
  | [] => none
  | b :: rest => some (b, rest)

/-- Parse a little-endian unsigned 32-bit word as a natural number. -/
def u32LE? : Parser Nat := fun input =>
  match take? 4 input with
  | none => none
  | some (word, rest) => some (leNat word, rest)

/-- Parse a little-endian unsigned 64-bit word as a natural number. -/
def u64LE? : Parser Nat := fun input =>
  match take? 8 input with
  | none => none
  | some (word, rest) => some (leNat word, rest)

/-- Parse an exact byte-string tag. -/
def tag? (tag : Bytes) : Parser Unit := fun input =>
  match take? tag.length input with
  | some (got, rest) => if got = tag then some ((), rest) else none
  | none => none

@[simp] theorem take?_zero (bs : Bytes) : take? 0 bs = some ([], bs) := rfl

@[simp] theorem byte?_cons (b : Nat) (bs : Bytes) : byte? (b :: bs) = some (b, bs) := rfl

end ByteParsing
end Closed
end KnuthFasc8AEx210
