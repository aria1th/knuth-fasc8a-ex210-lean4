import Mathlib

namespace KnuthFasc8AEx210
namespace Closed
namespace FastHex

/-!
# ByteArray-based hexadecimal decoding

This decoder is intended for the multi-megabyte matrix and rank certificates.
It scans the UTF-8 input once and appends directly to a `ByteArray`.
-/

/-- Convert an ASCII hexadecimal byte to a nibble. -/
def nibble? (c : UInt8) : Option UInt8 :=
  if c ≥ 48 && c ≤ 57 then
    some (c - 48)
  else if c ≥ 65 && c ≤ 70 then
    some (c - 65 + 10)
  else if c ≥ 97 && c ≤ 102 then
    some (c - 97 + 10)
  else
    none

/-- ASCII whitespace accepted between encoded bytes. -/
def isWhitespace (c : UInt8) : Bool :=
  c = 32 || c = 10 || c = 13 || c = 9

/-- Decode hexadecimal text directly to a byte array. -/
def decode? (s : String) : Option ByteArray :=
  let input := s.toUTF8
  let rec loop (i : Nat) (high : Option UInt8) (out : ByteArray) : Option ByteArray :=
    if h : i < input.size then
      let c := input[i]'h
      if isWhitespace c then
        loop (i + 1) high out
      else
        match nibble? c with
        | none => none
        | some n =>
            match high with
            | none => loop (i + 1) (some n) out
            | some hi => loop (i + 1) none (out.push (hi * 16 + n))
    else
      match high with
      | none => some out
      | some _ => none
  termination_by input.size - i
  loop 0 none ByteArray.empty

/-- Convert a decoded byte array to the list representation used by the small
format parsers. -/
def toNatList (bytes : ByteArray) : List Nat :=
  bytes.data.toList.map UInt8.toNat

example : (decode? "4b4d503130310000").map ByteArray.size = some 8 := by
  native_decide

example :
    (decode? "4b 4d\n50").map toNatList = some [75, 77, 80] := by
  native_decide

example : decode? "0" = none := by
  native_decide

end FastHex
end Closed
end KnuthFasc8AEx210
