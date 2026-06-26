import KnuthFasc8AEx210.Closed.ByteParsing

namespace KnuthFasc8AEx210
namespace Closed
namespace Hex

open ByteParsing

/-! A small executable decoder for canonical hexadecimal certificate text. -/

/-- Convert one ASCII hexadecimal character to its value. -/
def nibble? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then
    some (n - 48)
  else if 65 ≤ n ∧ n ≤ 70 then
    some (n - 65 + 10)
  else if 97 ≤ n ∧ n ≤ 102 then
    some (n - 97 + 10)
  else
    none

/-- Whitespace accepted between encoded bytes. -/
def isWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\n' || c = '\r' || c = '\t'

/-- Decode a whitespace-free list of hexadecimal characters. -/
def decodeDigits? : List Char → Option Bytes
  | [] => some []
  | [_] => none
  | hi :: lo :: rest =>
      match nibble? hi, nibble? lo, decodeDigits? rest with
      | some h, some l, some tail => some ((16 * h + l) :: tail)
      | _, _, _ => none

/-- Decode hexadecimal text, ignoring ASCII whitespace. -/
def decode? (s : String) : Option Bytes :=
  decodeDigits? (s.toList.filter fun c => !isWhitespace c)

example : decode? "4b4d503130310000" = some [75, 77, 80, 49, 48, 49, 0, 0] := by
  native_decide

example : decode? "4b 4d\n50" = some [75, 77, 80] := by
  native_decide

example : decode? "0" = none := by
  native_decide

end Hex
end Closed
end KnuthFasc8AEx210
