import Mathlib

namespace KnuthFasc8AEx210
namespace Closed
namespace ByteCursor

/-!
# Efficient cursor over a `ByteArray`

The small certificate parsers use lists for simple proofs and regression tests.
The multi-megabyte CSR matrices instead need a cursor that keeps the decoded
bytes packed and produces arrays directly.
-/

structure Cursor where
  bytes : ByteArray
  pos : Nat
  deriving Inhabited, Repr

/-- Start reading a byte array at position zero. -/
def Cursor.start (bytes : ByteArray) : Cursor := ⟨bytes, 0⟩

/-- Number of unread bytes. -/
def Cursor.remaining (c : Cursor) : Nat := c.bytes.size - c.pos

/-- Read a little-endian word at a known offset, using default zero out of range. -/
def wordAtLE (bytes : ByteArray) (base width : Nat) : Nat := Id.run do
  let mut value := 0
  let mut scale := 1
  for i in [0:width] do
    value := value + bytes.data[base + i]!.toNat * scale
    scale := scale * 256
  return value

/-- Read one little-endian word of `width` bytes. -/
def Cursor.readNatLE? (c : Cursor) (width : Nat) : Option (Nat × Cursor) :=
  if c.pos + width ≤ c.bytes.size then
    some (wordAtLE c.bytes c.pos width, ⟨c.bytes, c.pos + width⟩)
  else
    none

/-- Read a 32-bit little-endian word. -/
def Cursor.readU32? (c : Cursor) : Option (Nat × Cursor) := c.readNatLE? 4

/-- Read a 64-bit little-endian word. -/
def Cursor.readU64? (c : Cursor) : Option (Nat × Cursor) := c.readNatLE? 8

/-- Read `count` consecutive little-endian words directly into an array. -/
def Cursor.readNatArrayLE? (c : Cursor) (width count : Nat) : Option (Array Nat × Cursor) :=
  if c.pos + width * count ≤ c.bytes.size then
    let values := Id.run do
      let mut out := Array.mkEmpty count
      for i in [0:count] do
        out := out.push (wordAtLE c.bytes (c.pos + width * i) width)
      return out
    some (values, ⟨c.bytes, c.pos + width * count⟩)
  else
    none

/-- Read `count` raw bytes without unpacking them. -/
def Cursor.readBytes? (c : Cursor) (count : Nat) : Option (ByteArray × Cursor) :=
  if c.pos + count ≤ c.bytes.size then
    let values := Id.run do
      let mut out := ByteArray.empty
      for i in [0:count] do
        out := out.push c.bytes.data[c.pos + i]!
      return out
    some (values, ⟨c.bytes, c.pos + count⟩)
  else
    none

/-- Read and compare an exact byte tag. -/
def Cursor.readTag? (c : Cursor) (tag : ByteArray) : Option Cursor :=
  match c.readBytes? tag.size with
  | none => none
  | some (got, rest) => if got = tag then some rest else none

/-- The cursor has consumed the whole input. -/
def Cursor.atEnd (c : Cursor) : Bool := c.pos == c.bytes.size

private def exampleBytes : ByteArray := ⟨#[1, 2, 3, 4, 5, 6]⟩

example : (Cursor.start exampleBytes).readU32?.map Prod.fst = some 67305985 := by
  native_decide

example : ((Cursor.start exampleBytes).readBytes? 3).map (fun p => p.1.size) = some 3 := by
  native_decide

example : (Cursor.start exampleBytes).remaining = 6 := by
  native_decide

end ByteCursor
end Closed
end KnuthFasc8AEx210
