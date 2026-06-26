import KnuthFasc8AEx210.Closed.BooleanCertificate
import KnuthFasc8AEx210.Closed.FastHex
import KnuthFasc8AEx210.Closed.ResidualChunk
import KnuthFasc8AEx210.Closed.EmbeddedVisible

namespace KnuthFasc8AEx210
namespace Closed
namespace EmbeddedTrelChunk0

open ResidualChunk EmbeddedVisible

/-!
# First closed row block of the released `Trel+` residual

This module verifies rows `0 .. 1023` of `Trel_plus * v = 50 * v` from a
self-contained `KRC101` row-block payload. Further generated modules will use
the same checker for the remaining contiguous blocks.
-/

def chunkHex : String :=
  include_str ".." / ".." / "data" / "lean" / "trel_residual" /
    "Trel_plus.rows.00000.01024.krc.hex"

def chunkBytes : ByteArray :=
  (FastHex.decode? chunkHex).getD ByteArray.empty

def chunk : Chunk :=
  (parseChunk? chunkBytes).getD default

/-- Executable specification of this exact released block. -/
def payloadCheck (c : Chunk) : Bool :=
  (c.dimension == 16831) &&
  (c.startRow == 0) &&
  (c.rowCount == 1024) &&
  ResidualChunk.check c 50 eigen50Packed

/-- Proposition-level wrapper for the executable block specification. -/
def PayloadSpec (c : Chunk) : Prop :=
  payloadCheck c = true

theorem payloadCheck_sound (c : Chunk) (h : payloadCheck c = true) : PayloadSpec c := h

/-- One native computation checks metadata and all 1,024 residual equations. -/
theorem released_check : payloadCheck chunk = true := by
  native_decide

/-- Closed Boolean certificate for the first row block. -/
def verified : VerifiedBy Chunk PayloadSpec where
  payload := chunk
  check := payloadCheck
  sound := payloadCheck_sound
  checked := released_check

theorem certified : PayloadSpec chunk :=
  VerifiedBy.proof verified

end EmbeddedTrelChunk0
end Closed
end KnuthFasc8AEx210
