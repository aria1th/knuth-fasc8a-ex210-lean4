import KnuthFasc8AEx210.Closed.BooleanCertificate
import KnuthFasc8AEx210.Closed.FastHex
import KnuthFasc8AEx210.Closed.ResidualChunk
import KnuthFasc8AEx210.Closed.EmbeddedVisible

namespace KnuthFasc8AEx210
namespace Closed
namespace Generated
namespace TrelChunk07

open ResidualChunk EmbeddedVisible

def chunkHex : String :=
  include_str ".." / ".." / ".." / "data" / "lean" / "trel_residual" /
    "Trel_plus.rows.07168.01024.krc.hex"

def chunkBytes : ByteArray :=
  (FastHex.decode? chunkHex).getD ByteArray.empty

def chunk : Chunk :=
  (parseChunk? chunkBytes).getD default

def payloadCheck (c : Chunk) : Bool :=
  (c.dimension == 16831) &&
  (c.startRow == 7168) &&
  (c.rowCount == 1024) &&
  ResidualChunk.check c 50 eigen50Packed

def PayloadSpec (c : Chunk) : Prop :=
  payloadCheck c = true

theorem payloadCheck_sound (c : Chunk) (h : payloadCheck c = true) : PayloadSpec c := h

theorem released_check : payloadCheck chunk = true := by
  native_decide

def verified : VerifiedBy Chunk PayloadSpec where
  payload := chunk
  check := payloadCheck
  sound := payloadCheck_sound
  checked := released_check

theorem certified : PayloadSpec chunk :=
  VerifiedBy.proof verified

end TrelChunk07
end Generated
end Closed
end KnuthFasc8AEx210
