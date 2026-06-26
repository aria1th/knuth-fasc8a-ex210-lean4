import KnuthFasc8AEx210.Closed.BooleanCertificate
import KnuthFasc8AEx210.Closed.FastHex
import KnuthFasc8AEx210.Closed.ResidualChunk
import KnuthFasc8AEx210.Closed.EmbeddedVisible

namespace KnuthFasc8AEx210
namespace Closed
namespace Generated
namespace TrelChunk10

open ResidualChunk EmbeddedVisible

def chunkHex : String :=
  include_str ".." / ".." / ".." / "data" / "lean" / "trel_residual" /
    "Trel_plus.rows.10240.01024.krc.hex"

def chunkBytes : ByteArray :=
  (FastHex.decode? chunkHex).getD ByteArray.empty

def chunk : Chunk :=
  (parseChunk? chunkBytes).getD default

def payloadCheck (c : Chunk) : Bool :=
  (c.dimension == 16831) &&
  ((c.startRow == 10240) &&
    ((c.rowCount == 1024) &&
      ResidualChunk.check c 50 eigen50Packed))

structure PayloadSpec (c : Chunk) : Prop where
  dimension : c.dimension = 16831
  startRow : c.startRow = 10240
  rowCount : c.rowCount = 1024
  residual : ResidualChunk.Spec c 50 eigen50Packed

theorem payloadCheck_sound (c : Chunk) (h : payloadCheck c = true) : PayloadSpec c := by
  have parts :
      c.dimension = 16831 ∧
        (c.startRow = 10240 ∧
          (c.rowCount = 1024 ∧
            ResidualChunk.check c 50 eigen50Packed = true)) := by
    simpa [payloadCheck, Bool.and_eq_true] using h
  exact
    { dimension := parts.1
      startRow := parts.2.1
      rowCount := parts.2.2.1
      residual := ResidualChunk.check_sound c 50 eigen50Packed parts.2.2.2 }

theorem released_check : payloadCheck chunk = true := by
  native_decide

def verified : VerifiedBy Chunk PayloadSpec where
  payload := chunk
  check := payloadCheck
  sound := payloadCheck_sound
  checked := released_check

theorem certified : PayloadSpec chunk :=
  VerifiedBy.proof verified

end TrelChunk10
end Generated
end Closed
end KnuthFasc8AEx210
