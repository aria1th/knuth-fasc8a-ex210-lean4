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
self-contained `KRC101` row-block payload.  Further generated modules will use
the same checker for the remaining contiguous blocks.
-/

/-- Canonical row-block payload produced from `Trel_plus.kmc`. -/
def chunkHex : String :=
  include_str ".." / ".." / "data" / "lean" / "trel_residual" /
    "Trel_plus.rows.00000.01024.krc.hex"

/-- Packed bytes decoded inside Lean. -/
def chunkBytes : ByteArray :=
  (FastHex.decode? chunkHex).getD ByteArray.empty

/-- Parsed row block; parse failure gives an invalid default block. -/
def chunk : Chunk :=
  (parseChunk? chunkBytes).getD default

/-- Released eigenvector in the packed representation consumed by the checker. -/
def eigenvector : ByteArray :=
  ⟨eigen50.entries.toArray.map (fun value => UInt8.ofNat value)⟩

theorem decode_ok : FastHex.decode? chunkHex = some chunkBytes := by
  native_decide

theorem parse_ok : parseChunk? chunkBytes = some chunk := by
  native_decide

theorem dimension_ok : chunk.dimension = 16831 := by
  native_decide

theorem start_row_ok : chunk.startRow = 0 := by
  native_decide

theorem row_count_ok : chunk.rowCount = 1024 := by
  native_decide

/-- The first 1,024 released residual equations are checked by Lean. -/
theorem released_check : ResidualChunk.check chunk 50 eigenvector = true := by
  native_decide

/-- Closed Boolean certificate for the first row block. -/
def verified : VerifiedBy Chunk (fun c => ResidualChunk.Spec c 50 eigenvector) where
  payload := chunk
  check := fun c => ResidualChunk.check c 50 eigenvector
  sound := fun c h => ResidualChunk.check_sound c 50 eigenvector h
  checked := released_check

theorem certified : ResidualChunk.Spec chunk 50 eigenvector :=
  VerifiedBy.proof verified

end EmbeddedTrelChunk0
end Closed
end KnuthFasc8AEx210
