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

def eigenvector : ByteArray :=
  ⟨eigen50.entries.toArray.map (fun value => UInt8.ofNat value)⟩

/-- One native computation checks metadata and all 1,024 residual equations. -/
def checkReleased : Bool :=
  (chunk.dimension == 16831) &&
  ((chunk.startRow == 0) &&
    ((chunk.rowCount == 1024) &&
      ResidualChunk.check chunk 50 eigenvector))

theorem released_spec : checkReleased = true := by
  native_decide

theorem dimension_ok : chunk.dimension = 16831 := by
  have h := (Bool.and_eq_true.mp released_spec).1
  simpa using h

theorem start_row_ok : chunk.startRow = 0 := by
  have h := (Bool.and_eq_true.mp released_spec).2
  have h := (Bool.and_eq_true.mp h).1
  simpa using h

theorem row_count_ok : chunk.rowCount = 1024 := by
  have h := (Bool.and_eq_true.mp released_spec).2
  have h := (Bool.and_eq_true.mp h).2
  have h := (Bool.and_eq_true.mp h).1
  simpa using h

/-- The first 1,024 released residual equations are checked by Lean. -/
theorem released_check : ResidualChunk.check chunk 50 eigenvector = true := by
  have h := (Bool.and_eq_true.mp released_spec).2
  have h := (Bool.and_eq_true.mp h).2
  exact (Bool.and_eq_true.mp h).2

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
