import KnuthFasc8AEx210.Closed.FastHex
import KnuthFasc8AEx210.Closed.FastSparseMatrix
import KnuthFasc8AEx210.Closed.EmbeddedVisible

namespace KnuthFasc8AEx210
namespace Closed
namespace EmbeddedTrel

open FastSparseMatrix EmbeddedVisible

/-!
# Closed residual check for the released `Trel+` eigenvector

The 2.88 MB `KMC201` block is embedded as canonical hexadecimal text, decoded,
parsed and multiplied by the released vector inside Lean.
-/

/-- Canonical hexadecimal representation of `data/blocks/Trel_plus.kmc`. -/
def matrixHex : String :=
  include_str ".." / ".." / "data" / "lean" / "Trel_plus.kmc.hex"

/-- Packed matrix bytes decoded by Lean. -/
def matrixBytes : ByteArray :=
  (FastHex.decode? matrixHex).getD ByteArray.empty

/-- The parsed released matrix; parse failure yields the invalid default matrix. -/
def matrix : KMC201 :=
  (parseKMC201? matrixBytes).getD default

/-- The parsed `KMV101` payload converted to the packed vector representation. -/
def eigenvector : ByteArray :=
  ⟨eigen50.entries.toArray.map (fun n => UInt8.ofNat n)⟩

/-- Combined closed specification checked by one native computation. -/
def ReleasedSpec : Prop :=
  FastHex.decode? matrixHex = some matrixBytes ∧
  parseKMC201? matrixBytes = some matrix ∧
  matrix.dimension = 16831 ∧
  matrix.prime = 101 ∧
  eigenvector.size = 16831 ∧
  checkEigenMod101 matrix 50 eigenvector = true

/-- Lean decodes the matrix and verifies the complete eigenvector residual. -/
theorem released_spec : ReleasedSpec := by
  native_decide

/-- Proposition-level residual certificate extracted from the closed checker. -/
theorem eigen_spec : EigenSpec matrix 50 eigenvector :=
  checkEigenMod101_sound matrix 50 eigenvector released_spec.2.2.2.2.2

/-- The released pivot remains nonzero in the packed representation. -/
theorem eigenvector_pivot_nonzero : eigenvector.data[0]! = 37 := by
  native_decide

/-- The embedded matrix size agrees with the release manifest. -/
theorem matrix_file_size : matrixBytes.size = 2880301 := by
  native_decide

end EmbeddedTrel
end Closed
end KnuthFasc8AEx210
