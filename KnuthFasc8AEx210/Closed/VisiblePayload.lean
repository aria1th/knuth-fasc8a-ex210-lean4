import KnuthFasc8AEx210.Closed.BooleanCertificate
import KnuthFasc8AEx210.Closed.EmbeddedVisible

namespace KnuthFasc8AEx210
namespace Closed
namespace VisiblePayload

open Formats EmbeddedVisible

/-!
# Closed metadata certificate for the visible-factor payloads

This is the first concrete use of `VerifiedBy` in the closed-certificate path.
It packages the two parsed release files together with all format and metadata
facts consumed by the visible-factor verifier.

The result is deliberately weaker than the eventual spectral certificate: it
establishes that Lean itself decoded the canonical bytes, parsed the intended
formats, and checked the released dimensions and pivot.  A later layer adds the
sparse-matrix residual and reachability computations.
-/

/-- The two concrete visible-factor payloads after Lean parsing. -/
structure Payload where
  polynomial : KMP101
  eigenvector : KMV101
  deriving DecidableEq, Repr, Inhabited

/-- Mathematical specification of the released visible-factor payload metadata. -/
def Spec (p : Payload) : Prop :=
  p.polynomial.valid = true ∧
  p.polynomial.coeffs.length = 4107 ∧
  p.eigenvector.valid = true ∧
  p.eigenvector.dimension = 16831 ∧
  p.eigenvector.pivot = 0 ∧
  p.eigenvector.entries.getD p.eigenvector.pivot 0 = 37

/-- Executable checker corresponding exactly to `Spec`. -/
def check (p : Payload) : Bool :=
  p.polynomial.valid &&
  (p.polynomial.coeffs.length == 4107) &&
  p.eigenvector.valid &&
  (p.eigenvector.dimension == 16831) &&
  (p.eigenvector.pivot == 0) &&
  (p.eigenvector.entries.getD p.eigenvector.pivot 0 == 37)

/-- Soundness of the executable metadata checker. -/
theorem check_sound (p : Payload) (h : check p = true) : Spec p := by
  simpa [check, Spec, Bool.and_eq_true] using h

/-- The payload decoded and parsed from the canonical checked-in hexadecimal files. -/
def released : Payload where
  polynomial := visible76
  eigenvector := eigen50

/-- The released payload passes the executable checker inside Lean. -/
theorem released_check : check released = true := by
  native_decide

/-- A fully closed Boolean certificate for the visible payload metadata. -/
def verified : VerifiedBy Payload Spec where
  payload := released
  check := check
  sound := check_sound
  checked := released_check

/-- Bundled metadata facts extracted from the closed certificate. -/
theorem released_spec : Spec released :=
  VerifiedBy.proof verified

/-- The polynomial component of the bundled payload is the parsed release file. -/
theorem released_polynomial : released.polynomial = visible76 := rfl

/-- The eigenvector component of the bundled payload is the parsed release file. -/
theorem released_eigenvector : released.eigenvector = eigen50 := rfl

end VisiblePayload
end Closed
end KnuthFasc8AEx210
