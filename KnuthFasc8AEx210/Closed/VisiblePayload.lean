import KnuthFasc8AEx210.Closed.BooleanCertificate
import KnuthFasc8AEx210.Closed.EmbeddedVisible

namespace KnuthFasc8AEx210
namespace Closed
namespace VisiblePayload

open Formats EmbeddedVisible

/-!
# Closed metadata certificate for the visible-factor payloads

This packages the polynomial, restricted eigenvector, and terminal vector that
Lean decoded from the canonical checked-in hexadecimal data.
-/

structure Payload where
  polynomial : KMP101
  eigenvector : KMV101
  finishVector : FinishVector
  deriving DecidableEq, Repr, Inhabited

/-- The conjunction is left-associated to match `Bool.and_eq_true`. -/
def Spec (p : Payload) : Prop :=
  (((((((p.polynomial.valid = true ∧
    p.polynomial.coeffs.length = 4107) ∧
    p.eigenvector.valid = true) ∧
    p.eigenvector.dimension = 16831) ∧
    p.eigenvector.pivot = 0) ∧
    p.eigenvector.entries.getD p.eigenvector.pivot 0 = 37) ∧
    p.finishVector.valid = true) ∧
    p.finishVector.dimension = 18325)

def check (p : Payload) : Bool :=
  p.polynomial.valid &&
  (p.polynomial.coeffs.length == 4107) &&
  p.eigenvector.valid &&
  (p.eigenvector.dimension == 16831) &&
  (p.eigenvector.pivot == 0) &&
  (p.eigenvector.entries.getD p.eigenvector.pivot 0 == 37) &&
  p.finishVector.valid &&
  (p.finishVector.dimension == 18325)

theorem check_sound (p : Payload) (h : check p = true) : Spec p := by
  simpa [check, Spec, Bool.and_eq_true] using h

def released : Payload where
  polynomial := visible76
  eigenvector := eigen50
  finishVector := finish

theorem released_check : check released = true := by
  native_decide

def verified : VerifiedBy Payload Spec where
  payload := released
  check := check
  sound := check_sound
  checked := released_check

theorem released_spec : Spec released :=
  VerifiedBy.proof verified

theorem released_polynomial : released.polynomial = visible76 := rfl

theorem released_eigenvector : released.eigenvector = eigen50 := rfl

theorem released_finishVector : released.finishVector = finish := rfl

end VisiblePayload
end Closed
end KnuthFasc8AEx210
