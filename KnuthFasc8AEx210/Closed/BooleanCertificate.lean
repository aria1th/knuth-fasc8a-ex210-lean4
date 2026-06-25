import Mathlib

namespace KnuthFasc8AEx210
namespace Closed

universe u v

/-!
# Boolean certificate wrapper

This module is the PR3 bridge from external proposition interfaces to a fully
closed Lean proof.  The intended pattern is:

1. define a concrete payload type for a checked-in certificate;
2. define an executable Boolean checker for that payload;
3. prove the checker sound;
4. evaluate the checker on the concrete payload inside Lean.

The certified object may live in `Prop` or in `Type`: for example,
`SourceRepositoryCertificate` contains concrete polynomial data, so it is a
`Type`, not merely a proposition.
-/

/-- A Boolean checker, a concrete payload, a soundness theorem, and a checked run. -/
structure VerifiedBy (α : Type u) (P : α → Sort v) where
  payload : α
  check : α → Bool
  sound : ∀ a, check a = true → P a
  checked : check payload = true

namespace VerifiedBy

/-- Extract the certified object from a verified Boolean certificate. -/
def proof {α : Type u} {P : α → Sort v} (cert : VerifiedBy α P) : P cert.payload :=
  cert.sound cert.payload cert.checked

/-- Transport a verified certificate across an implication or construction. -/
def map {α : Type u} {P Q : α → Sort v} (cert : VerifiedBy α P)
    (h : ∀ a, P a → Q a) : VerifiedBy α Q where
  payload := cert.payload
  check := cert.check
  sound := fun a ha => h a (cert.sound a ha)
  checked := cert.checked

end VerifiedBy

end Closed
end KnuthFasc8AEx210
