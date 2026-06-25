import Mathlib

namespace KnuthFasc8AEx210
namespace Closed

/-!
# Boolean certificate wrapper

This module is the PR3 bridge from external proposition interfaces to a fully
closed Lean proof.  The intended pattern is:

1. define a concrete payload type for a checked-in certificate;
2. define an executable Boolean checker for that payload;
3. prove the checker sound;
4. evaluate the checker on the concrete payload inside Lean.

A final closed proof should use `VerifiedBy.proof`, not a free-standing
proposition interface.
-/

/-- A Boolean checker, a concrete payload, a soundness theorem, and a checked run. -/
structure VerifiedBy (α : Type u) (P : α → Prop) where
  payload : α
  check : α → Bool
  sound : ∀ a, check a = true → P a
  checked : check payload = true

namespace VerifiedBy

/-- Extract the certified proposition from a verified Boolean certificate. -/
theorem proof {α : Type u} {P : α → Prop} (v : VerifiedBy α P) : P v.payload :=
  v.sound v.payload v.checked

/-- Transport a verified certificate across a logical implication. -/
def map {α : Type u} {P Q : α → Prop} (v : VerifiedBy α P)
    (h : ∀ a, P a → Q a) : VerifiedBy α Q where
  payload := v.payload
  check := v.check
  sound := fun a ha => h a (v.sound a ha)
  checked := v.checked

end VerifiedBy

end Closed
end KnuthFasc8AEx210
