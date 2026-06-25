import KnuthFasc8AEx210.SourceRepository
import KnuthFasc8AEx210.Closed.BooleanCertificate

open Polynomial

namespace KnuthFasc8AEx210
namespace Closed

noncomputable section

/-!
# Closed counterexample target

`SourceRepositoryCertificate.counterexample` is currently conditional on a
proposition-level certificate.  PR3 aims to replace that free proposition by a
concrete Lean-checked Boolean certificate.

The theorem in this file is the exact hand-off shape for that replacement:
once a concrete parser/checker returns a `VerifiedBy` witness for
`SourceRepositoryCertificate`, the final nondivisibility theorem is closed with
no further mathematical assumptions.
-/

/--
A checked Boolean source certificate discharges the current proposition-level
interface and yields the width-five nondivisibility theorem.
-/
theorem counterexample_of_verified_source_certificate
    {Payload : Type u} {Q5 Q5Open Delta : ℤ[X]}
    (v : VerifiedBy Payload (fun _ => SourceRepositoryCertificate Q5 Q5Open Delta)) :
    ¬(Q5.map (Int.castRingHom ℚ)) ^ 3 ∣ Q5Open.map (Int.castRingHom ℚ) := by
  exact SourceRepositoryCertificate.counterexample v.proof

/--
The first closed-certification milestone: construct the source-repository
certificate from a concrete Lean payload and an executable checker.

A later PR3 commit should instantiate `Payload` with parsed or generated data
for `visible76.poly`, `Trel_plus_eigen50.vec`, the `.kmc` blocks, and the
`.kwc2` rank certificates, then prove the checker sound.
-/
abbrev ClosedCertificateMilestone (Payload : Type u)
    (Q5 Q5Open Delta : ℤ[X]) : Prop :=
  Nonempty (VerifiedBy Payload (fun _ => SourceRepositoryCertificate Q5 Q5Open Delta))

end

end Closed
end KnuthFasc8AEx210
