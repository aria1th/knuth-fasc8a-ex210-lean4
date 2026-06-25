import KnuthFasc8AEx210.CertificateInterfaces

open Polynomial

namespace KnuthFasc8AEx210

/-!
# The exact interface to `kylekaba/knuth-fasc8a-ex210`

The source repository proves the following five groups of claims:

* primitive constant-term-one denominators `Q₅` and `Q₅⁺`;
* `Q₅⁺ ∣ Delta`, where `Delta` is the block transfer determinant;
* visibility of `1 - 50z` in `Q₅` modulo `101`;
* simple occurrence in the `T` and `Wrel` sectors;
* absence from the `U` sector.

The binary files and C++ verifiers named in the field comments establish these
claims externally. This structure is the precise hand-off point for a future
kernel-integrated Lean certificate reader.
-/

/-- Mathematical data and claims exported by the checked-in width-five certificates. -/
structure SourceRepositoryCertificate (Q5 Q5Open Delta : ℤ[X]) where
  /-- Normalization of the reduced closed denominator. -/
  closed_constant : Q5.coeff 0 = 1
  /-- Normalization of the reduced open denominator. -/
  open_constant : Q5Open.coeff 0 = 1
  /-- Transfer decomposition and reduced-denominator lemma. -/
  open_dvd_transferDet : Q5Open ∣ Delta
  /-- `data/certs/visible76.poly` and `src/verify_visible.cpp`. -/
  visible_factor : paperFactor ∣ mod101 Q5
  /-- Determinant of the relevant closed sector `Trel`. -/
  closedSector : F101[X]
  /-- Product of the relevant one-endpoint sectors `U1` and `U2`. -/
  oneEndpointSector : F101[X]
  /-- Determinant of `Wrel`, permutation-similar to `Trel`. -/
  completedSector : F101[X]
  /-- Block triangularity and the checked `Wrel ≃ Trel` identification. -/
  transferDet_mod101 :
    mod101 Delta = closedSector * oneEndpointSector * completedSector
  /-- Border certificate `Trel_plus_border.kwc2` plus the minus-block certificate. -/
  closed_simple : SimpleRootAt (99 : F101) closedSector
  /-- The four `U1/U2` plus/minus shift certificates. -/
  oneEndpoint_regular : NonRootAt (99 : F101) oneEndpointSector
  /-- The checked permutation similarity `Wrel ≃ Trel`. -/
  completed_simple : SimpleRootAt (99 : F101) completedSector

namespace SourceRepositoryCertificate

/-- Convert source-repository claims into the generic three-sector capacity interface. -/
def capacity {Q5 Q5Open Delta : ℤ[X]}
    (c : SourceRepositoryCertificate Q5 Q5Open Delta) :
    PaperThreeSectorCapacity Delta where
  left := c.closedSector
  middle := c.oneEndpointSector
  right := c.completedSector
  delta_eq := c.transferDet_mod101
  left_simple := c.closed_simple
  middle_regular := c.oneEndpoint_regular
  right_simple := c.completed_simple

/--
Once the source repository's checked claims are imported as propositions, the
counterexample is a short theorem with no matrix computation in its proof.
-/
theorem counterexample {Q5 Q5Open Delta : ℤ[X]}
    (c : SourceRepositoryCertificate Q5 Q5Open Delta) :
    ¬(Q5.map (Int.castRingHom ℚ)) ^ 3 ∣ Q5Open.map (Int.castRingHom ℚ) := by
  exact widthFive_counterexample_of_three_sector_capacity
    c.closed_constant c.open_constant c.open_dvd_transferDet c.visible_factor c.capacity

end SourceRepositoryCertificate

end KnuthFasc8AEx210
