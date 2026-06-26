import KnuthFasc8AEx210.Closed.ResidualCoverage
import KnuthFasc8AEx210.Closed.Generated.TrelResidual

namespace KnuthFasc8AEx210
namespace Closed
namespace TrelResidualCertificate

/-!
# Semantic wrapper for the generated `Trel+` residual certificates

The generated module proves each row-block residual certificate.  The coverage
module proves that the row-block intervals cover all `16,831` rows exactly once.
This file packages both facts into one semantic certificate that can be used by
later bridge lemmas.
-/

/-- The current Lean-checked content of the released `Trel+` residual certificate. -/
structure Certificate : Prop where
  coverage : ResidualCoverage.TrelCoverageSpec ResidualCoverage.trelRanges
  rowBlocks : Generated.TrelResidual.Certificate

/-- The released row-block residual certificate, checked by Lean. -/
theorem released : Certificate where
  coverage := ResidualCoverage.trelCoverageSpec
  rowBlocks := Generated.TrelResidual.released

/-- Convenience projection: the generated row-block certificates are available. -/
theorem released_rowBlocks : Generated.TrelResidual.Certificate :=
  released.rowBlocks

/-- Convenience projection: the row-block coverage proof is semantic, not only Boolean. -/
theorem released_coverage : ResidualCoverage.TrelCoverageSpec ResidualCoverage.trelRanges :=
  released.coverage

end TrelResidualCertificate
end Closed
end KnuthFasc8AEx210
