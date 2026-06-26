import KnuthFasc8AEx210.Closed.ResidualCoverage
import KnuthFasc8AEx210.Closed.Generated.TrelChunk00
import KnuthFasc8AEx210.Closed.Generated.TrelChunk01
import KnuthFasc8AEx210.Closed.Generated.TrelChunk02
import KnuthFasc8AEx210.Closed.Generated.TrelChunk03
import KnuthFasc8AEx210.Closed.Generated.TrelChunk04
import KnuthFasc8AEx210.Closed.Generated.TrelChunk05
import KnuthFasc8AEx210.Closed.Generated.TrelChunk06
import KnuthFasc8AEx210.Closed.Generated.TrelChunk07
import KnuthFasc8AEx210.Closed.Generated.TrelChunk08
import KnuthFasc8AEx210.Closed.Generated.TrelChunk09
import KnuthFasc8AEx210.Closed.Generated.TrelChunk10
import KnuthFasc8AEx210.Closed.Generated.TrelChunk11
import KnuthFasc8AEx210.Closed.Generated.TrelChunk12
import KnuthFasc8AEx210.Closed.Generated.TrelChunk13
import KnuthFasc8AEx210.Closed.Generated.TrelChunk14
import KnuthFasc8AEx210.Closed.Generated.TrelChunk15
import KnuthFasc8AEx210.Closed.Generated.TrelChunk16

namespace KnuthFasc8AEx210
namespace Closed
namespace Generated
namespace TrelResidual

/-- Semantic certificate for every released `Trel+` residual row. -/
structure Certificate : Prop where
  coverage : ResidualCoverage.covers 16831 ResidualCoverage.trelRanges = true
  chunk00 : TrelChunk00.PayloadSpec TrelChunk00.chunk
  chunk01 : TrelChunk01.PayloadSpec TrelChunk01.chunk
  chunk02 : TrelChunk02.PayloadSpec TrelChunk02.chunk
  chunk03 : TrelChunk03.PayloadSpec TrelChunk03.chunk
  chunk04 : TrelChunk04.PayloadSpec TrelChunk04.chunk
  chunk05 : TrelChunk05.PayloadSpec TrelChunk05.chunk
  chunk06 : TrelChunk06.PayloadSpec TrelChunk06.chunk
  chunk07 : TrelChunk07.PayloadSpec TrelChunk07.chunk
  chunk08 : TrelChunk08.PayloadSpec TrelChunk08.chunk
  chunk09 : TrelChunk09.PayloadSpec TrelChunk09.chunk
  chunk10 : TrelChunk10.PayloadSpec TrelChunk10.chunk
  chunk11 : TrelChunk11.PayloadSpec TrelChunk11.chunk
  chunk12 : TrelChunk12.PayloadSpec TrelChunk12.chunk
  chunk13 : TrelChunk13.PayloadSpec TrelChunk13.chunk
  chunk14 : TrelChunk14.PayloadSpec TrelChunk14.chunk
  chunk15 : TrelChunk15.PayloadSpec TrelChunk15.chunk
  chunk16 : TrelChunk16.PayloadSpec TrelChunk16.chunk

/-- All 17 semantic row-block certificates cover all 16,831 rows exactly once. -/
theorem released : Certificate where
  coverage := ResidualCoverage.trelRanges_cover
  chunk00 := TrelChunk00.certified
  chunk01 := TrelChunk01.certified
  chunk02 := TrelChunk02.certified
  chunk03 := TrelChunk03.certified
  chunk04 := TrelChunk04.certified
  chunk05 := TrelChunk05.certified
  chunk06 := TrelChunk06.certified
  chunk07 := TrelChunk07.certified
  chunk08 := TrelChunk08.certified
  chunk09 := TrelChunk09.certified
  chunk10 := TrelChunk10.certified
  chunk11 := TrelChunk11.certified
  chunk12 := TrelChunk12.certified
  chunk13 := TrelChunk13.certified
  chunk14 := TrelChunk14.certified
  chunk15 := TrelChunk15.certified
  chunk16 := TrelChunk16.certified

end TrelResidual
end Generated
end Closed
end KnuthFasc8AEx210
