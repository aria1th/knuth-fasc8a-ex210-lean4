import KnuthFasc8AEx210.Closed.ResidualBridge
import KnuthFasc8AEx210.Closed.TrelResidualCertificate

namespace KnuthFasc8AEx210
namespace Closed
namespace TrelResidualRows

/-!
# Global row witnesses for the released `Trel+` residual

`TrelResidualCertificate.released` packages the generated row-block certificates
and the coverage theorem.  This file projects every generated local residual
certificate into global row witnesses for rows `startRow + localRow`.
-/

open ResidualBridge

/--
For every local row in each released chunk, Lean can produce a corresponding
global residual-row witness.
-/
structure GlobalWitnesses : Prop where
  chunk00 : ∀ localRow, localRow < Generated.TrelChunk00.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk00.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk00.chunk.startRow + localRow)
  chunk01 : ∀ localRow, localRow < Generated.TrelChunk01.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk01.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk01.chunk.startRow + localRow)
  chunk02 : ∀ localRow, localRow < Generated.TrelChunk02.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk02.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk02.chunk.startRow + localRow)
  chunk03 : ∀ localRow, localRow < Generated.TrelChunk03.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk03.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk03.chunk.startRow + localRow)
  chunk04 : ∀ localRow, localRow < Generated.TrelChunk04.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk04.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk04.chunk.startRow + localRow)
  chunk05 : ∀ localRow, localRow < Generated.TrelChunk05.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk05.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk05.chunk.startRow + localRow)
  chunk06 : ∀ localRow, localRow < Generated.TrelChunk06.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk06.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk06.chunk.startRow + localRow)
  chunk07 : ∀ localRow, localRow < Generated.TrelChunk07.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk07.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk07.chunk.startRow + localRow)
  chunk08 : ∀ localRow, localRow < Generated.TrelChunk08.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk08.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk08.chunk.startRow + localRow)
  chunk09 : ∀ localRow, localRow < Generated.TrelChunk09.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk09.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk09.chunk.startRow + localRow)
  chunk10 : ∀ localRow, localRow < Generated.TrelChunk10.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk10.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk10.chunk.startRow + localRow)
  chunk11 : ∀ localRow, localRow < Generated.TrelChunk11.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk11.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk11.chunk.startRow + localRow)
  chunk12 : ∀ localRow, localRow < Generated.TrelChunk12.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk12.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk12.chunk.startRow + localRow)
  chunk13 : ∀ localRow, localRow < Generated.TrelChunk13.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk13.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk13.chunk.startRow + localRow)
  chunk14 : ∀ localRow, localRow < Generated.TrelChunk14.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk14.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk14.chunk.startRow + localRow)
  chunk15 : ∀ localRow, localRow < Generated.TrelChunk15.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk15.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk15.chunk.startRow + localRow)
  chunk16 : ∀ localRow, localRow < Generated.TrelChunk16.chunk.rowCount →
    GlobalRowWitness Generated.TrelChunk16.chunk 50 EmbeddedVisible.eigen50Packed
      (Generated.TrelChunk16.chunk.startRow + localRow)

/-- All generated local row certificates are available as global row witnesses. -/
theorem released : GlobalWitnesses where
  chunk00 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk00.certified.residual hlocal
  chunk01 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk01.certified.residual hlocal
  chunk02 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk02.certified.residual hlocal
  chunk03 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk03.certified.residual hlocal
  chunk04 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk04.certified.residual hlocal
  chunk05 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk05.certified.residual hlocal
  chunk06 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk06.certified.residual hlocal
  chunk07 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk07.certified.residual hlocal
  chunk08 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk08.certified.residual hlocal
  chunk09 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk09.certified.residual hlocal
  chunk10 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk10.certified.residual hlocal
  chunk11 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk11.certified.residual hlocal
  chunk12 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk12.certified.residual hlocal
  chunk13 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk13.certified.residual hlocal
  chunk14 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk14.certified.residual hlocal
  chunk15 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk15.certified.residual hlocal
  chunk16 := fun localRow hlocal =>
    globalWitness_of_local Generated.TrelChunk16.certified.residual hlocal

end TrelResidualRows
end Closed
end KnuthFasc8AEx210
