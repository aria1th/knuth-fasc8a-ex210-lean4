import Mathlib
import KnuthFasc8AEx210.Closed.ResidualBridge
import KnuthFasc8AEx210.Closed.TrelResidualCertificate

namespace KnuthFasc8AEx210
namespace Closed
namespace TrelResidualRows

/-!
# Global row witnesses for the released `Trel+` residual

`TrelResidualCertificate.released` packages the generated row-block certificates
and the coverage theorem. This file projects every generated local residual
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

/-- Some released chunk witnesses the residual equation for a global row. -/
def SomeGlobalWitness (globalRow : Nat) : Prop :=
  ∃ c : ResidualChunk.Chunk,
    GlobalRowWitness c 50 EmbeddedVisible.eigen50Packed globalRow

/-- A certified interval supplies global row witnesses for all rows inside it. -/
theorem someGlobalWitness_of_interval {c : ResidualChunk.Chunk} {start count row : Nat}
    (hres : ResidualChunk.Spec c 50 EmbeddedVisible.eigen50Packed)
    (hstart : c.startRow = start) (hcount : c.rowCount = count)
    (hlo : start ≤ row) (hhi : row < start + count) : SomeGlobalWitness row := by
  let localRow := row - start
  refine ⟨c, globalWitness_of_local_eq hres (localRow := localRow) ?_ ?_⟩
  · rw [hcount]
    omega
  · rw [hstart]
    dsimp [localRow]
    omega

/-- Every global row of the released `Trel+` block has a row-block residual witness. -/
theorem someGlobalWitness_of_lt_16831 (row : Nat) (hrow : row < 16831) :
    SomeGlobalWitness row := by
  by_cases h00 : row < 1024
  · exact someGlobalWitness_of_interval
      (c := Generated.TrelChunk00.chunk) (start := 0) (count := 1024) (row := row)
      Generated.TrelChunk00.certified.residual
      Generated.TrelChunk00.certified.startRow Generated.TrelChunk00.certified.rowCount
      (by omega) (by omega)
  · by_cases h01 : row < 2048
    · exact someGlobalWitness_of_interval
        (c := Generated.TrelChunk01.chunk) (start := 1024) (count := 1024) (row := row)
        Generated.TrelChunk01.certified.residual
        Generated.TrelChunk01.certified.startRow Generated.TrelChunk01.certified.rowCount
        (by omega) (by omega)
    · by_cases h02 : row < 3072
      · exact someGlobalWitness_of_interval
          (c := Generated.TrelChunk02.chunk) (start := 2048) (count := 1024) (row := row)
          Generated.TrelChunk02.certified.residual
          Generated.TrelChunk02.certified.startRow Generated.TrelChunk02.certified.rowCount
          (by omega) (by omega)
      · by_cases h03 : row < 4096
        · exact someGlobalWitness_of_interval
            (c := Generated.TrelChunk03.chunk) (start := 3072) (count := 1024) (row := row)
            Generated.TrelChunk03.certified.residual
            Generated.TrelChunk03.certified.startRow Generated.TrelChunk03.certified.rowCount
            (by omega) (by omega)
        · by_cases h04 : row < 5120
          · exact someGlobalWitness_of_interval
              (c := Generated.TrelChunk04.chunk) (start := 4096) (count := 1024) (row := row)
              Generated.TrelChunk04.certified.residual
              Generated.TrelChunk04.certified.startRow Generated.TrelChunk04.certified.rowCount
              (by omega) (by omega)
          · by_cases h05 : row < 6144
            · exact someGlobalWitness_of_interval
                (c := Generated.TrelChunk05.chunk) (start := 5120) (count := 1024) (row := row)
                Generated.TrelChunk05.certified.residual
                Generated.TrelChunk05.certified.startRow Generated.TrelChunk05.certified.rowCount
                (by omega) (by omega)
            · by_cases h06 : row < 7168
              · exact someGlobalWitness_of_interval
                  (c := Generated.TrelChunk06.chunk) (start := 6144) (count := 1024) (row := row)
                  Generated.TrelChunk06.certified.residual
                  Generated.TrelChunk06.certified.startRow Generated.TrelChunk06.certified.rowCount
                  (by omega) (by omega)
              · by_cases h07 : row < 8192
                · exact someGlobalWitness_of_interval
                    (c := Generated.TrelChunk07.chunk) (start := 7168) (count := 1024) (row := row)
                    Generated.TrelChunk07.certified.residual
                    Generated.TrelChunk07.certified.startRow Generated.TrelChunk07.certified.rowCount
                    (by omega) (by omega)
                · by_cases h08 : row < 9216
                  · exact someGlobalWitness_of_interval
                      (c := Generated.TrelChunk08.chunk) (start := 8192) (count := 1024) (row := row)
                      Generated.TrelChunk08.certified.residual
                      Generated.TrelChunk08.certified.startRow Generated.TrelChunk08.certified.rowCount
                      (by omega) (by omega)
                  · by_cases h09 : row < 10240
                    · exact someGlobalWitness_of_interval
                        (c := Generated.TrelChunk09.chunk) (start := 9216) (count := 1024) (row := row)
                        Generated.TrelChunk09.certified.residual
                        Generated.TrelChunk09.certified.startRow Generated.TrelChunk09.certified.rowCount
                        (by omega) (by omega)
                    · by_cases h10 : row < 11264
                      · exact someGlobalWitness_of_interval
                          (c := Generated.TrelChunk10.chunk) (start := 10240) (count := 1024) (row := row)
                          Generated.TrelChunk10.certified.residual
                          Generated.TrelChunk10.certified.startRow Generated.TrelChunk10.certified.rowCount
                          (by omega) (by omega)
                      · by_cases h11 : row < 12288
                        · exact someGlobalWitness_of_interval
                            (c := Generated.TrelChunk11.chunk) (start := 11264) (count := 1024) (row := row)
                            Generated.TrelChunk11.certified.residual
                            Generated.TrelChunk11.certified.startRow Generated.TrelChunk11.certified.rowCount
                            (by omega) (by omega)
                        · by_cases h12 : row < 13312
                          · exact someGlobalWitness_of_interval
                              (c := Generated.TrelChunk12.chunk) (start := 12288) (count := 1024) (row := row)
                              Generated.TrelChunk12.certified.residual
                              Generated.TrelChunk12.certified.startRow Generated.TrelChunk12.certified.rowCount
                              (by omega) (by omega)
                          · by_cases h13 : row < 14336
                            · exact someGlobalWitness_of_interval
                                (c := Generated.TrelChunk13.chunk) (start := 13312) (count := 1024) (row := row)
                                Generated.TrelChunk13.certified.residual
                                Generated.TrelChunk13.certified.startRow Generated.TrelChunk13.certified.rowCount
                                (by omega) (by omega)
                            · by_cases h14 : row < 15360
                              · exact someGlobalWitness_of_interval
                                  (c := Generated.TrelChunk14.chunk) (start := 14336) (count := 1024) (row := row)
                                  Generated.TrelChunk14.certified.residual
                                  Generated.TrelChunk14.certified.startRow Generated.TrelChunk14.certified.rowCount
                                  (by omega) (by omega)
                              · by_cases h15 : row < 16384
                                · exact someGlobalWitness_of_interval
                                    (c := Generated.TrelChunk15.chunk) (start := 15360) (count := 1024) (row := row)
                                    Generated.TrelChunk15.certified.residual
                                    Generated.TrelChunk15.certified.startRow Generated.TrelChunk15.certified.rowCount
                                    (by omega) (by omega)
                                · exact someGlobalWitness_of_interval
                                    (c := Generated.TrelChunk16.chunk) (start := 16384) (count := 447) (row := row)
                                    Generated.TrelChunk16.certified.residual
                                    Generated.TrelChunk16.certified.startRow Generated.TrelChunk16.certified.rowCount
                                    (by omega) (by omega)

end TrelResidualRows
end Closed
end KnuthFasc8AEx210
