import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem a2_sumsq_000 :
    ((a2Roots.map fun t => formL a2GL [-1, -1] t ^ 2).sum) = 12 := by
  decide +kernel

theorem a2_sumsq_001 :
    ((a2Roots.map fun t => formL a2GL [0, -1] t ^ 2).sum) = 12 := by
  decide +kernel

theorem a2_sumsq_002 :
    ((a2Roots.map fun t => formL a2GL [-1, 0] t ^ 2).sum) = 12 := by
  decide +kernel

theorem a2_sumsq_003 :
    ((a2Roots.map fun t => formL a2GL [1, 0] t ^ 2).sum) = 12 := by
  decide +kernel

theorem a2_sumsq_004 :
    ((a2Roots.map fun t => formL a2GL [0, 1] t ^ 2).sum) = 12 := by
  decide +kernel

theorem a2_sumsq_005 :
    ((a2Roots.map fun t => formL a2GL [1, 1] t ^ 2).sum) = 12 := by
  decide +kernel

theorem a2_chunk_00 :
    a2RootChunk00.Forall (fun s => ((a2Roots.map fun t => formL a2GL s t ^ 2).sum) = 12) := by
  exact And.intro a2_sumsq_000 (And.intro a2_sumsq_001 (And.intro a2_sumsq_002 (And.intro a2_sumsq_003 (And.intro a2_sumsq_004 (a2_sumsq_005)))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.a2_chunk_00
