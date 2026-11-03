import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e7_sumsq_120 :
    ((e7Roots.map fun t => formL e7GL [1, 2, 2, 3, 2, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_121 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 3, 3, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_122 :
    ((e7Roots.map fun t => formL e7GL [1, 2, 2, 3, 3, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_123 :
    ((e7Roots.map fun t => formL e7GL [1, 2, 2, 4, 3, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_124 :
    ((e7Roots.map fun t => formL e7GL [1, 2, 3, 4, 3, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_125 :
    ((e7Roots.map fun t => formL e7GL [2, 2, 3, 4, 3, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_chunk_06 :
    e7RootChunk06.Forall (fun s => ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72) := by
  exact And.intro e7_sumsq_120 (And.intro e7_sumsq_121 (And.intro e7_sumsq_122 (And.intro e7_sumsq_123 (And.intro e7_sumsq_124 (e7_sumsq_125)))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_chunk_06
