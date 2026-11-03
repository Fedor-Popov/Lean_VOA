import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e7_sumsq_100 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 0, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_101 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_102 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 1, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_103 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 0, 1, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_104 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 1, 1, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_105 :
    ((e7Roots.map fun t => formL e7GL [1, 0, 1, 1, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_106 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 1, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_107 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 1, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_108 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 2, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_109 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 2, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_110 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 2, 1, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_111 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 2, 2, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_112 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 2, 2, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_113 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 2, 2, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_114 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 3, 2, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_115 :
    ((e7Roots.map fun t => formL e7GL [1, 2, 2, 3, 2, 1, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_116 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 2, 2, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_117 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 2, 2, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_118 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 2, 2, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_119 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 3, 2, 2, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_chunk_05 :
    e7RootChunk05.Forall (fun s => ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72) := by
  exact And.intro e7_sumsq_100 (And.intro e7_sumsq_101 (And.intro e7_sumsq_102 (And.intro e7_sumsq_103 (And.intro e7_sumsq_104 (And.intro e7_sumsq_105 (And.intro e7_sumsq_106 (And.intro e7_sumsq_107 (And.intro e7_sumsq_108 (And.intro e7_sumsq_109 (And.intro e7_sumsq_110 (And.intro e7_sumsq_111 (And.intro e7_sumsq_112 (And.intro e7_sumsq_113 (And.intro e7_sumsq_114 (And.intro e7_sumsq_115 (And.intro e7_sumsq_116 (And.intro e7_sumsq_117 (And.intro e7_sumsq_118 (e7_sumsq_119)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_chunk_05
