import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_100 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_101 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_102 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_103 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -1, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_104 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -1, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_105 :
    ((e8Roots.map fun t => formL e8GL [-1, 0, -1, -1, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_106 :
    ((e8Roots.map fun t => formL e8GL [0, 0, -1, -1, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_107 :
    ((e8Roots.map fun t => formL e8GL [0, -1, 0, -1, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_108 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, -1, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_109 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, -1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_110 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_111 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_112 :
    ((e8Roots.map fun t => formL e8GL [-1, 0, -1, -1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_113 :
    ((e8Roots.map fun t => formL e8GL [0, 0, -1, -1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_114 :
    ((e8Roots.map fun t => formL e8GL [0, -1, 0, -1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_115 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, -1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_116 :
    ((e8Roots.map fun t => formL e8GL [-1, 0, -1, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_117 :
    ((e8Roots.map fun t => formL e8GL [0, 0, -1, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_118 :
    ((e8Roots.map fun t => formL e8GL [0, -1, 0, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_119 :
    ((e8Roots.map fun t => formL e8GL [-1, 0, 0, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_05 :
    e8RootChunk05.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_100 (And.intro e8_sumsq_101 (And.intro e8_sumsq_102 (And.intro e8_sumsq_103 (And.intro e8_sumsq_104 (And.intro e8_sumsq_105 (And.intro e8_sumsq_106 (And.intro e8_sumsq_107 (And.intro e8_sumsq_108 (And.intro e8_sumsq_109 (And.intro e8_sumsq_110 (And.intro e8_sumsq_111 (And.intro e8_sumsq_112 (And.intro e8_sumsq_113 (And.intro e8_sumsq_114 (And.intro e8_sumsq_115 (And.intro e8_sumsq_116 (And.intro e8_sumsq_117 (And.intro e8_sumsq_118 (e8_sumsq_119)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_05
