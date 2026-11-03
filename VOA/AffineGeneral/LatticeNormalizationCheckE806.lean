import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_120 :
    ((e8Roots.map fun t => formL e8GL [1, 0, 0, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_121 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 0, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_122 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 1, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_123 :
    ((e8Roots.map fun t => formL e8GL [1, 0, 1, 0, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_124 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_125 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 0, 1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_126 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 1, 1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_127 :
    ((e8Roots.map fun t => formL e8GL [1, 0, 1, 1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_128 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_129 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 1, 0, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_130 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_131 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 1, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_132 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 0, 1, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_133 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 1, 1, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_134 :
    ((e8Roots.map fun t => formL e8GL [1, 0, 1, 1, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_135 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 1, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_136 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 1, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_137 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_138 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_139 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 1, 0, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_06 :
    e8RootChunk06.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_120 (And.intro e8_sumsq_121 (And.intro e8_sumsq_122 (And.intro e8_sumsq_123 (And.intro e8_sumsq_124 (And.intro e8_sumsq_125 (And.intro e8_sumsq_126 (And.intro e8_sumsq_127 (And.intro e8_sumsq_128 (And.intro e8_sumsq_129 (And.intro e8_sumsq_130 (And.intro e8_sumsq_131 (And.intro e8_sumsq_132 (And.intro e8_sumsq_133 (And.intro e8_sumsq_134 (And.intro e8_sumsq_135 (And.intro e8_sumsq_136 (And.intro e8_sumsq_137 (And.intro e8_sumsq_138 (e8_sumsq_139)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_06
