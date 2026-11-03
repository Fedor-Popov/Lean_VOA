import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_140 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_141 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_142 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 1, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_143 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 0, 1, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_144 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 1, 1, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_145 :
    ((e8Roots.map fun t => formL e8GL [1, 0, 1, 1, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_146 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 1, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_147 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 1, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_148 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_149 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_150 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 1, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_151 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 2, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_152 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 2, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_153 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 2, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_154 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 2, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_155 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 2, 1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_156 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 0, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_157 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_158 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_159 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 1, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_07 :
    e8RootChunk07.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_140 (And.intro e8_sumsq_141 (And.intro e8_sumsq_142 (And.intro e8_sumsq_143 (And.intro e8_sumsq_144 (And.intro e8_sumsq_145 (And.intro e8_sumsq_146 (And.intro e8_sumsq_147 (And.intro e8_sumsq_148 (And.intro e8_sumsq_149 (And.intro e8_sumsq_150 (And.intro e8_sumsq_151 (And.intro e8_sumsq_152 (And.intro e8_sumsq_153 (And.intro e8_sumsq_154 (And.intro e8_sumsq_155 (And.intro e8_sumsq_156 (And.intro e8_sumsq_157 (And.intro e8_sumsq_158 (e8_sumsq_159)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_07
