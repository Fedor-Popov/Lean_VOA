import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_180 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 4, 3, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_181 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 3, 4, 3, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_182 :
    ((e8Roots.map fun t => formL e8GL [2, 2, 3, 4, 3, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_183 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 0, 0, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_184 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 0, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_185 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_186 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_187 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 1, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_188 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 0, 1, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_189 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 1, 1, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_190 :
    ((e8Roots.map fun t => formL e8GL [1, 0, 1, 1, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_191 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 1, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_192 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 1, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_193 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_194 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_195 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 1, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_196 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 2, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_197 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 2, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_198 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 2, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_199 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 2, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_09 :
    e8RootChunk09.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_180 (And.intro e8_sumsq_181 (And.intro e8_sumsq_182 (And.intro e8_sumsq_183 (And.intro e8_sumsq_184 (And.intro e8_sumsq_185 (And.intro e8_sumsq_186 (And.intro e8_sumsq_187 (And.intro e8_sumsq_188 (And.intro e8_sumsq_189 (And.intro e8_sumsq_190 (And.intro e8_sumsq_191 (And.intro e8_sumsq_192 (And.intro e8_sumsq_193 (And.intro e8_sumsq_194 (And.intro e8_sumsq_195 (And.intro e8_sumsq_196 (And.intro e8_sumsq_197 (And.intro e8_sumsq_198 (e8_sumsq_199)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_09
