import VOA.AffineGeneral.LatticeNormalizationData
import VOA.AffineGeneral.LatticeNormalizationPilot

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_220 :
    ((e8Roots.map fun t => formL e8GL [2, 2, 3, 4, 3, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_221 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 3, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_222 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 3, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_223 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 4, 3, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_224 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 3, 4, 3, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_225 :
    ((e8Roots.map fun t => formL e8GL [2, 2, 3, 4, 3, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_226 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 4, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_227 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 3, 4, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_228 :
    ((e8Roots.map fun t => formL e8GL [2, 2, 3, 4, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_229 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 3, 5, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_230 :
    ((e8Roots.map fun t => formL e8GL [2, 2, 3, 5, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_231 :
    ((e8Roots.map fun t => formL e8GL [1, 3, 3, 5, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_232 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 3, 5, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_233 :
    ((e8Roots.map fun t => formL e8GL [2, 2, 4, 5, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_234 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 4, 5, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_235 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 4, 6, 4, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_236 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 4, 6, 5, 3, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_237 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 4, 6, 5, 4, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_238 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 4, 6, 5, 4, 3, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_239 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 4, 6, 5, 4, 3, 2] t ^ 2).sum) = 120 := by
  exact e8_fixed_239

theorem e8_chunk_11 :
    e8RootChunk11.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_220 (And.intro e8_sumsq_221 (And.intro e8_sumsq_222 (And.intro e8_sumsq_223 (And.intro e8_sumsq_224 (And.intro e8_sumsq_225 (And.intro e8_sumsq_226 (And.intro e8_sumsq_227 (And.intro e8_sumsq_228 (And.intro e8_sumsq_229 (And.intro e8_sumsq_230 (And.intro e8_sumsq_231 (And.intro e8_sumsq_232 (And.intro e8_sumsq_233 (And.intro e8_sumsq_234 (And.intro e8_sumsq_235 (And.intro e8_sumsq_236 (And.intro e8_sumsq_237 (And.intro e8_sumsq_238 (e8_sumsq_239)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_11
