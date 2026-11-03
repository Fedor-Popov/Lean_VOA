import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_200 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 2, 1, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_201 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 2, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_202 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 2, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_203 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 2, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_204 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 2, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_205 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 2, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_206 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 3, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_207 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 3, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_208 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 4, 3, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_209 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 3, 4, 3, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_210 :
    ((e8Roots.map fun t => formL e8GL [2, 2, 3, 4, 3, 2, 1, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_211 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 2, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_212 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 2, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_213 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 2, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_214 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 2, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_215 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 2, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_216 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 3, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_217 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 3, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_218 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 4, 3, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_219 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 3, 4, 3, 2, 2, 1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_10 :
    e8RootChunk10.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_200 (And.intro e8_sumsq_201 (And.intro e8_sumsq_202 (And.intro e8_sumsq_203 (And.intro e8_sumsq_204 (And.intro e8_sumsq_205 (And.intro e8_sumsq_206 (And.intro e8_sumsq_207 (And.intro e8_sumsq_208 (And.intro e8_sumsq_209 (And.intro e8_sumsq_210 (And.intro e8_sumsq_211 (And.intro e8_sumsq_212 (And.intro e8_sumsq_213 (And.intro e8_sumsq_214 (And.intro e8_sumsq_215 (And.intro e8_sumsq_216 (And.intro e8_sumsq_217 (And.intro e8_sumsq_218 (e8_sumsq_219)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_10
