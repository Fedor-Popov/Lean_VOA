import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_160 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 0, 1, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_161 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 1, 1, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_162 :
    ((e8Roots.map fun t => formL e8GL [1, 0, 1, 1, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_163 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 1, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_164 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 1, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_165 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_166 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_167 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 1, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_168 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 2, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_169 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 2, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_170 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 2, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_171 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 2, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_172 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 2, 1, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_173 :
    ((e8Roots.map fun t => formL e8GL [0, 1, 1, 2, 2, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_174 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 1, 2, 2, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_175 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 2, 2, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_176 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 2, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_177 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 2, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_178 :
    ((e8Roots.map fun t => formL e8GL [1, 1, 2, 3, 3, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_179 :
    ((e8Roots.map fun t => formL e8GL [1, 2, 2, 3, 3, 2, 1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_08 :
    e8RootChunk08.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_160 (And.intro e8_sumsq_161 (And.intro e8_sumsq_162 (And.intro e8_sumsq_163 (And.intro e8_sumsq_164 (And.intro e8_sumsq_165 (And.intro e8_sumsq_166 (And.intro e8_sumsq_167 (And.intro e8_sumsq_168 (And.intro e8_sumsq_169 (And.intro e8_sumsq_170 (And.intro e8_sumsq_171 (And.intro e8_sumsq_172 (And.intro e8_sumsq_173 (And.intro e8_sumsq_174 (And.intro e8_sumsq_175 (And.intro e8_sumsq_176 (And.intro e8_sumsq_177 (And.intro e8_sumsq_178 (e8_sumsq_179)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_08
