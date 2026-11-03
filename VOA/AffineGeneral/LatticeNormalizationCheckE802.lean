import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_040 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -2, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_041 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -2, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_042 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -2, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_043 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -2, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_044 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_045 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_046 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_047 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -1, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_048 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -1, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_049 :
    ((e8Roots.map fun t => formL e8GL [-1, 0, -1, -1, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_050 :
    ((e8Roots.map fun t => formL e8GL [0, 0, -1, -1, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_051 :
    ((e8Roots.map fun t => formL e8GL [0, -1, 0, -1, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_052 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, -1, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_053 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, -1, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_054 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_055 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 0, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_056 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 0, 0, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_057 :
    ((e8Roots.map fun t => formL e8GL [-2, -2, -3, -4, -3, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_058 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -3, -4, -3, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_059 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -4, -3, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_02 :
    e8RootChunk02.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_040 (And.intro e8_sumsq_041 (And.intro e8_sumsq_042 (And.intro e8_sumsq_043 (And.intro e8_sumsq_044 (And.intro e8_sumsq_045 (And.intro e8_sumsq_046 (And.intro e8_sumsq_047 (And.intro e8_sumsq_048 (And.intro e8_sumsq_049 (And.intro e8_sumsq_050 (And.intro e8_sumsq_051 (And.intro e8_sumsq_052 (And.intro e8_sumsq_053 (And.intro e8_sumsq_054 (And.intro e8_sumsq_055 (And.intro e8_sumsq_056 (And.intro e8_sumsq_057 (And.intro e8_sumsq_058 (e8_sumsq_059)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_02
