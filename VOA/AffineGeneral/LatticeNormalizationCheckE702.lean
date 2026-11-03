import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e7_sumsq_040 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, -1, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_041 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_042 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 0, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_043 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -2, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_044 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -2, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_045 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -2, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_046 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -1, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_047 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -1, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_048 :
    ((e7Roots.map fun t => formL e7GL [-1, 0, -1, -1, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_049 :
    ((e7Roots.map fun t => formL e7GL [0, 0, -1, -1, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_050 :
    ((e7Roots.map fun t => formL e7GL [0, -1, 0, -1, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_051 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, -1, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_052 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, -1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_053 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_054 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_055 :
    ((e7Roots.map fun t => formL e7GL [-1, 0, -1, -1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_056 :
    ((e7Roots.map fun t => formL e7GL [0, 0, -1, -1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_057 :
    ((e7Roots.map fun t => formL e7GL [0, -1, 0, -1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_058 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, -1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_059 :
    ((e7Roots.map fun t => formL e7GL [-1, 0, -1, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_chunk_02 :
    e7RootChunk02.Forall (fun s => ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72) := by
  exact And.intro e7_sumsq_040 (And.intro e7_sumsq_041 (And.intro e7_sumsq_042 (And.intro e7_sumsq_043 (And.intro e7_sumsq_044 (And.intro e7_sumsq_045 (And.intro e7_sumsq_046 (And.intro e7_sumsq_047 (And.intro e7_sumsq_048 (And.intro e7_sumsq_049 (And.intro e7_sumsq_050 (And.intro e7_sumsq_051 (And.intro e7_sumsq_052 (And.intro e7_sumsq_053 (And.intro e7_sumsq_054 (And.intro e7_sumsq_055 (And.intro e7_sumsq_056 (And.intro e7_sumsq_057 (And.intro e7_sumsq_058 (e7_sumsq_059)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_chunk_02
