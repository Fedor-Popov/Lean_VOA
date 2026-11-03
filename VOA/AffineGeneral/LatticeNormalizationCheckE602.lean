import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e6_sumsq_040 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_041 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 0, 1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_042 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 1, 1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_043 :
    ((e6Roots.map fun t => formL e6GL [1, 0, 1, 1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_044 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 1, 1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_045 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 1, 1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_046 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 0, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_047 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 1, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_048 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 0, 1, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_049 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 1, 1, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_050 :
    ((e6Roots.map fun t => formL e6GL [1, 0, 1, 1, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_051 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 1, 1, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_052 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 1, 1, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_053 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 1, 2, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_054 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 1, 2, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_055 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 2, 2, 1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_056 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 0, 0, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_057 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 0, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_058 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 1, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_059 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 0, 1, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_chunk_02 :
    e6RootChunk02.Forall (fun s => ((e6Roots.map fun t => formL e6GL s t ^ 2).sum) = 48) := by
  exact And.intro e6_sumsq_040 (And.intro e6_sumsq_041 (And.intro e6_sumsq_042 (And.intro e6_sumsq_043 (And.intro e6_sumsq_044 (And.intro e6_sumsq_045 (And.intro e6_sumsq_046 (And.intro e6_sumsq_047 (And.intro e6_sumsq_048 (And.intro e6_sumsq_049 (And.intro e6_sumsq_050 (And.intro e6_sumsq_051 (And.intro e6_sumsq_052 (And.intro e6_sumsq_053 (And.intro e6_sumsq_054 (And.intro e6_sumsq_055 (And.intro e6_sumsq_056 (And.intro e6_sumsq_057 (And.intro e6_sumsq_058 (e6_sumsq_059)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e6_chunk_02
