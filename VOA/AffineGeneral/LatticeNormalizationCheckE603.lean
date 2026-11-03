import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e6_sumsq_060 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 1, 1, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_061 :
    ((e6Roots.map fun t => formL e6GL [1, 0, 1, 1, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_062 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 1, 1, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_063 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 1, 1, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_064 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 1, 2, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_065 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 1, 2, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_066 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 2, 2, 1, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_067 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 1, 2, 2, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_068 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 1, 2, 2, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_069 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 2, 2, 2, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_070 :
    ((e6Roots.map fun t => formL e6GL [1, 1, 2, 3, 2, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_071 :
    ((e6Roots.map fun t => formL e6GL [1, 2, 2, 3, 2, 1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_chunk_03 :
    e6RootChunk03.Forall (fun s => ((e6Roots.map fun t => formL e6GL s t ^ 2).sum) = 48) := by
  exact And.intro e6_sumsq_060 (And.intro e6_sumsq_061 (And.intro e6_sumsq_062 (And.intro e6_sumsq_063 (And.intro e6_sumsq_064 (And.intro e6_sumsq_065 (And.intro e6_sumsq_066 (And.intro e6_sumsq_067 (And.intro e6_sumsq_068 (And.intro e6_sumsq_069 (And.intro e6_sumsq_070 (e6_sumsq_071)))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e6_chunk_03
