import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e7_sumsq_060 :
    ((e7Roots.map fun t => formL e7GL [0, 0, -1, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_061 :
    ((e7Roots.map fun t => formL e7GL [0, -1, 0, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_062 :
    ((e7Roots.map fun t => formL e7GL [-1, 0, 0, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_063 :
    ((e7Roots.map fun t => formL e7GL [1, 0, 0, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_064 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 0, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_065 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 1, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_066 :
    ((e7Roots.map fun t => formL e7GL [1, 0, 1, 0, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_067 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_068 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 0, 1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_069 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 1, 1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_070 :
    ((e7Roots.map fun t => formL e7GL [1, 0, 1, 1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_071 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_072 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 1, 0, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_073 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_074 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 1, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_075 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 0, 1, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_076 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 1, 1, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_077 :
    ((e7Roots.map fun t => formL e7GL [1, 0, 1, 1, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_078 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 1, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_079 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 1, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_chunk_03 :
    e7RootChunk03.Forall (fun s => ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72) := by
  exact And.intro e7_sumsq_060 (And.intro e7_sumsq_061 (And.intro e7_sumsq_062 (And.intro e7_sumsq_063 (And.intro e7_sumsq_064 (And.intro e7_sumsq_065 (And.intro e7_sumsq_066 (And.intro e7_sumsq_067 (And.intro e7_sumsq_068 (And.intro e7_sumsq_069 (And.intro e7_sumsq_070 (And.intro e7_sumsq_071 (And.intro e7_sumsq_072 (And.intro e7_sumsq_073 (And.intro e7_sumsq_074 (And.intro e7_sumsq_075 (And.intro e7_sumsq_076 (And.intro e7_sumsq_077 (And.intro e7_sumsq_078 (e7_sumsq_079)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_chunk_03
