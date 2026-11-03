import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_060 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -3, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_061 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -3, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_062 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -2, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_063 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -2, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_064 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -2, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_065 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -2, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_066 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -2, -2, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_067 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -2, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_068 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -2, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_069 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -2, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_070 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -2, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_071 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -2, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_072 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_073 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_074 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_075 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -1, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_076 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -1, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_077 :
    ((e8Roots.map fun t => formL e8GL [-1, 0, -1, -1, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_078 :
    ((e8Roots.map fun t => formL e8GL [0, 0, -1, -1, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_079 :
    ((e8Roots.map fun t => formL e8GL [0, -1, 0, -1, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_03 :
    e8RootChunk03.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_060 (And.intro e8_sumsq_061 (And.intro e8_sumsq_062 (And.intro e8_sumsq_063 (And.intro e8_sumsq_064 (And.intro e8_sumsq_065 (And.intro e8_sumsq_066 (And.intro e8_sumsq_067 (And.intro e8_sumsq_068 (And.intro e8_sumsq_069 (And.intro e8_sumsq_070 (And.intro e8_sumsq_071 (And.intro e8_sumsq_072 (And.intro e8_sumsq_073 (And.intro e8_sumsq_074 (And.intro e8_sumsq_075 (And.intro e8_sumsq_076 (And.intro e8_sumsq_077 (And.intro e8_sumsq_078 (e8_sumsq_079)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_03
