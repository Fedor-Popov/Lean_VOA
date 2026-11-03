import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_000 :
    ((e8Roots.map fun t => formL e8GL [-2, -3, -4, -6, -5, -4, -3, -2] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_001 :
    ((e8Roots.map fun t => formL e8GL [-2, -3, -4, -6, -5, -4, -3, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_002 :
    ((e8Roots.map fun t => formL e8GL [-2, -3, -4, -6, -5, -4, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_003 :
    ((e8Roots.map fun t => formL e8GL [-2, -3, -4, -6, -5, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_004 :
    ((e8Roots.map fun t => formL e8GL [-2, -3, -4, -6, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_005 :
    ((e8Roots.map fun t => formL e8GL [-2, -3, -4, -5, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_006 :
    ((e8Roots.map fun t => formL e8GL [-2, -2, -4, -5, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_007 :
    ((e8Roots.map fun t => formL e8GL [-2, -3, -3, -5, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_008 :
    ((e8Roots.map fun t => formL e8GL [-1, -3, -3, -5, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_009 :
    ((e8Roots.map fun t => formL e8GL [-2, -2, -3, -5, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_010 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -3, -5, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_011 :
    ((e8Roots.map fun t => formL e8GL [-2, -2, -3, -4, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_012 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -3, -4, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_013 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -4, -4, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_014 :
    ((e8Roots.map fun t => formL e8GL [-2, -2, -3, -4, -3, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_015 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -3, -4, -3, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_016 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -4, -3, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_017 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -3, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_018 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -3, -3, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_019 :
    ((e8Roots.map fun t => formL e8GL [-2, -2, -3, -4, -3, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_00 :
    e8RootChunk00.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_000 (And.intro e8_sumsq_001 (And.intro e8_sumsq_002 (And.intro e8_sumsq_003 (And.intro e8_sumsq_004 (And.intro e8_sumsq_005 (And.intro e8_sumsq_006 (And.intro e8_sumsq_007 (And.intro e8_sumsq_008 (And.intro e8_sumsq_009 (And.intro e8_sumsq_010 (And.intro e8_sumsq_011 (And.intro e8_sumsq_012 (And.intro e8_sumsq_013 (And.intro e8_sumsq_014 (And.intro e8_sumsq_015 (And.intro e8_sumsq_016 (And.intro e8_sumsq_017 (And.intro e8_sumsq_018 (e8_sumsq_019)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_00
