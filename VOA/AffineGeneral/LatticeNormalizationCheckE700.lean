import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e7_sumsq_000 :
    ((e7Roots.map fun t => formL e7GL [-2, -2, -3, -4, -3, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_001 :
    ((e7Roots.map fun t => formL e7GL [-1, -2, -3, -4, -3, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_002 :
    ((e7Roots.map fun t => formL e7GL [-1, -2, -2, -4, -3, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_003 :
    ((e7Roots.map fun t => formL e7GL [-1, -2, -2, -3, -3, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_004 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -3, -3, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_005 :
    ((e7Roots.map fun t => formL e7GL [-1, -2, -2, -3, -2, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_006 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -3, -2, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_007 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -2, -2, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_008 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -2, -2, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_009 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -2, -2, -2, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_010 :
    ((e7Roots.map fun t => formL e7GL [-1, -2, -2, -3, -2, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_011 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -3, -2, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_012 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -2, -2, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_013 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -2, -2, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_014 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -2, -2, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_015 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -2, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_016 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -2, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_017 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -2, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_018 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -1, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_019 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -1, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_chunk_00 :
    e7RootChunk00.Forall (fun s => ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72) := by
  exact And.intro e7_sumsq_000 (And.intro e7_sumsq_001 (And.intro e7_sumsq_002 (And.intro e7_sumsq_003 (And.intro e7_sumsq_004 (And.intro e7_sumsq_005 (And.intro e7_sumsq_006 (And.intro e7_sumsq_007 (And.intro e7_sumsq_008 (And.intro e7_sumsq_009 (And.intro e7_sumsq_010 (And.intro e7_sumsq_011 (And.intro e7_sumsq_012 (And.intro e7_sumsq_013 (And.intro e7_sumsq_014 (And.intro e7_sumsq_015 (And.intro e7_sumsq_016 (And.intro e7_sumsq_017 (And.intro e7_sumsq_018 (e7_sumsq_019)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_chunk_00
