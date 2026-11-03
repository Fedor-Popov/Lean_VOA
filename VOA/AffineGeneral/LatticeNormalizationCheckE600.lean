import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e6_sumsq_000 :
    ((e6Roots.map fun t => formL e6GL [-1, -2, -2, -3, -2, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_001 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -2, -3, -2, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_002 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -2, -2, -2, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_003 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -1, -2, -2, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_004 :
    ((e6Roots.map fun t => formL e6GL [0, -1, -1, -2, -2, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_005 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -2, -2, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_006 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -1, -2, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_007 :
    ((e6Roots.map fun t => formL e6GL [0, -1, -1, -2, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_008 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -1, -1, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_009 :
    ((e6Roots.map fun t => formL e6GL [0, -1, -1, -1, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_010 :
    ((e6Roots.map fun t => formL e6GL [-1, 0, -1, -1, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_011 :
    ((e6Roots.map fun t => formL e6GL [0, 0, -1, -1, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_012 :
    ((e6Roots.map fun t => formL e6GL [0, -1, 0, -1, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_013 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, -1, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_014 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 0, -1, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_015 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 0, 0, -1] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_016 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -2, -2, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_017 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -1, -2, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_018 :
    ((e6Roots.map fun t => formL e6GL [0, -1, -1, -2, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_019 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -1, -1, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_chunk_00 :
    e6RootChunk00.Forall (fun s => ((e6Roots.map fun t => formL e6GL s t ^ 2).sum) = 48) := by
  exact And.intro e6_sumsq_000 (And.intro e6_sumsq_001 (And.intro e6_sumsq_002 (And.intro e6_sumsq_003 (And.intro e6_sumsq_004 (And.intro e6_sumsq_005 (And.intro e6_sumsq_006 (And.intro e6_sumsq_007 (And.intro e6_sumsq_008 (And.intro e6_sumsq_009 (And.intro e6_sumsq_010 (And.intro e6_sumsq_011 (And.intro e6_sumsq_012 (And.intro e6_sumsq_013 (And.intro e6_sumsq_014 (And.intro e6_sumsq_015 (And.intro e6_sumsq_016 (And.intro e6_sumsq_017 (And.intro e6_sumsq_018 (e6_sumsq_019)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e6_chunk_00
