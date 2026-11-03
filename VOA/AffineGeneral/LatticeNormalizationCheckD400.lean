import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem d4_sumsq_000 :
    ((d4Roots.map fun t => formL d4GL [-1, -2, -1, -1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_001 :
    ((d4Roots.map fun t => formL d4GL [-1, -1, -1, -1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_002 :
    ((d4Roots.map fun t => formL d4GL [0, -1, -1, -1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_003 :
    ((d4Roots.map fun t => formL d4GL [-1, -1, 0, -1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_004 :
    ((d4Roots.map fun t => formL d4GL [0, -1, 0, -1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_005 :
    ((d4Roots.map fun t => formL d4GL [0, 0, 0, -1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_006 :
    ((d4Roots.map fun t => formL d4GL [-1, -1, -1, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_007 :
    ((d4Roots.map fun t => formL d4GL [0, -1, -1, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_008 :
    ((d4Roots.map fun t => formL d4GL [0, 0, -1, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_009 :
    ((d4Roots.map fun t => formL d4GL [-1, -1, 0, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_010 :
    ((d4Roots.map fun t => formL d4GL [0, -1, 0, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_011 :
    ((d4Roots.map fun t => formL d4GL [-1, 0, 0, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_012 :
    ((d4Roots.map fun t => formL d4GL [1, 0, 0, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_013 :
    ((d4Roots.map fun t => formL d4GL [0, 1, 0, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_014 :
    ((d4Roots.map fun t => formL d4GL [1, 1, 0, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_015 :
    ((d4Roots.map fun t => formL d4GL [0, 0, 1, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_016 :
    ((d4Roots.map fun t => formL d4GL [0, 1, 1, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_017 :
    ((d4Roots.map fun t => formL d4GL [1, 1, 1, 0] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_018 :
    ((d4Roots.map fun t => formL d4GL [0, 0, 0, 1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_019 :
    ((d4Roots.map fun t => formL d4GL [0, 1, 0, 1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_chunk_00 :
    d4RootChunk00.Forall (fun s => ((d4Roots.map fun t => formL d4GL s t ^ 2).sum) = 24) := by
  exact And.intro d4_sumsq_000 (And.intro d4_sumsq_001 (And.intro d4_sumsq_002 (And.intro d4_sumsq_003 (And.intro d4_sumsq_004 (And.intro d4_sumsq_005 (And.intro d4_sumsq_006 (And.intro d4_sumsq_007 (And.intro d4_sumsq_008 (And.intro d4_sumsq_009 (And.intro d4_sumsq_010 (And.intro d4_sumsq_011 (And.intro d4_sumsq_012 (And.intro d4_sumsq_013 (And.intro d4_sumsq_014 (And.intro d4_sumsq_015 (And.intro d4_sumsq_016 (And.intro d4_sumsq_017 (And.intro d4_sumsq_018 (d4_sumsq_019)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.d4_chunk_00
