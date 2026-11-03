import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem d4_sumsq_020 :
    ((d4Roots.map fun t => formL d4GL [1, 1, 0, 1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_021 :
    ((d4Roots.map fun t => formL d4GL [0, 1, 1, 1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_022 :
    ((d4Roots.map fun t => formL d4GL [1, 1, 1, 1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_sumsq_023 :
    ((d4Roots.map fun t => formL d4GL [1, 2, 1, 1] t ^ 2).sum) = 24 := by
  decide +kernel

theorem d4_chunk_01 :
    d4RootChunk01.Forall (fun s => ((d4Roots.map fun t => formL d4GL s t ^ 2).sum) = 24) := by
  exact And.intro d4_sumsq_020 (And.intro d4_sumsq_021 (And.intro d4_sumsq_022 (d4_sumsq_023)))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.d4_chunk_01
