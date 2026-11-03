import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e6_sumsq_020 :
    ((e6Roots.map fun t => formL e6GL [0, -1, -1, -1, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_021 :
    ((e6Roots.map fun t => formL e6GL [-1, 0, -1, -1, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_022 :
    ((e6Roots.map fun t => formL e6GL [0, 0, -1, -1, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_023 :
    ((e6Roots.map fun t => formL e6GL [0, -1, 0, -1, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_024 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, -1, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_025 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, 0, -1, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_026 :
    ((e6Roots.map fun t => formL e6GL [-1, -1, -1, -1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_027 :
    ((e6Roots.map fun t => formL e6GL [0, -1, -1, -1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_028 :
    ((e6Roots.map fun t => formL e6GL [-1, 0, -1, -1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_029 :
    ((e6Roots.map fun t => formL e6GL [0, 0, -1, -1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_030 :
    ((e6Roots.map fun t => formL e6GL [0, -1, 0, -1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_031 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 0, -1, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_032 :
    ((e6Roots.map fun t => formL e6GL [-1, 0, -1, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_033 :
    ((e6Roots.map fun t => formL e6GL [0, 0, -1, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_034 :
    ((e6Roots.map fun t => formL e6GL [0, -1, 0, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_035 :
    ((e6Roots.map fun t => formL e6GL [-1, 0, 0, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_036 :
    ((e6Roots.map fun t => formL e6GL [1, 0, 0, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_037 :
    ((e6Roots.map fun t => formL e6GL [0, 1, 0, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_038 :
    ((e6Roots.map fun t => formL e6GL [0, 0, 1, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_sumsq_039 :
    ((e6Roots.map fun t => formL e6GL [1, 0, 1, 0, 0, 0] t ^ 2).sum) = 48 := by
  decide +kernel

theorem e6_chunk_01 :
    e6RootChunk01.Forall (fun s => ((e6Roots.map fun t => formL e6GL s t ^ 2).sum) = 48) := by
  exact And.intro e6_sumsq_020 (And.intro e6_sumsq_021 (And.intro e6_sumsq_022 (And.intro e6_sumsq_023 (And.intro e6_sumsq_024 (And.intro e6_sumsq_025 (And.intro e6_sumsq_026 (And.intro e6_sumsq_027 (And.intro e6_sumsq_028 (And.intro e6_sumsq_029 (And.intro e6_sumsq_030 (And.intro e6_sumsq_031 (And.intro e6_sumsq_032 (And.intro e6_sumsq_033 (And.intro e6_sumsq_034 (And.intro e6_sumsq_035 (And.intro e6_sumsq_036 (And.intro e6_sumsq_037 (And.intro e6_sumsq_038 (e6_sumsq_039)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e6_chunk_01
