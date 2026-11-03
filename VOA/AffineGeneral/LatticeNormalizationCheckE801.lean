import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_020 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -3, -4, -3, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_021 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -4, -3, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_022 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -3, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_023 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -3, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_024 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -2, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_025 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -2, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_026 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -2, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_027 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -2, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_028 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -2, -2, -2, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_029 :
    ((e8Roots.map fun t => formL e8GL [-2, -2, -3, -4, -3, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_030 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -3, -4, -3, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_031 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -4, -3, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_032 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -3, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_033 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -3, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_034 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -2, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_035 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -2, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_036 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -2, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_037 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -2, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_038 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -2, -2, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_039 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -2, -1, -1, -1] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_01 :
    e8RootChunk01.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_020 (And.intro e8_sumsq_021 (And.intro e8_sumsq_022 (And.intro e8_sumsq_023 (And.intro e8_sumsq_024 (And.intro e8_sumsq_025 (And.intro e8_sumsq_026 (And.intro e8_sumsq_027 (And.intro e8_sumsq_028 (And.intro e8_sumsq_029 (And.intro e8_sumsq_030 (And.intro e8_sumsq_031 (And.intro e8_sumsq_032 (And.intro e8_sumsq_033 (And.intro e8_sumsq_034 (And.intro e8_sumsq_035 (And.intro e8_sumsq_036 (And.intro e8_sumsq_037 (And.intro e8_sumsq_038 (e8_sumsq_039)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_01
