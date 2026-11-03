import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e7_sumsq_020 :
    ((e7Roots.map fun t => formL e7GL [-1, 0, -1, -1, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_021 :
    ((e7Roots.map fun t => formL e7GL [0, 0, -1, -1, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_022 :
    ((e7Roots.map fun t => formL e7GL [0, -1, 0, -1, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_023 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, -1, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_024 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, -1, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_025 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 0, -1, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_026 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 0, 0, -1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_027 :
    ((e7Roots.map fun t => formL e7GL [-1, -2, -2, -3, -2, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_028 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -3, -2, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_029 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -2, -2, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_030 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -2, -2, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_031 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -2, -2, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_032 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -2, -2, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_033 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -2, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_034 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -2, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_035 :
    ((e7Roots.map fun t => formL e7GL [-1, -1, -1, -1, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_036 :
    ((e7Roots.map fun t => formL e7GL [0, -1, -1, -1, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_037 :
    ((e7Roots.map fun t => formL e7GL [-1, 0, -1, -1, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_038 :
    ((e7Roots.map fun t => formL e7GL [0, 0, -1, -1, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_039 :
    ((e7Roots.map fun t => formL e7GL [0, -1, 0, -1, -1, -1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_chunk_01 :
    e7RootChunk01.Forall (fun s => ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72) := by
  exact And.intro e7_sumsq_020 (And.intro e7_sumsq_021 (And.intro e7_sumsq_022 (And.intro e7_sumsq_023 (And.intro e7_sumsq_024 (And.intro e7_sumsq_025 (And.intro e7_sumsq_026 (And.intro e7_sumsq_027 (And.intro e7_sumsq_028 (And.intro e7_sumsq_029 (And.intro e7_sumsq_030 (And.intro e7_sumsq_031 (And.intro e7_sumsq_032 (And.intro e7_sumsq_033 (And.intro e7_sumsq_034 (And.intro e7_sumsq_035 (And.intro e7_sumsq_036 (And.intro e7_sumsq_037 (And.intro e7_sumsq_038 (e7_sumsq_039)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_chunk_01
