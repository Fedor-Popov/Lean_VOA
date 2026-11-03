import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e7_sumsq_080 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 2, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_081 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 2, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_082 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 2, 1, 0, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_083 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 0, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_084 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_085 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 1, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_086 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 0, 1, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_087 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 1, 1, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_088 :
    ((e7Roots.map fun t => formL e7GL [1, 0, 1, 1, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_089 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 1, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_090 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 1, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_091 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 2, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_092 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 2, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_093 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 2, 1, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_094 :
    ((e7Roots.map fun t => formL e7GL [0, 1, 1, 2, 2, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_095 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 1, 2, 2, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_096 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 2, 2, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_097 :
    ((e7Roots.map fun t => formL e7GL [1, 1, 2, 3, 2, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_098 :
    ((e7Roots.map fun t => formL e7GL [1, 2, 2, 3, 2, 1, 0] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_sumsq_099 :
    ((e7Roots.map fun t => formL e7GL [0, 0, 0, 0, 0, 0, 1] t ^ 2).sum) = 72 := by
  decide +kernel

theorem e7_chunk_04 :
    e7RootChunk04.Forall (fun s => ((e7Roots.map fun t => formL e7GL s t ^ 2).sum) = 72) := by
  exact And.intro e7_sumsq_080 (And.intro e7_sumsq_081 (And.intro e7_sumsq_082 (And.intro e7_sumsq_083 (And.intro e7_sumsq_084 (And.intro e7_sumsq_085 (And.intro e7_sumsq_086 (And.intro e7_sumsq_087 (And.intro e7_sumsq_088 (And.intro e7_sumsq_089 (And.intro e7_sumsq_090 (And.intro e7_sumsq_091 (And.intro e7_sumsq_092 (And.intro e7_sumsq_093 (And.intro e7_sumsq_094 (And.intro e7_sumsq_095 (And.intro e7_sumsq_096 (And.intro e7_sumsq_097 (And.intro e7_sumsq_098 (e7_sumsq_099)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e7_chunk_04
