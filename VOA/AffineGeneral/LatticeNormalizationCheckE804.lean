import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000
set_option linter.style.longLine false

theorem e8_sumsq_080 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, -1, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_081 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, -1, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_082 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, -1, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_083 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, 0, -1, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_084 :
    ((e8Roots.map fun t => formL e8GL [-1, -2, -2, -3, -2, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_085 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -3, -2, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_086 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -2, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_087 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -2, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_088 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -2, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_089 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -2, -2, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_090 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -2, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_091 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -2, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_092 :
    ((e8Roots.map fun t => formL e8GL [-1, -1, -1, -1, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_093 :
    ((e8Roots.map fun t => formL e8GL [0, -1, -1, -1, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_094 :
    ((e8Roots.map fun t => formL e8GL [-1, 0, -1, -1, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_095 :
    ((e8Roots.map fun t => formL e8GL [0, 0, -1, -1, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_096 :
    ((e8Roots.map fun t => formL e8GL [0, -1, 0, -1, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_097 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, -1, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_098 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, -1, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_sumsq_099 :
    ((e8Roots.map fun t => formL e8GL [0, 0, 0, 0, 0, -1, 0, 0] t ^ 2).sum) = 120 := by
  decide +kernel

theorem e8_chunk_04 :
    e8RootChunk04.Forall (fun s => ((e8Roots.map fun t => formL e8GL s t ^ 2).sum) = 120) := by
  exact And.intro e8_sumsq_080 (And.intro e8_sumsq_081 (And.intro e8_sumsq_082 (And.intro e8_sumsq_083 (And.intro e8_sumsq_084 (And.intro e8_sumsq_085 (And.intro e8_sumsq_086 (And.intro e8_sumsq_087 (And.intro e8_sumsq_088 (And.intro e8_sumsq_089 (And.intro e8_sumsq_090 (And.intro e8_sumsq_091 (And.intro e8_sumsq_092 (And.intro e8_sumsq_093 (And.intro e8_sumsq_094 (And.intro e8_sumsq_095 (And.intro e8_sumsq_096 (And.intro e8_sumsq_097 (And.intro e8_sumsq_098 (e8_sumsq_099)))))))))))))))))))

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_chunk_04
