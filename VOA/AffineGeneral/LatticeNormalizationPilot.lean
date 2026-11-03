import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 10000

theorem e8_fixed_239 :
    ((e8Roots.map fun t => formL e8GL [2, 3, 4, 6, 5, 4, 3, 2] t ^ 2).sum) = 120 := by
  decide +kernel

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e8_fixed_239
