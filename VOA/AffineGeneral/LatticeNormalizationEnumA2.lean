import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 100000

theorem a2_enumRoots : enumRoots a2RowsData = a2Roots := by
  decide +kernel

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.a2_enumRoots
