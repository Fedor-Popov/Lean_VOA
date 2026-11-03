import VOA.AffineGeneral.LatticeNormalizationData

namespace VOA.AffineGeneral.Normalization.Certificate

set_option maxRecDepth 100000

theorem e6_enumRoots : enumRoots e6RowsData = e6Roots := by
  decide +kernel

end VOA.AffineGeneral.Normalization.Certificate

#print axioms VOA.AffineGeneral.Normalization.Certificate.e6_enumRoots
