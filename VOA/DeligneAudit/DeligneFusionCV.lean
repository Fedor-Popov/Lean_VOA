import VOA.DeligneAudit.DeligneFusionCVTotal
import VOA.DeligneAudit.DeligneFusionCVResidualThetaZero
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationDimension
import VOA.DeligneAudit.DeligneFusionCVRectZero
import VOA.DeligneAudit.DeligneFusionCVRectCount
import VOA.DeligneAudit.DeligneFusionCVRectList
import VOA.DeligneAudit.DeligneFusionCVRectCutoff
import VOA.DeligneAudit.DeligneFusionCVRectReflection
import VOA.DeligneAudit.DeligneFusionCVRectPolynomialCyclic
import VOA.DeligneAudit.DeligneFusionCVRectPolynomialCurrentSplit
import VOA.DeligneAudit.DeligneFusionCVRectPolynomialRelations
import VOA.DeligneAudit.DeligneFusionCVRectFamily
import VOA.DeligneAudit.DeligneFusionCVRectOneColor
import VOA.DeligneAudit.DeligneFusionCVRectFamilyCanonical
import VOA.DeligneAudit.DeligneFusionCVRectMixedSpanning
import VOA.DeligneAudit.DeligneFusionCVSmall
import VOA.DeligneAudit.DeligneFusionCVRectStarBase
import VOA.DeligneAudit.DeligneFusionCVRectStarIntegration

import VOA.DeligneAudit.DeligneFusionCVRectFilteredRectangular
import VOA.DeligneAudit.DeligneFusionCVRectAdjointBound
import VOA.DeligneAudit.DeligneFusionCVResidualThetaBoundFinal

/-!
# The complete A₂ auxiliary CV proof

Both base families in the actual universal-module induction are proved:
`CVUniv.sharpRectangularBases` and `CVUniv.residualTheta3Bound`.
The mixed coefficient relations hold in the restricted PBW associated graded;
the polynomial quotient counts and the exhaustive filtered dimension transfer
are actual proved maps and bounds. No KR, fusion identification, source
finite-dimensionality or coefficient-ideal inclusion is assumed.
-/

#print axioms VOA.DeligneAudit.A2.CVUniv.sharpRectangularBases
#print axioms VOA.DeligneAudit.A2.CVUniv.residualTheta3Bound
#print axioms VOA.DeligneAudit.A2.CVUniv.fusionTotalDim_of_cvBases
#print axioms VOA.DeligneAudit.A2.CVRectAdjointBound.adjoint_cubes_bound
#print axioms VOA.DeligneAudit.A2.CVSmall.totalDim_two
