import VOA.Core.DongSuper
import VOA.Core.SuperVertexOperatorAlgebra
import VOA.Core.SuperWeakAssoc
import VOA.Examples.FreeFermion
import VOA.Examples.BCGhosts
import VOA.Examples.BetaGamma
open VOA
-- Axis B (parity / Koszul sign): Foundations.Parity
#print axioms VOA.parSign_add
#print axioms VOA.koszul_mul_self
#print axioms VOA.koszul_add_left
#print axioms VOA.ParityGrading.even
-- Axis B (ε-twisted locality): Foundations.Locality
#print axioms VOA.bracketDistε_one
#print axioms VOA.localε_one_iff
#print axioms VOA.bracketDistε_swap
-- the super-Jacobi identity and ε-generic Dong: Core.DongSuper
#print axioms VOA.jacobi₃ε
#print axioms VOA.dong_coreε
#print axioms VOA.dong_nonnegε
#print axioms VOA.dong_nonneg_of_dong_nonnegε
-- the generalized core structures: Core.SuperVertexAlgebra / SuperVertexOperatorAlgebra
#print axioms VOA.isInternal_extend
#print axioms VOA.PreVertexAlgebra.toSuper
#print axioms VOA.VertexOperatorAlgebra.toSuper
#print axioms VOA.VertexOperatorAlgebra.toSuper_spinStatistics
-- the ε-generic OPE criterion and the super mode API
#print axioms VOA.localε_iff_deltaSum
#print axioms VOA.localε_of_car
#print axioms VOA.localε_neg_one_of_anticomm
#print axioms VOA.SuperVertexAlgebra.dong_fields
#print axioms VOA.SuperVertexOperatorAlgebra.L0_eigenvalue
-- the (-1)^F infrastructure, ε-generic Goddard, and super skew-symmetry
#print axioms VOA.ParityGrading.parityInvol_homog
#print axioms VOA.ParityGrading.koszulOp_homog
#print axioms VOA.ParityGrading.exists_parity_decomp
#print axioms VOA.SuperVertexAlgebra.goddard_pointwiseε
#print axioms VOA.SuperVertexAlgebra.goddard_uniquenessε
#print axioms VOA.SuperVertexOperatorAlgebra.creation_powε
#print axioms VOA.SuperVertexOperatorAlgebra.skewBase_vacuum
#print axioms VOA.SuperVertexOperatorAlgebra.skewDistε_eq_Y
#print axioms VOA.SuperVertexOperatorAlgebra.skew_modeε
-- reducing the super skew gate to a sign-free statement
#print axioms VOA.SuperVertexAlgebra.Y_apply_vacuum_parity
#print axioms VOA.SuperVertexAlgebra.goddard_pointwise_vacε
#print axioms VOA.SuperVertexOperatorAlgebra.applyVec_bracketDistε_factor
#print axioms VOA.SuperVertexOperatorAlgebra.skewVacLocalε_iff_signFree
#print axioms VOA.SuperVertexOperatorAlgebra.weakAssocLocε_of_signFree
#print axioms VOA.SuperVertexOperatorAlgebra.skew_modeε_of_signFree
-- the three examples that pin the conventions empirically
#print axioms VOA.FreeFermion.psi_anticomm
#print axioms VOA.FreeFermion.psi_localε
#print axioms VOA.BCGhosts.bc_anticomm
#print axioms VOA.BCGhosts.bc_localε
#print axioms VOA.BCGhosts.bfield_localε
#print axioms VOA.BetaGamma.pderiv_comm
#print axioms VOA.BetaGamma.beta_gamma_comm
#print axioms VOA.BetaGamma.beta_gamma_local
