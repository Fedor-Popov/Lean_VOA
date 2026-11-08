import VOA.Moonshine.MoonshineLRM5Hecke
import VOA.Moonshine.MoonshineLRM5Poly
import VOA.Moonshine.MoonshineLRM5Invariance
import VOA.Moonshine.MoonshineLRM5Cosets
import VOA.Moonshine.MoonshineLRM5CosetMap
import VOA.Moonshine.MoonshineLRM5Replicable
import VOA.Moonshine.MoonshineLRM5KNZ
import VOA.Moonshine.MoonshineLRM5Product

/-! Axiom audit for the untwisted denominator identity (`MoonshineLRM5*`). -/

namespace VOA.Moonshine.ConwayNorton.M8

#print axioms qHeckeBlock
#print axioms qHeckeBlock_of_pos
#print axioms qHeckeSum
#print axioms qHeckeCoeff
#print axioms hasSum_qHeckeBlock
#print axioms hasSum_qHeckeSum

#print axioms PowerSeriesAbsConv
#print axioms powerSeriesEval
#print axioms PowerSeriesAbsConv.add
#print axioms powerSeriesEval_add
#print axioms PowerSeriesAbsConv.mul
#print axioms powerSeriesEval_mul
#print axioms powerSeriesAbsConv_C
#print axioms powerSeriesEval_C
#print axioms powerSeriesAbsConv_X
#print axioms powerSeriesEval_X
#print axioms PowerSeriesAbsConv.pow
#print axioms powerSeriesEval_pow
#print axioms PowerSeriesAbsConv.sum
#print axioms powerSeriesEval_sum
#print axioms powerSeriesAbsConv_qSeriesUnit
#print axioms powerSeriesEval_qSeriesUnit
#print axioms polyUnitSeries
#print axioms aeval_qSeriesLaurent_eq_single_mul
#print axioms powerSeriesAbsConv_polyUnitSeries
#print axioms powerSeriesEval_polyUnitSeries
#print axioms hasSum_mul_eval_qSeriesFun

#print axioms smul_invariant_of_S_T
#print axioms qHeckeBlock_vadd_one
#print axioms qHeckeSum_T_smul

#print axioms cosetMatrix
#print axioms heckePoint_S_smul_eq

#print axioms negInvMod
#print axioms negInvMod_cast
#print axioms negInvMod_lt
#print axioms dvd_negInvMod_mul_add_one
#print axioms eq_negInvMod
#print axioms coprime_of_dvd_mul_add_one
#print axioms heckeCosets
#print axioms cosetS
#print axioms CosetData.M_div_g
#print axioms cosetData_of_mem
#print axioms cosetS_mem
#print axioms cosetS_cosetS
#print axioms heckeVal
#print axioms heckeSumOf
#print axioms qHeckeSum_eq_heckeSumOf
#print axioms heckeVal_S_smul
#print axioms heckeSumOf_S_smul
#print axioms qHeckeSum_smul

#print axioms cJ
#print axioms isJDominated_cJ
#print axioms qSeriesFun_cJ
#print axioms qSeriesFun_cJ_smul
#print axioms hasSum_faberPoly_eval_sub
#print axioms exp_neg_pi_lt_half
#print axioms exists_smul_half_le_im
#print axioms norm_le_mul_of_invariant_hasSum
#print axioms eq_zero_of_invariant_hasSum
#print axioms replicationDefect
#print axioms hasSum_replicationDefect
#print axioms faberPoly_cJ_eval_eq_qHeckeSum
#print axioms coeff_faberPoly_cJ_eq_qHeckeCoeff

#print axioms derivative_map
#print axioms evalAtQSeries
#print axioms faberGen_map_generating
#print axioms knzCoeff
#print axioms knzSeries
#print axioms qInv
#print axioms coeff_ofPowerSeries_mk
#print axioms qSeriesLaurent_eq_qInv_add
#print axioms qInv_mul_ofPowerSeries_mk
#print axioms faberGen_map_eq_mul
#print axioms qInvGeom
#print axioms mul_qInvGeom
#print axioms knzLogCoeff
#print axioms knzLogSeries
#print axioms knzLogSeries_eq
#print axioms knz_log
#print axioms knzLogCoeff_cJ
#print axioms knz_log_J

#print axioms odeCoeff
#print axioms odeSol
#print axioms constantCoeff_odeSol
#print axioms odeSol_spec
#print axioms eq_of_ode
#print axioms odeSol_add
#print axioms charZero_laurentSeries
#print axioms ofPowerSeries_mk_zero
#print axioms coneLogCoeff
#print axioms coneLog
#print axioms constantCoeff_coneLog
#print axioms coneProd
#print axioms coneProd_spec
#print axioms constantCoeff_coneProd
#print axioms coneLog_add
#print axioms coneProd_add
#print axioms coneLog_cJ
#print axioms knz_product
#print axioms coneLog_eq_of_coneProd_eq
#print axioms coeff_coneLog
#print axioms coneProd_exponent_unique

end VOA.Moonshine.ConwayNorton.M8
