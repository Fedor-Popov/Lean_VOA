import VOA.Classification.COne.OrbIcoVProbes
import VOA.Classification.COne.OrbIcoVSchurProbe

/-! Nonzero normalizations of the actual Casimir-separated probes. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational PlusC2Eval OrbIco OrbPrim OrbRat6 OrbIcoT

set_option maxHeartbeats 2000000 in
-- The existing small Schur-product certificate is evaluated only at one scalar.
theorem sc6_probe_sum : schurProbeSum sc6 = -1 / 309071606732292096000000 := by
  decide +kernel

theorem neutralProbe_wv_neutral : OrbOctaR.neutralProbe (wv 6 6) =
    (1 / 665280 : ℂ) * chargeCoord (latP 1) (-1 : ℤ) (LatMod.a0 1) ^ 36 *
      (-1 / 309071606732292096000000 : ℂ) := by
  rw [wv6_sc6, map_smul]
  change (1 / 665280 : ℂ) * firstProbe
    (coordEα (latP 1) 0 (latStateGen (latP 1) (shEval sc6) 0)) = _
  simp only [latStateGen, coordEα_apply, ite_true]
  rw [firstProbe_shEval sc6 36 sc6_degrees, sc6_probe_sum]
  push_cast
  ring

theorem neutralProbe_wv_charge (i : ℕ) (hi : i ≠ 6) :
    OrbOctaR.neutralProbe (wv 6 i) = 0 := by
  classical
  rw [wv, map_smul]
  obtain ⟨P, hP, he⟩ := vn_bigrad 6 i
  rw [← he]
  change cnk 6 i * firstProbe (coordEα (latP 1) 0
    (latStateGen (latP 1) P ((6 : ℤ) - (i : ℤ)))) = 0
  simp only [latStateGen, coordEα_apply]
  split_ifs with hd
  · exfalso
    apply hi
    change (0 : ℤ) = 6 - (i : ℤ) at hd
    omega
  · rw [map_zero, mul_zero]


theorem neutralProbe_Xico : OrbIcoS.neutralProbe Xico =
    f6 * OrbOctaR.neutralProbe (wv 6 6) := by
  change OrbOctaR.neutralProbe (Xico : Sp) = _
  rw [Xico_eq_Tb, fpoly_eq]
  simp only [← MvPolynomial.smul_eq_C_mul, map_add, map_smul,
    Tb_xy 12 0 6 rfl, Tb_xy 0 12 6 rfl,
    Tb_xy 10 2 6 rfl, Tb_xy 2 10 6 rfl,
    Tb_xy 8 4 6 rfl, Tb_xy 4 8 6 rfl, Tb_xy 6 6 6 rfl]
  simp only [neutralProbe_wv_charge 0 (by omega), neutralProbe_wv_charge 12 (by omega),
    neutralProbe_wv_charge 2 (by omega), neutralProbe_wv_charge 10 (by omega),
    neutralProbe_wv_charge 4 (by omega), neutralProbe_wv_charge 8 (by omega),
    smul_eq_mul, zero_add, add_zero, mul_zero]

theorem f6_ne_zero : f6 ≠ 0 := by
  intro h
  apply gp_ne_neg_two
  have hh : gp = -(1 / 2 : ℂ) := by
    dsimp [f6] at h
    linear_combination (1 / 88 : ℂ) * h
  have hbad := gp_sq'
  rw [hh] at hbad
  norm_num at hbad

theorem neutralProbe_Xico_ne_zero : OrbIcoS.neutralProbe Xico ≠ 0 := by
  rw [neutralProbe_Xico, neutralProbe_wv_neutral]
  refine mul_ne_zero f6_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) (by norm_num))
  apply pow_ne_zero
  rw [OrbOctaRC.chargeCoord_one]
  simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_ne_zero]
  exact PlusC2.cα_ne_zero 1 le_rfl

/-- Both measurement functionals are independent at every pair of tower levels. -/
theorem measurement_determinant_ne_zero (r q : ℕ) :
    vacuumProbe ((Wi.L (-2) ^ r) Wi.vacuum) * sixthProbe ((Wi.L (-2) ^ q) Xico) -
      sixthProbe ((Wi.L (-2) ^ r) Wi.vacuum) * vacuumProbe ((Wi.L (-2) ^ q) Xico) ≠ 0 := by
  rw [measurement_determinant]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) neutralProbe_Xico_ne_zero

end VOA.Classification.COne.OrbIcoV
