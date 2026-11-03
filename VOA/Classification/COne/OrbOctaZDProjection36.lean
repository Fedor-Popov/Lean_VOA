import VOA.Classification.COne.OrbOctaZDChannel36

/-! A nonzero intrinsic octahedral projection onto the weight-36 seed. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbOcta OrbC2b
  VOA.LatGen VOA.LatGen.Triplet MvPolynomial

noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

/-- The binary model of the next invariant primary. -/
theorem T2_I3sq : T2 (I3 * I3) =
    (-4 : ℂ) • wv 6 2 + (8 : ℂ) • wv 6 6 + (-4 : ℂ) • wv 6 10 := by
  have h : psi (I3 * I3) = (-4 : ℂ) • (X 0 ^ 10 * X 1 ^ 2) +
      (8 : ℂ) • (X 0 ^ 6 * X 1 ^ 6) + (-4 : ℂ) • (X 0 ^ 2 * X 1 ^ 10) := by
    rw [map_mul, psi_I3]
    have he : MvPolynomial.C Complex.I * MvPolynomial.C (-2 * eps1) *
        (MvPolynomial.C Complex.I * MvPolynomial.C (-2 * eps1) : P2) = -4 := by
      calc
        _ = (MvPolynomial.C Complex.I : P2) ^ 2 *
            MvPolynomial.C (-2 * eps1) ^ 2 := by ring
        _ = -4 := by rw [C_I_pow_two, C_eps_pow_two]; ring
    simp only [smul_eq_C_mul, map_neg, map_ofNat]
    linear_combination (X 0 ^ 5 * X 1 - X 0 * X 1 ^ 5) ^ 2 * he
  rw [T2_apply, h, map_add, map_add, map_smul, map_smul, map_smul,
    Tb_xy 10 2 6 rfl, Tb_xy 6 6 6 rfl, Tb_xy 2 10 6 rfl]

private theorem pair88 : V2v.smul (wv 4 8) (-5) (wv 4 8) = 0 := by
  rw [OrbOctaRC.wv4_eight_value]
  change V2v.smul (latChargeGen (latP 1) (-4 : ℤ)) (-5)
    (latStateGen (latP 1) (HeisenbergN.vacuumN _) (-4 : ℤ)) = 0
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_neg (by norm_num)]
  simp [latStateGen]

set_option maxHeartbeats 1000000 in
-- Assemble seven small channel projections in the normalized multiplet.
/-- The scalar is measured in the repository's fixed multiplet normalization. -/
theorem self_channel36_ambient :
    V2v.smul (T2 I4) (-5) (T2 I4) - (1359072 : ℂ) • T2 (I3 * I3) ∈
      lowerDesc V2v 36 := by
  let Φ := fun i j : ℕ => V2v.smul (wv 4 i) (-5) (wv 4 j) -
    ((-56628 / 7 : ℂ) * coeff36 i j) • wv 6 (i + j - 2)
  have hm (i j : ℕ) (h2 : 2 ≤ i + j) (h14 : i + j ≤ 14) (hi : i ≤ 8) (hj : j ≤ 8) :
      Φ i j ∈ lowerDesc V2v 36 := second44 (i + j) i j rfl h2 h14 hi hj
  have he : V2v.smul (T2 I4) (-5) (T2 I4) - (1359072 : ℂ) • T2 (I3 * I3) =
      (56 : ℂ) • Φ 0 4 + (56 : ℂ) • Φ 4 0 + (4 : ℂ) • Φ 0 8 + (4 : ℂ) • Φ 8 0 +
        (784 : ℂ) • Φ 4 4 + (56 : ℂ) • Φ 4 8 + (56 : ℂ) • Φ 8 4 := by
    rw [T2_I4, T2_I3sq]
    simp only [Φ, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
      PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, pair00, pair88, coeff36]
    norm_num
    module
  rw [he]
  repeat' apply Submodule.add_mem
  all_goals exact Submodule.smul_mem _ _ (hm _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num))

/-- The ambient channel descends to the actual fixed-point VOA. -/
theorem self_channel36 :
    OrbOctaR.W.smul OrbOctaR.X (-5) OrbOctaR.X -
      (1359072 : ℂ) • octaSeeds 2 ∈ lowerDesc OrbOctaR.W 36 := by
  have h := average_lowerDesc octa self_channel36_ambient
  rw [map_sub, map_smul, average_smul_T2 ⟨isA4Inv_I4, s3_I4⟩ ⟨isA4Inv_I4, s3_I4⟩] at h
  have ha : OrbC2.average octa (T2 (I3 * I3)) = Tav (I3 * I3) := by
    have hc := Tav_coe (show IsS4Inv (I3 * I3) from
      ⟨isA4Inv_mul isA4Inv_I3 isA4Inv_I3, by rw [map_mul, s3_I3, neg_mul_neg]⟩)
    rw [← hc, OrbC2.average_fixed]
  rw [ha] at h
  exact h

end VOA.Classification.COne.OrbOctaZD
