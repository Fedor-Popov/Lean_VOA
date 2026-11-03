import VOA.Classification.COne.PlusRat3Gen
import VOA.Moonshine.PlusWeightTwo

/-! # Sign/half pairs and `V₁₆⁺` (`m = 8`)

* `top_eval_zero_of_rows`: if a Zhu element vanishes at every row of weight `c`, it kills every
  top vector of `L(0)`-eigenvalue `c`.
* The half rows: `o(H⁴) = o(H⁶) = 0`; the sign row: `o(H⁴) = o(H⁶) = 1`.
* The sign model `V_L⁻` has one-dimensional weight-two space (`m ≥ 3`).
* At `m = 8` the sign (bottom 1) and half (bottom 2) rows differ by one; the pair (half kernel,
  sign quotient) splits (`pairSplitting_half_sign_eight`), with the same three quadratic relations
  as for charged rows (here with `o(H⁴)x = o(H⁶)x = x`) and the `E`-virtual eigenvalue
  `1 + 34/434 ≠ 0`.
* `V2mPlus_stronglyRational_eight`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible

variable (m : ℕ) (hm : 1 ≤ m)

@[reducible] local instance zhuRing8 : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebra8 : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-! ## §1  Zhu elements vanishing on all rows of one weight -/

/-- If `z` vanishes at every row of weight `c`, it kills every top vector of eigenvalue `c`. -/
theorem top_eval_zero_of_rows (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {y : M} (hy : y ∈ Omega A) {c : ℂ}
    (hL : L0 A y = c • y) (z : VOA.A (V2mPlus m hm))
    (hz : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = c → chiT m hm hm2 j z = 0) :
    topEvaluation A y hy z = 0 := by
  classical
  set χ := chiT m hm hm2
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  have hdim : Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤ Fintype.card (Label m) := by
    rw [V2mPlus_zhu_finrank m hm hm2, card_label m hm]
  let e := characterAlgEquiv χ (chiT_injective m hm hm2) hdim
  have he_apply : ∀ r j, e r j = χ j r := fun _ _ => rfl
  set f := topEvaluation A y hy
  let ε : VOA.A (V2mPlus m hm) :=
    e.symm (fun j => if ((weight m j : ℚ) : ℂ) = c then 1 else 0)
  let ξ : VOA.A (V2mPlus m hm) :=
    e.symm (fun j => if ((weight m j : ℚ) : ℂ) = c then 0 else (χ j (generator m hm 0) - c)⁻¹)
  have hω : f (generator m hm 0 - algebraMap ℂ _ c) = 0 := by
    rw [map_sub, topEvaluation_omega m hm A hy, Algebra.algebraMap_eq_smul_one, map_smul,
      topEvaluation_one, hL, sub_self]
  have hfac : (1 : VOA.A (V2mPlus m hm)) - ε = ξ * (generator m hm 0 - algebraMap ℂ _ c) := by
    apply e.injective
    funext j
    rw [map_sub, map_one, map_mul, map_sub, AlgEquiv.commutes, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
    simp only [Pi.sub_apply, Pi.one_apply, Pi.mul_apply, Pi.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, he_apply]
    have hwj := hasValues_omega m hm (chiT_hasValues m hm hm2 j)
    by_cases hj : ((weight m j : ℚ) : ℂ) = c
    · rw [if_pos hj, if_pos hj]; simp
    · rw [if_neg hj, if_neg hj, sub_zero]
      have hne : χ j (generator m hm 0) - c ≠ 0 := by
        rw [hwj, sub_ne_zero]; exact hj
      exact (inv_mul_cancel₀ hne).symm
  have hε : f ε = y := by
    have h1 : f (1 - ε) = 0 := by
      rw [hfac]
      obtain ⟨s, hs⟩ := VOA.mk_surjective (V2mPlus m hm) ξ
      rw [← hs, topEvaluation_mk_mul, hω, map_zero]
    rw [map_sub, topEvaluation_one, sub_eq_zero] at h1
    exact h1.symm
  have hzε : z * ε = 0 := by
    apply e.injective
    funext j
    rw [map_mul, map_zero, AlgEquiv.apply_symm_apply]
    simp only [Pi.mul_apply, Pi.zero_apply, he_apply]
    by_cases hj : ((weight m j : ℚ) : ℂ) = c
    · rw [if_pos hj, hz j hj, zero_mul]
    · rw [if_neg hj, mul_zero]
  obtain ⟨a, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) z
  have h2 : f (VOA.mk (V2mPlus m hm) a * ε) = f (VOA.mk (V2mPlus m hm) a) := by
    rw [topEvaluation_mk_mul, hε, topEvaluation_mk]
  rw [← h2, hzε, map_zero]

/-! ## §2  The half rows and the sign row -/

/-- `H⁴` and `H⁶` vanish at both half rows. -/
theorem chiT_half_HP_zero (hm2 : 2 ≤ m) (i : Fin 8) (hi : i = 2 ∨ i = 3) (t : ℕ)
    (ht : t = 2 ∨ t = 3) :
    chiT m hm hm2 (.inr i) (VOA.mk (V2mPlus m hm) (HP m hm t)) = 0 := by
  set σ : ℂ := if i = 2 then 1 else -1 with hσdef
  have hσ : σ * σ = 1 := by rcases hi with rfl | rfl <;> simp [hσdef]
  let N := resN m hm (latticeModule m hm m)
  have he : ((((m : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ) : ℂ) = (m : ℂ) / 4 := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast; field_simp
  have hl : IsLowestWeight N ((m : ℂ) / 4) := by
    rw [← he]; exact latticeModule_isLowestWeight m hm m (by simp)
  have hlat : IsLowestWeight (latticeModule m hm m) ((m : ℂ) / 4) := by
    rw [← he]; exact latticeModule_isLowestWeight m hm m (by simp)
  have hx := halfVector_mem m hm σ
  have hΩ := lowest_mem_Omega m hm N hl hx
  set χ := chiT m hm hm2 (.inr i)
  have hχ := chiT_hasValues m hm hm2 (.inr i)
  have g0 : oMod N (gP m hm 0) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • halfVector m σ := by
    rw [hχ.1]
    change oMod N (V2mPlus m hm).conformalVector _ = _
    rw [oMod_conformalVector, N.L0_weight _ _ hx]
    congr 1
    rcases hi with rfl | rfl <;> simp [values, exceptional]
  have g1 : oMod N (gP m hm 1) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • halfVector m σ := by
    rw [hχ.2.1]
    change oMod N (WP m hm) _ = _
    rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe, oMod_W_V2m m hm _ hl hx]
    congr 1
    rcases hi with rfl | rfl <;> simp [values, exceptional] <;> ring
  have g2 : oMod N (gP m hm 2) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • halfVector m σ := by
    rw [hχ.2.2]
    change oMod N (EP m hm) _ = _
    rw [halfVector_E m hm σ hσ]
    congr 1
    rcases hi with rfl | rfl <;> simp [hσdef, values, exceptional]
  have hc := topEvaluation_eq_char m hm hm2 N.toWeakModule hΩ χ (by
    intro j; rw [topEvaluation_mk_eq_oMod m hm N hΩ (gP_mem_grading m hm j)]
    fin_cases j
    exacts [g0, g1, g2]) (VOA.mk (V2mPlus m hm) (HP m hm t))
  have hgr := HP_mem_grading m hm t (by omega) (by omega)
  rw [topEvaluation_mk_eq_oMod m hm N hΩ hgr, oMod_resN m hm _ hgr,
    hasN_HP m hm t (by omega) (by omega)] at hc
  have h0 : oMod (latticeModule m hm m) (ls m (HR t)) (halfVector m σ) = 0 := by
    rcases ht with rfl | rfl
    · exact oMod_eq_zero_of_mem_O _ hlat (H4_mem_O m hm) hx
    · exact oMod_eq_zero_of_mem_O _ hlat (H6_mem_O m hm) hx
  rw [h0] at hc
  rcases smul_eq_zero.mp hc.symm with h | h
  · exact h
  · exact absurd h (halfVector_ne_zero m σ)

theorem signVector_HP (t : ℕ) (ht : t = 2 ∨ t = 3) :
    oMod (signModule m hm) (HP m hm t) (signVector m hm) = signVector m hm := by
  have hgr := HP_mem_grading m hm t (by omega) (by omega)
  apply Subtype.ext
  rw [oMod_homogeneous _ hgr]
  change (V2m m hm).smul ((HP m hm t : VP m hm) : LatModuleGen (latP m)) _
    (bosonState (latP m) (a0 m)) = bosonState (latP m) (a0 m)
  rw [hasN_HP m hm t (by omega) (by omega), bosonState_eq_evR, ls, V2m_smul_evR_W,
    ← evR_normR]
  congr 2
  rcases ht with rfl | rfl
  · decide +kernel
  · decide +kernel

/-- `H⁴` and `H⁶` take the value `1` at the sign row. -/
theorem chiT_sign_HP (hm2 : 2 ≤ m) (t : ℕ) (ht : t = 2 ∨ t = 3) :
    chiT m hm hm2 (.inr 1) (VOA.mk (V2mPlus m hm) (HP m hm t)) = 1 := by
  set N := signModule m hm
  have hl := signModule_isLowestWeight m hm
  have hx := signVector_mem m hm
  have hΩ := lowest_mem_Omega m hm N hl hx
  set χ := chiT m hm hm2 (.inr 1)
  have hχ := chiT_hasValues m hm hm2 (.inr 1)
  have g0 : oMod N (gP m hm 0) (signVector m hm) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • signVector m hm := by
    rw [hχ.1]
    change oMod N (V2mPlus m hm).conformalVector _ = _
    rw [oMod_conformalVector, N.L0_weight _ _ hx]
    congr 1
  have g1 : oMod N (gP m hm 1) (signVector m hm) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • signVector m hm := by
    rw [hχ.2.1]
    change oMod N (WP m hm) _ = _
    rw [signVector_W]
    congr 1
  have g2 : oMod N (gP m hm 2) (signVector m hm) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • signVector m hm := by
    rw [hχ.2.2]
    change oMod N (EP m hm) _ = _
    rw [signVector_E m hm hm2]
    simp [values, exceptional]
  have hc := topEvaluation_eq_char m hm hm2 N.toWeakModule hΩ χ (by
    intro j; rw [topEvaluation_mk_eq_oMod m hm N hΩ (gP_mem_grading m hm j)]
    fin_cases j
    exacts [g0, g1, g2]) (VOA.mk (V2mPlus m hm) (HP m hm t))
  rw [topEvaluation_mk_eq_oMod m hm N hΩ (HP_mem_grading m hm t (by omega) (by omega)),
    signVector_HP m hm t ht] at hc
  have h2 : (1 - χ (VOA.mk (V2mPlus m hm) (HP m hm t))) • signVector m hm = 0 := by
    rw [sub_smul, one_smul, ← hc, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · linear_combination -h
  · exact absurd h (signVector_ne_zero m hm)

/-! ## §3  The sign model has a one-dimensional weight-two space (`m ≥ 3`) -/

theorem fock_weight_two_mem_span {p : FockN (rank (latP m))}
    (hp : p ∈ gradingWN (rank (latP m)) 2) :
    p ∈ Submodule.span ℂ {(X ((1 : ℕ), a0 m) : FockN (rank (latP m))),
      X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)} := by
  classical
  have ha : ∀ a : Fin (rank (latP m)), a = a0 m := by
    intro a
    apply Fin.ext
    have h1 := a.isLt
    have h2 : rank (latP m) = 1 := rank_latP m
    simp only [a0]
    omega
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight weightFnN d = 2 := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [show monomial d (coeff d p) = coeff d p • (monomial d (1 : ℂ) : FockN (rank (latP m))) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  apply Submodule.smul_mem
  rcases weight_eq_two (rank (latP m)) d hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · rw [ha a]
    exact Submodule.subset_span (Set.mem_insert _ _)
  · rw [ha a, ha b, show (monomial (Finsupp.single ((0 : ℕ), a0 m) 1 + Finsupp.single ((0 : ℕ), a0 m) 1)
        (1 : ℂ) : FockN (rank (latP m))) = X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) by
      show _ = monomial _ (1 : ℂ) * monomial _ (1 : ℂ)
      rw [monomial_mul, mul_one]]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

theorem V2m_grading_two (hm3 : 3 ≤ m) {v : LatModuleGen (latP m)} (hv : v ∈ (V2m m hm).grading 2) :
    ∃ q ∈ gradingWN (rank (latP m)) 2, v = latStateGen (latP m) q 0 := by
  rw [V2m_grading_eq] at hv
  have hle : gradingLatGen (latP m) 2 ≤ bigradα (latP m) (2, 0) := by
    apply iSup_le
    intro α
    change ℤ at α
    by_cases hα : α = 0
    · subst hα
      have h0 : LatGen.halfNorm (latP m) (0 : ℤ) = 0 := by
        simp only [LatGen.halfNorm]; rw [latP_form]; simp
      rw [h0, sub_zero]
      exact le_rfl
    · rw [bigradα_eq_bot_of_neg (latP m) α]
      · exact bot_le
      · have hhn : LatGen.halfNorm (latP m) α = m * (α * α) := by
          simp only [LatGen.halfNorm]
          rw [latP_form]
          rw [show 2 * (m : ℤ) * α * α = 2 * (m * (α * α)) by ring]
          simp
        rw [hhn]
        have hα' : α ≠ 0 := hα
        have hsq : 1 ≤ α * α := by
          rcases lt_or_gt_of_ne hα' with h | h <;> nlinarith
        have hmZ : (3 : ℤ) ≤ m := by exact_mod_cast hm3
        nlinarith
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp (hle hv)
  refine ⟨q, ?_, by rw [mkEα_apply]; rfl⟩
  rw [gradingZN_of_nonneg (by norm_num)] at hq; exact hq

theorem signLm_coe :
    ((mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) 0 (signVector m hm) :
      (signSubmodule m hm).carrier) : LatModuleGen (latP m)) =
      latStateGen (latP m) (X ((1 : ℕ), a0 m)) 0 := by
  change (V2m m hm).smul ((V2mPlus m hm).conformalVector : LatModuleGen (latP m)) 0
    (bosonState (latP m) (a0 m)) = _
  rw [omega_coe, bosonState_eq_evR, V2m_smul_evR_W, ← evR_normR,
    show normR (polyActW omR (-0 - 1) [(1, [0])]) = [(1, [1])] by decide +kernel]
  congr 1
  simp [evalRaw, evalWord]

/-- Every weight-two vector of the sign model is a multiple of `L(-1)e`. -/
theorem sign_weight_two (hm3 : 3 ≤ m) {w : (signSubmodule m hm).carrier}
    (hw : w ∈ (signModule m hm).weight 2) :
    ∃ c : ℂ, w = c • mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) 0 (signVector m hm) := by
  have hw' : (w : LatModuleGen (latP m)) ∈ (V2m m hm).grading 2 := by
    change (w : LatModuleGen (latP m)) ∈ adjWeight (V2m m hm) 2 at hw
    rw [show (2 : ℂ) = ((2 : ℤ) : ℂ) by norm_num, adjWeight_cast] at hw
    exact hw
  obtain ⟨q, hq, hwq⟩ := V2m_grading_two m hm hm3 hw'
  obtain ⟨c1, c2, hqc⟩ := Submodule.mem_span_pair.mp (fock_weight_two_mem_span m hq)
  have hθ := (sign_mem m hm _).mp w.2
  rw [hwq, thetaLat_latStateGen, neg_zero, ← hqc] at hθ
  have hσ : sigmaN (rank (latP m)) (c1 • X ((1 : ℕ), a0 m) + c2 • (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)))
      = -(c1 • X ((1 : ℕ), a0 m)) + c2 • (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)) := by
    rw [map_add, map_smul, map_smul, sigmaN_mul, sigmaN_X, sigmaN_X, neg_mul_neg, smul_neg]
  rw [hσ] at hθ
  have hc2 : c2 = 0 := by
    have h1 := congrArg (coordEα (latP m) 0) hθ
    simp only [latStateGen, ← TensorProduct.neg_tmul, coordEα_apply, if_true] at h1
    have h2 : (2 * c2) • (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) : FockN (rank (latP m))) = 0 := by
      rw [mul_smul, two_smul]
      linear_combination (norm := module) h1
    rcases smul_eq_zero.mp h2 with h | h
    · linear_combination h / 2
    · exact absurd h (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  subst hc2
  refine ⟨c1, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, signLm_coe, hwq, ← hqc, zero_smul, add_zero, latStateGen_csmul]

/-! ## §4  `m = 8`: the half kernel / sign quotient pairs -/

section Eight
variable (hm : 1 ≤ 8)

theorem two_le_eight : 2 ≤ 8 := by norm_num

theorem weight_eight_one (j : Label 8) : weight 8 j = 1 → j = .inr 1 := by
  revert j; decide +kernel

theorem weight_eight_two (j : Label 8) : weight 8 j = 2 → j = .inr 2 ∨ j = .inr 3 := by
  revert j; decide +kernel

theorem uniq_eight_one : ∀ j : Label 8, ((weight 8 j : ℚ) : ℂ) = (1 : ℂ) → j = .inr 1 := by
  intro j h
  apply weight_eight_one
  have h' : ((weight 8 j : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by rw [h]; norm_num
  exact Rat.cast_injective h'

theorem rows_eight_two : ∀ j : Label 8, ((weight 8 j : ℚ) : ℂ) = (2 : ℂ) → j = .inr 2 ∨ j = .inr 3 := by
  intro j h
  apply weight_eight_two
  have h' : ((weight 8 j : ℚ) : ℂ) = ((2 : ℚ) : ℂ) := by rw [h]; norm_num
  exact Rat.cast_injective h'

/-- On a top vector of weight `2` (the half rows), `o(H⁴)` and `o(H⁶)` vanish. -/
theorem omega_route_eight {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus 8 hm) M)
    {w : M} (hwΩ : w ∈ Omega A) (hwL : L0 A w = (2 : ℂ) • w) (t : ℕ) (ht : t = 2 ∨ t = 3) :
    mode (A.YM (HP 8 hm t)) ((2 * t : ℕ) - 1 : ℤ) w = 0 := by
  have h := top_eval_zero_of_rows 8 hm two_le_eight A hwΩ hwL (VOA.mk (V2mPlus 8 hm) (HP 8 hm t))
    (by
      intro j hj
      rcases rows_eight_two j hj with rfl | rfl
      · exact chiT_half_HP_zero 8 hm two_le_eight 2 (Or.inl rfl) t ht
      · exact chiT_half_HP_zero 8 hm two_le_eight 3 (Or.inr rfl) t ht)
  rw [topEvaluation_mk, oLevW_homogeneous A 0 (HP_mem_grading 8 hm t (by omega) (by omega)),
    add_zero] at h
  exact h

/-- **(half kernel, sign quotient) splits at `m = 8`**, for both half rows. -/
theorem pairSplitting_half_sign_eight (i : Fin 8) (hi : i = 2 ∨ i = 3) :
    PairSplitting 8 hm (.inr i) (.inr 1) := by
  intro M _ _ A P hP hQ hb ht
  have hwi : ((weight 8 (.inr i) : ℚ) : ℂ) = 2 := by
    have h : weight 8 (.inr i) = 2 := by
      rcases hi with rfl | rfl
      · decide +kernel
      · decide +kernel
    rw [h]; norm_num
  have hw1 : ((weight 8 (.inr 1) : ℚ) : ℂ) = 1 := by norm_num [weight]
  rw [hwi] at hb
  rw [hw1] at ht
  have hlow : ∀ μ : ℂ, μ.re < (1 : ℂ).re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0 := by
    intro μ hμ v hv
    have hvP : v ∈ P := by
      by_contra h
      have hw : FactorWeight A P ⊤ μ := fun hT => h (hT ⟨Submodule.mem_top, hv⟩)
      have := ht.2 μ hw
      linarith
    exact kernel_generalized_below_bottom_eq_zero A P _ hb hvP hv (by norm_num at hμ ⊢; linarith)
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift (V2mPlus_c2Cofinite 8 hm) A P hP
    (show (2 : ℂ) ≠ 1 by norm_num) hb ht
  have hx0 : x ≠ 0 := fun h => hxP (h ▸ P.zero_mem)
  have hxg : x ∈ (L0 A).maxGenEigenspace 1 :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  have hxΩ : x ∈ Omega A := by
    intro β v hv n hn
    apply hlow _ _ _ (mode_mem_maxGenEigenspace A hv n hxg)
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show β - n - 1 ≤ -1 by omega)
    rw [Complex.add_re, Complex.intCast_re, Complex.one_re]
    linarith
  -- the character of `x`
  have hχx := top_char_unique 8 hm two_le_eight A hxΩ hxL (.inr 1) uniq_eight_one
  have hzero : ∀ {k : ℤ} {a : VP 8 hm}, a ∈ (V2mPlus 8 hm).grading k →
      mode (A.YM a) (k - 1) x = chiT 8 hm two_le_eight (.inr 1) (VOA.mk (V2mPlus 8 hm) a) • x := by
    intro k a ha
    have h := hχx (VOA.mk (V2mPlus 8 hm) a)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h
    exact h
  have h4 : mode (A.YM (HP 8 hm 2)) 3 x = (1 : ℂ) • x := by
    have h := hzero (HP_mem_grading 8 hm 2 (by norm_num) (by norm_num))
    rw [chiT_sign_HP 8 hm two_le_eight 2 (Or.inl rfl)] at h
    simpa using h
  have h6 : mode (A.YM (HP 8 hm 3)) 5 x = (1 : ℂ) • x := by
    have h := hzero (HP_mem_grading 8 hm 3 (by norm_num) (by norm_num))
    rw [chiT_sign_HP 8 hm two_le_eight 3 (Or.inr rfl)] at h
    simpa using h
  have hE : mode (A.YM (EP 8 hm)) (((8 : ℕ) : ℤ) - 1) x = 0 := by
    have h := hzero (EP_mem_grading 8 hm)
    have hv := (chiT_hasValues 8 hm two_le_eight (.inr 1)).2.2
    change chiT 8 hm two_le_eight (.inr 1) (VOA.mk (V2mPlus 8 hm) (EP 8 hm)) = _ at hv
    rw [hv] at h
    simp [values, exceptional] at h
    simpa using h
  -- the lattice model: the sign module
  set B := (signModule 8 hm).toWeakModule
  set e := signVector 8 hm
  have heΩ : e ∈ Omega B := lowest_mem_Omega 8 hm _ (signModule_isLowestWeight 8 hm) (signVector_mem 8 hm)
  have heL : L0 B e = (1 : ℂ) • e := (signModule 8 hm).L0_weight _ _ (signVector_mem 8 hm)
  have hχe := top_char_unique 8 hm two_le_eight B heΩ heL (.inr 1) uniq_eight_one
  have htrans : ∀ {k : ℤ} {t : VP 8 hm}, t ∈ (V2mPlus 8 hm).grading k → ∃ c : ℂ,
      mode (A.YM t) (k - 2) x - c • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x ∈ Omega A := by
    intro k t htk
    have hte : mode ((signModule 8 hm).YM t) (k - 2) e ∈ (signModule 8 hm).weight 2 := by
      have h := mode_mem_weight (signModule 8 hm) htk (signVector_mem 8 hm) (k - 2)
      have hc : (1 : ℂ) + (k : ℂ) - ((k - 2 : ℤ) : ℂ) - 1 = 2 := by push_cast; ring
      rwa [hc] at h
    obtain ⟨c, hc⟩ := sign_weight_two 8 hm (by norm_num) hte
    exact ⟨c, transfer_general A B (chiT 8 hm two_le_eight (.inr 1)) hxΩ heΩ hχx hχe
      (signVector_ne_zero 8 hm) hxL hlow htk hc⟩
  have hL1 : ∀ w : M, w ∈ Omega A → mode (A.YM (V2mPlus 8 hm).conformalVector) 2 w = 0 :=
    fun w hw => Omega_mode_vanish hw (V2mPlus 8 hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
  have hp1 := L1G_p1 8 hm two_le_eight A hxΩ hxL
  have hg2 := HP_mem_grading 8 hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading 8 hm 3 (by norm_num) (by norm_num)
  -- `v = E₍₆₎x = 0`
  have hv0 : mode (A.YM (EP 8 hm)) (((8 : ℕ) : ℤ) - 2) x = 0 := by
    obtain ⟨cE, hw⟩ := htrans (EP_mem_grading 8 hm)
    have hcE : cE = 0 := by
      have h := hL1 _ hw
      rw [map_sub, map_smul, L1G_v 8 hm A hxΩ hE, hp1, smul_smul, zero_sub, neg_eq_zero] at h
      rcases smul_eq_zero.mp h with h | h
      · linear_combination h / 2
      · exact absurd h hx0
    subst hcE
    rw [zero_smul, sub_zero] at hw
    have hwL := L0G_degOne 8 hm A (EP_mem_grading 8 hm) hxL
    rw [show (1 : ℂ) + 1 = 2 by norm_num] at hwL
    have hR := omega_route_eight hm A hw hwL 2 (Or.inl rfl)
    rw [show ((2 * 2 : ℕ) : ℤ) - 1 = 3 by norm_num] at hR
    have hv := oG_H4_v 8 hm A hxΩ hxL h4 hE
    rw [hR, smul_zero] at hv
    rcases smul_eq_zero.mp hv.symm with h | h
    · norm_num at h
    · exact h
  -- `p₂ = (7/3) p₁`
  have hp2 : mode (A.YM (HP 8 hm 2)) 2 x = (7 / 3 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x := by
    obtain ⟨c2, hw2⟩ := htrans hg2
    obtain ⟨c3, hw3⟩ := htrans hg3
    rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hw2
    rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hw3
    have hc2 : c2 = 7 / 3 := by
      have h := hL1 _ hw2
      rw [map_sub, map_smul, L1G_p2 8 hm A hxΩ hxL h4, hp1, smul_smul, ← sub_smul] at h
      rcases smul_eq_zero.mp h with h | h
      · linear_combination -h / 2
      · exact absurd h hx0
    have hc3 : c3 = 31 / 5 := by
      have h := hL1 _ hw3
      rw [map_sub, map_smul, L1G_p3 8 hm A hxΩ hxL h4 h6, hp1, smul_smul, ← sub_smul] at h
      rcases smul_eq_zero.mp h with h | h
      · linear_combination -h / 2
      · exact absurd h hx0
    subst hc2 hc3
    have hLp1 := L0G_degOne 8 hm A (V2mPlus 8 hm).conformal_mem hxL
    have hLp2 := L0G_degOne 8 hm A hg2 hxL
    have hLp3 := L0G_degOne 8 hm A hg3 hxL
    rw [show ((2 : ℤ) - 2) = 0 by norm_num, show (1 : ℂ) + 1 = 2 by norm_num] at hLp1
    rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num, show (1 : ℂ) + 1 = 2 by norm_num] at hLp2
    rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num, show (1 : ℂ) + 1 = 2 by norm_num] at hLp3
    have hwL2 : L0 A (mode (A.YM (HP 8 hm 2)) 2 x - (7 / 3 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x)
        = (2 : ℂ) • (mode (A.YM (HP 8 hm 2)) 2 x - (7 / 3 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x) := by
      rw [map_sub, map_smul, hLp1, hLp2, smul_sub, smul_comm]
    have hwL3 : L0 A (mode (A.YM (HP 8 hm 3)) 4 x - (31 / 5 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x)
        = (2 : ℂ) • (mode (A.YM (HP 8 hm 3)) 4 x - (31 / 5 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x) := by
      rw [map_sub, map_smul, hLp1, hLp3, smul_sub, smul_comm]
    have hR1 := omega_route_eight hm A hw2 hwL2 2 (Or.inl rfl)
    have hR2 := omega_route_eight hm A hw3 hwL3 2 (Or.inl rfl)
    have hR3 := omega_route_eight hm A hw2 hwL2 3 (Or.inr rfl)
    rw [show ((2 * 2 : ℕ) : ℤ) - 1 = 3 by norm_num] at hR1 hR2
    rw [show ((2 * 3 : ℕ) : ℤ) - 1 = 5 by norm_num] at hR3
    have e1 := commG_H4_p2 8 hm A h4
    have e2 := commG_H4_p3 8 hm A h4
    have e3 := commG_H6_p2 8 hm A h6
    have f1 := oG_H4_p1 8 hm A h4
    have f2 := oG_H6_p1 8 hm A h6
    change _ = (1 / 15 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x + _ + _ at e1
    change _ = (-1 / 35 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x + _ + _ + _ at e2
    change _ = (-1 / 21 : ℂ) • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x + _ - _ + _ at e3
    rw [map_sub, map_smul, e1, f1] at hR1
    rw [map_sub, map_smul, e2, f1] at hR2
    rw [map_sub, map_smul, e3, f2] at hR3
    linear_combination (norm := module) (5 : ℂ) • hR1 - (15 / 8 : ℂ) • hR2 + (9 / 8 : ℂ) • hR3
  -- the degree-one line
  have hline : degOneSpan A x ≤ Submodule.span ℂ {mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x} := by
    set G := Set.range (gP 8 hm)
    have hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ (V2mPlus 8 hm).grading j := by
      rintro g ⟨j, rfl⟩
      exact ⟨_, by fin_cases j <;> simp [wtP], gP_mem_grading 8 hm j⟩
    have hST : ScalarTop A x := ⟨hxΩ, fun j c hc => ⟨_, hzero hc⟩⟩
    have hraise := raise_mem hG (top_eq_span_iterProd 8 hm two_le_eight) hST
    set L := Submodule.span ℂ {mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x}
    have hpL : mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x ∈ L := Submodule.mem_span_singleton_self _
    have hgen : raiseSpan A G x ≤ L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, g, ⟨i', rfl⟩, hgj, rfl⟩
      have hwt := gP_mem_grading 8 hm i'
      by_cases hj : j = wtP 8 i'
      · subst hj
        fin_cases i'
        · change mode (A.YM (V2mPlus 8 hm).conformalVector) ((2 : ℤ) - 2) x ∈ L
          rw [show (2 : ℤ) - 2 = 0 by norm_num]; exact hpL
        · change mode (A.YM (WP 8 hm)) ((4 : ℤ) - 2) x ∈ L
          rw [WP_eq_comb 8 hm]
          simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
          have h2 : mode (A.YM (HP 8 hm 2)) (4 - 2 - ((0 : ℕ) : ℤ)) x =
              (7 / 3 : ℂ) • mode (A.YM (HP 8 hm 1)) 0 x := by
            rw [show (4 : ℤ) - 2 - ((0 : ℕ) : ℤ) = 2 by norm_num]
            exact hp2
          rw [h2, show (4 : ℤ) - 2 - ((2 : ℕ) : ℤ) = 0 by norm_num]
          change _ • (_ • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x) +
            (_ • mode (A.YM (V2mPlus 8 hm).conformalVector) 0 x + 0) ∈ L
          exact L.add_mem (L.smul_mem _ (L.smul_mem _ hpL)) (L.add_mem (L.smul_mem _ hpL) L.zero_mem)
        · change mode (A.YM (EP 8 hm)) (((8 : ℕ) : ℤ) - 2) x ∈ L
          rw [hv0]; exact L.zero_mem
      · rw [eq_zero_of_mem_two_gradings hj hgj hwt, map_zero, mode_zero, LinearMap.zero_apply]
        exact L.zero_mem
    apply Submodule.span_le.mpr
    rintro _ ⟨β, a, ha, rfl⟩
    exact hgen (hraise β a ha)
  -- the splitting
  apply (exists_cyclic_lift_iff_complement A P hQ 1 ht).mp
  refine ⟨x, hxg, hxP, ?_⟩
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  have hyg : y ∈ (L0 A).maxGenEigenspace (1 + ((1 : ℤ) : ℂ)) := by
    rw [show (1 : ℂ) + ((1 : ℤ) : ℂ) = 2 by push_cast; norm_num]; exact hy.2
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0' x,
    no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite 8 hm) A hxg 1 hyg]
  intro hyD
  have hyL := hline (degreeSpan_one_le A hxL hyD)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyL
  have hPm := PlusRat2Dual.mem_P_mode A P (V2mPlus 8 hm).conformalVector 2 hy.1
  rw [map_smul, hp1, smul_smul] at hPm
  by_cases hc : c = 0
  · subst hc; rw [zero_smul] at hy0'; exact hy0' rfl
  · apply hxP
    have hc' : c * (2 * (1 : ℂ)) ≠ 0 := mul_ne_zero hc (by norm_num)
    have := P.smul_mem ((algebraMap ℂ (modeAlg A)) (c * (2 * (1 : ℂ)))⁻¹) hPm
    rw [algebraMap_smul, smul_smul, inv_mul_cancel₀ hc', one_smul] at this
    exact this

end Eight

/-! ## §5  `V₁₆⁺` is strongly rational -/

theorem positivePairs_eight_cert : ∀ p ∈ positivePairs 8,
    ((weight 8 p.1 = 0 ∧ weight 8 p.2 = 1) ∨ (weight 8 p.1 = 1 ∧ weight 8 p.2 = 0)) ∨
      p.1 = .inr 0 ∨ p = (.inl 1, .inl 5) ∨ p = (.inr 1, .inr 2) ∨ p = (.inr 1, .inr 3) := by
  decide +kernel

theorem weight_eight_c2 (j : Label 8) : weight 8 j = weight 8 (.inl 1) → j = .inl 1 := by
  revert j; decide +kernel

theorem weight_eight_c6 (j : Label 8) : weight 8 j = weight 8 (.inl 5) → j = .inl 5 := by
  revert j; decide +kernel

theorem weight_eight_gap : weight 8 (.inl 5) = weight 8 (.inl 1) + 1 := by decide +kernel

/-- **`V₁₆⁺ = V_{√16 ℤ}⁺` is strongly rational.** -/
theorem V2mPlus_stronglyRational_eight (hm : 1 ≤ 8) : StronglyRational (V2mPlus 8 hm) := by
  apply V2mPlus_stronglyRational_of_unordered 8 hm (by norm_num)
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_eight_cert (i, j) hp with h | h | h | h | h
  · exact absurd h hvs
  · exact absurd h hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_one_both 8 hm (by norm_num) 1 5 weight_eight_gap
      weight_eight_c2 weight_eight_c6).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_swap 8 hm (by decide +kernel) (pairSplitting_half_sign_eight hm 2 (Or.inl rfl))
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_swap 8 hm (by decide +kernel) (pairSplitting_half_sign_eight hm 3 (Or.inr rfl))

end VOA.Classification.COne.PlusRat3
