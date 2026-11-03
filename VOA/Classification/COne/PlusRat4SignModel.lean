import VOA.Classification.COne.PlusRat4Model
import VOA.Moonshine.LatticeGradedDim

/-! # The sign model `V_L⁻` at degree two (`m ≥ 4`)

* `V2m_grading_three`: weight-three vectors of `V_L` (`m ≥ 4`) lie in `M(1) ⊗ e⁰`.
* `fock_weight_three_mem_span`: the Fock weight-three space is spanned by `x₂`, `x₁x₀`, `x₀³`.
* `sign_weight_three`: a weight-three vector of `V_L⁻` lies in `span(x₂ ⊗ e⁰, x₀³ ⊗ e⁰)`
  (the even monomial `x₁x₀` is excluded by `θ`).
* `sign_topData`: the sign top as `TopData` (given that the sign row is the only row of weight 1).
* `sign_deg2`: every degree-two vector of the sign model is `a L(-1)²e + b L(-2)e`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

variable (m : ℕ) (hm : 1 ≤ m)

theorem fock_weight_three_mem_span {p : FockN (rank (latP m))}
    (hp : p ∈ gradingWN (rank (latP m)) 3) :
    p ∈ Submodule.span ℂ {(X ((2 : ℕ), a0 m) : FockN (rank (latP m))),
      X ((1 : ℕ), a0 m) * X ((0 : ℕ), a0 m),
      X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)} := by
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
  have hw : Finsupp.weight weightFnN d = 3 := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [show monomial d (coeff d p) = coeff d p • (monomial d (1 : ℂ) : FockN (rank (latP m))) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  apply Submodule.smul_mem
  rcases weight_eq_three (rank (latP m)) d hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
  · rw [ha a]
    exact Submodule.subset_span (Set.mem_insert _ _)
  · rw [ha a, ha b, show (monomial (Finsupp.single ((1 : ℕ), a0 m) 1 + Finsupp.single ((0 : ℕ), a0 m) 1)
        (1 : ℂ) : FockN (rank (latP m))) = X ((1 : ℕ), a0 m) * X ((0 : ℕ), a0 m) by
      show _ = monomial _ (1 : ℂ) * monomial _ (1 : ℂ)
      rw [monomial_mul, mul_one]]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · rw [ha a, ha b, ha c, show (monomial (Finsupp.single ((0 : ℕ), a0 m) 1 +
        Finsupp.single ((0 : ℕ), a0 m) 1 + Finsupp.single ((0 : ℕ), a0 m) 1)
        (1 : ℂ) : FockN (rank (latP m))) = X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) by
      show _ = monomial _ (1 : ℂ) * monomial _ (1 : ℂ) * monomial _ (1 : ℂ)
      rw [monomial_mul, monomial_mul, mul_one, mul_one]]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem V2m_grading_three (hm4 : 4 ≤ m) {v : LatModuleGen (latP m)} (hv : v ∈ (V2m m hm).grading 3) :
    ∃ q ∈ gradingWN (rank (latP m)) 3, v = latStateGen (latP m) q 0 := by
  rw [V2m_grading_eq] at hv
  have hle : gradingLatGen (latP m) 3 ≤ bigradα (latP m) (3, 0) := by
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
        have hmZ : (4 : ℤ) ≤ m := by exact_mod_cast hm4
        nlinarith
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp (hle hv)
  refine ⟨q, ?_, by rw [mkEα_apply]; rfl⟩
  rw [gradingZN_of_nonneg (by norm_num)] at hq; exact hq

/-- Weight-three vectors of the sign model lie in `span(x₂ ⊗ e⁰, x₀³ ⊗ e⁰)`. -/
theorem sign_weight_three (hm4 : 4 ≤ m) {w : (signSubmodule m hm).carrier}
    (hw : w ∈ (signModule m hm).weight 3) :
    (w : LatModuleGen (latP m)) ∈ Submodule.span ℂ {latStateGen (latP m) (X ((2 : ℕ), a0 m)) 0,
      latStateGen (latP m) (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)) 0} := by
  have hw' : (w : LatModuleGen (latP m)) ∈ (V2m m hm).grading 3 := by
    change (w : LatModuleGen (latP m)) ∈ adjWeight (V2m m hm) 3 at hw
    rw [show (3 : ℂ) = ((3 : ℤ) : ℂ) by norm_num, adjWeight_cast] at hw
    exact hw
  obtain ⟨q, hq, hwq⟩ := V2m_grading_three m hm hm4 hw'
  have hspan := fock_weight_three_mem_span m hq
  rw [Submodule.mem_span_insert] at hspan
  obtain ⟨c1, z, hz, rfl⟩ := hspan
  obtain ⟨c2, c3, hz'⟩ := Submodule.mem_span_pair.mp hz
  subst hz'
  have hθ := (sign_mem m hm _).mp w.2
  rw [hwq, thetaLat_latStateGen, neg_zero] at hθ
  have hσ : sigmaN (rank (latP m)) (c1 • X ((2 : ℕ), a0 m) + (c2 • (X ((1 : ℕ), a0 m) * X ((0 : ℕ), a0 m)) +
      c3 • (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)))) =
      -(c1 • X ((2 : ℕ), a0 m)) + (c2 • (X ((1 : ℕ), a0 m) * X ((0 : ℕ), a0 m)) -
        c3 • (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m))) := by
    rw [map_add, map_add, map_smul, map_smul, map_smul, sigmaN_mul, sigmaN_mul, sigmaN_mul,
      sigmaN_X, sigmaN_X, sigmaN_X]
    rw [neg_mul_neg, neg_mul_neg]
    simp only [smul_neg, mul_neg]
    abel
  rw [hσ] at hθ
  have hc2 : c2 = 0 := by
    have h1 := congrArg (coordEα (latP m) 0) hθ
    simp only [latStateGen, ← TensorProduct.neg_tmul, coordEα_apply, if_true] at h1
    have h2 : (2 * c2) • (X ((1 : ℕ), a0 m) * X ((0 : ℕ), a0 m) : FockN (rank (latP m))) = 0 := by
      rw [mul_smul, two_smul]
      linear_combination (norm := module) h1
    rcases smul_eq_zero.mp h2 with h | h
    · linear_combination h / 2
    · exact absurd h (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  subst hc2
  rw [hwq]
  apply Submodule.mem_span_pair.mpr
  refine ⟨c1, c3, ?_⟩
  rw [zero_smul, zero_add]
  simp [latStateGen, TensorProduct.add_tmul, TensorProduct.smul_tmul']

variable (hm2 : 2 ≤ m)

/-- The sign top as `TopData` (the sign row the only row of weight `1`). -/
theorem sign_topData (hm3 : 3 ≤ m)
    (huniq1 : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = 1 → j = .inr 1) :
    TopData (signModule m hm).toWeakModule (chiT m hm hm2 (.inr 1)) 1 (signVector m hm) where
  omega := lowest_mem_Omega m hm _ (signModule_isLowestWeight m hm) (signVector_mem m hm)
  char := top_char_unique m hm hm2 _ _ ((signModule m hm).L0_weight _ _ (signVector_mem m hm))
    (.inr 1) huniq1
  L0 := (signModule m hm).L0_weight _ _ (signVector_mem m hm)
  line := by
    intro j c hc
    have hte : mode ((signModule m hm).YM c) (j - 2) (signVector m hm) ∈ (signModule m hm).weight 2 := by
      have h := mode_mem_weight (signModule m hm) hc (signVector_mem m hm) (j - 2)
      have hc' : (1 : ℂ) + (j : ℂ) - ((j - 2 : ℤ) : ℂ) - 1 = 2 := by push_cast; ring
      rwa [hc'] at h
    exact sign_weight_two m hm hm3 hte

include hm2 in
/-- Every degree-two vector of the sign model is `a L(-1)²e + b L(-2)e` (`m ≥ 4`). -/
theorem sign_deg2 (hm4 : 4 ≤ m) {k : ℤ} {t : VP m hm} (ht : t ∈ (V2mPlus m hm).grading k) :
    ∃ a b : ℂ, mode ((signModule m hm).YM t) (k - 3) (signVector m hm) =
      a • mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) 0
          (mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) 0 (signVector m hm)) +
        b • mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) (-1) (signVector m hm) := by
  have hw : ∀ {j : ℤ} {c : VP m hm}, c ∈ (V2mPlus m hm).grading j →
      mode ((signModule m hm).YM c) (j - 3) (signVector m hm) ∈ (signModule m hm).weight 3 := by
    intro j c hc
    have h := mode_mem_weight (signModule m hm) hc (signVector_mem m hm) (j - 3)
    have hc' : (1 : ℂ) + (j : ℂ) - ((j - 3 : ℤ) : ℂ) - 1 = 3 := by push_cast; ring
    rwa [hc'] at h
  have hR : mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) 0 (mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) 0 (signVector m hm)) ∈ (signModule m hm).weight 3 := by
    have h1 := mode_mem_weight (signModule m hm) (V2mPlus m hm).conformal_mem (signVector_mem m hm) 0
    have h2 := mode_mem_weight (signModule m hm) (V2mPlus m hm).conformal_mem h1 0
    have hc' : (1 : ℂ) + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = 3 := by
      push_cast; ring
    rwa [hc'] at h2
  have hQ : mode ((signModule m hm).YM (V2mPlus m hm).conformalVector) (-1) (signVector m hm) ∈ (signModule m hm).weight 3 := by
    have := hw (V2mPlus m hm).conformal_mem
    rwa [show ((2 : ℤ) - 3) = -1 by norm_num] at this
  have heΩ := lowest_mem_Omega m hm _ (signModule_isLowestWeight m hm) (signVector_mem m hm)
  have heL : L0 (signModule m hm).toWeakModule (signVector m hm) = (1 : ℂ) • signVector m hm := (signModule m hm).L0_weight _ _ (signVector_mem m hm)
  obtain ⟨a, b, hab⟩ := exists_comb_of_span_pair (sign_weight_three m hm hm4 (hw ht))
    (sign_weight_three m hm hm4 hR) (sign_weight_three m hm hm4 hQ) (by
      intro s t hst
      apply RQ_indep m hm hm2 (signModule m hm).toWeakModule heΩ heL (signVector_ne_zero m hm) one_ne_zero
        (by norm_num) s t
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_zero]
      exact hst)
  refine ⟨a, b, ?_⟩
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  exact hab

end VOA.Classification.COne.PlusRat4
