import VOA.Classification.COne.PlusRat6TwModel

/-! # The tops of the twisted model and their table rows

For `odd = false` (`true`) the vector `topTensor m odd = 1 ⊗ 1` (`h(-1/2) ⊗ 1`) spans the
`L(0)`-eigenspace of weight `1/16` (`9/16`) of `BW m hm t`, and every vector of that eigenspace is
a top vector (`mem_Omega_bottom`).  `exists_pure_top` turns it into a top vector whose Zhu
character is a table row; the `ω`- and `E`-values (`E_topTensor`) pin the row to
`twLabel t odd ∈ {T1±, T2±}` (`label_of_values`).

`modelSpecG_twisted`: every twisted row has a model with spectrum maps `φT, ψT`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3 PlusRat5 PlusCharacterTable
  PlusResonantPairs PlusZhuNormalForms PlusRatSign PlusSplitting PlusRatTelescope
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat4 PlusRational
open VOA.Moonshine.LatticeTwistedGeneral VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted
  PlusTwistLattice
open scoped TensorProduct

variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) (t : ZMod 2)

/-- The twisted row realized by `(t, odd)`. -/
def twLabel (t : ZMod 2) (odd : Bool) : Label m :=
  .inr (if t = 0 then (if odd then 5 else 4) else (if odd then 7 else 6))

theorem zmod_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t
  · left; rfl
  · right; rfl

theorem one_ne_zero_zmod : (1 : ZMod 2) ≠ 0 := by decide

theorem weight_twLabel (odd : Bool) :
    ((weight m (twLabel m t odd) : ℚ) : ℂ) = bottom odd := by
  rcases zmod_cases t with rfl | rfl <;> cases odd <;>
    simp [twLabel, weight, bottom, one_ne_zero_zmod]

theorem twLabel_surj (i : Fin 8) (hi : 4 ≤ i.val) : ∃ t odd, twLabel m t odd = .inr i := by
  fin_cases i <;> simp at hi
  · exact ⟨0, false, rfl⟩
  · exact ⟨0, true, rfl⟩
  · exact ⟨1, false, rfl⟩
  · exact ⟨1, true, rfl⟩

/-- Every vector of the bottom eigenspace is a top vector. -/
theorem mem_Omega_bottom (odd : Bool) {y : FockT (rank (latP m)) ⊗[ℂ] ℂ}
    (hy : y ∈ (NW m hm t).weight (bottom odd)) : y ∈ Omega (BW m hm t) := by
  intro β v hv n hn
  have h := mode_mem_weight (NW m hm t) hv hy n
  rw [NW_weight, weightLT_eq_bot, Submodule.mem_bot] at h
  · exact h
  intro d hd
  have hre := congrArg Complex.re hd
  have hβn : (β : ℝ) ≤ n := by exact_mod_cast hn
  rw [levelT, rank_latP] at hre
  cases odd <;> simp [bottom] at hre <;> push_cast at hre <;>
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

theorem topTensor_mem_bottom (odd : Bool) :
    topTensor m odd ∈ (NW m hm t).weight (bottom odd) := by
  rw [NW_weight, ← level_bottom m odd, weightLT_level]
  exact topTensor_mem m odd

theorem L0_bottom (odd : Bool) {y : FockT (rank (latP m)) ⊗[ℂ] ℂ}
    (hy : y ∈ (NW m hm t).weight (bottom odd)) : L0 (BW m hm t) y = bottom odd • y :=
  (NW m hm t).L0_weight _ _ hy

theorem lvl_term (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (v : ℕ × Fin (rank (latP m))) :
    s v * (2 * v.1 + 1) ≤ lvl m s := by
  by_cases hv : s v = 0
  · rw [hv]; simp
  · have hmem : v ∈ s.support := Finsupp.mem_support_iff.mpr hv
    have := Finset.single_le_sum (f := fun i => s i • wT i) (fun _ _ => Nat.zero_le _) hmem
    rw [lvl, Finsupp.weight_apply, Finsupp.sum]
    simpa only [smul_eq_mul, wT_apply] using this

theorem lvl_eq_zero {s : (ℕ × Fin (rank (latP m))) →₀ ℕ} (h : lvl m s = 0) : s = 0 := by
  ext v
  have h1 := lvl_term m s v
  rw [h] at h1
  have h2 : s v * 1 ≤ s v * (2 * v.1 + 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem lvl_eq_one {s : (ℕ × Fin (rank (latP m))) →₀ ℕ} (h : lvl m s = 1) :
    s = Finsupp.single (0, a0 m) 1 := by
  have hsupp : ∀ v, v ≠ (0, a0 m) → s v = 0 := by
    intro v hv
    by_contra h0
    have h1 := lvl_term m s v
    rw [h] at h1
    have hv1 : v.1 = 0 := by
      by_contra h2
      have h3 : 1 * 3 ≤ s v * (2 * v.1 + 1) :=
        Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr h0) (by omega)
      omega
    exact hv (Prod.ext hv1 (fin_eq_a0 m v.2))
  have hs : s = Finsupp.single (0, a0 m) (s (0, a0 m)) := by
    ext v
    by_cases hv : v = (0, a0 m)
    · subst hv; simp
    · rw [hsupp v hv, Finsupp.single_apply, if_neg (Ne.symm hv)]
  rw [hs] at h ⊢
  rw [lvl, Finsupp.weight_single, smul_eq_mul, wT_apply] at h
  simp at h
  rw [h]

/-- The bottom eigenspace is the line through `topTensor m odd`. -/
theorem bottom_mem_span (odd : Bool) {y : FockT (rank (latP m)) ⊗[ℂ] ℂ}
    (hy : y ∈ (NW m hm t).weight (bottom odd)) : ∃ κ : ℂ, y = κ • topTensor m odd := by
  rw [NW_weight, ← level_bottom m odd, weightLT_level] at hy
  have h := GT_span m _ hy
  have hsub : {u | ∃ s, lvl m s = odd.toNat ∧ u = monoT m s} ⊆ {topTensor m odd} := by
    rintro _ ⟨s, hs, rfl⟩
    cases odd
    · rw [lvl_eq_zero m hs]; simp [monoT, topTensor, oscillatorTop]
    · rw [lvl_eq_one m hs]
      simp [monoT, topTensor, oscillatorTop, MvPolynomial.X]
  have h2 := Submodule.span_mono hsub h
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp h2
  exact ⟨κ, hκ.symm⟩

/-- `o(E)` on the bottom eigenspace. -/
theorem oE_bottom (odd : Bool) {y : FockT (rank (latP m)) ⊗[ℂ] ℂ}
    (hy : y ∈ (NW m hm t).weight (bottom odd)) :
    mode ((BW m hm t).YM (EP m hm)) ((m : ℤ) - 1 + 0) y = eValue m t odd • y := by
  obtain ⟨κ, rfl⟩ := bottom_mem_span m hm t odd hy
  rw [map_smul, BW_mode, show (2 : ℤ) * ((m : ℤ) - 1 + 0) = 2 * ((m : ℤ) - 1) by ring]
  rw [show (Tw m hm t).YM ((EP m hm : VP m hm) : LatModuleGen (latP m)) (2 * ((m : ℤ) - 1))
      (topTensor m odd) = eValue m t odd • topTensor m odd from E_topTensor m hm t odd]
  rw [smul_comm]

/-- The `E`-value is real. -/
theorem eValue_eq (odd : Bool) : eValue m t odd =
    (((twistedScale m) * (if t = 0 then 1 else -1) * (if odd then 1 - 4 * (m : ℝ) else 1) : ℝ) : ℂ) := by
  rcases zmod_cases t with rfl | rfl <;> cases odd <;>
    simp [eValue, VOA.Moonshine.Extraspecial.sgn_zero, VOA.Moonshine.Extraspecial.sgn_one,
      one_ne_zero_zmod]

theorem twistedScale_pos : 0 < twistedScale m := by
  unfold twistedScale; positivity

include hm2 in
/-- The `(ω, E)` values pin the twisted row. -/
theorem label_of_values (odd : Bool) (l : Label m)
    (hω : (values m (twistedScale m) l).1 = if odd then 9 / 16 else 1 / 16)
    (hE : (values m (twistedScale m) l).2.2 =
      twistedScale m * (if t = 0 then 1 else -1) * (if odd then 1 - 4 * (m : ℝ) else 1)) :
    l = twLabel m t odd := by
  have ha := twistedScale_pos m
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hq := mul_pos ha (show (0 : ℝ) < 4 * m - 1 by linarith)
  set a := twistedScale m
  rcases zmod_cases t with rfl | rfl <;> cases odd <;>
    simp only [if_true, if_false, one_ne_zero_zmod, Bool.false_eq_true] at hω hE <;>
    rcases l with r | i
  all_goals first
    | (exfalso; simp only [values] at hE; nlinarith)
    | (fin_cases i <;> simp [values, exceptional, twLabel] at hω hE ⊢ <;>
        first
          | nlinarith
          | (have h4 : (4 * (m : ℝ)) = 9 := by linarith
             have h4' : 4 * m = 9 := by exact_mod_cast h4
             omega)
          | (rcases hE with h | h <;> nlinarith))

theorem φT_ne_zero (a : ℕ) : φT a ≠ 0 := by
  intro h
  have h1 : ((16 * a : ℕ) : ℂ) = 1 := by
    rw [φT] at h; push_cast; linear_combination 128 * h
  have h2 : 16 * a = 1 := by exact_mod_cast h1
  omega

theorem bottom_real (odd : Bool) : bottom odd = (((if odd then 9 / 16 else 1 / 16 : ℝ)) : ℂ) := by
  cases odd <;> simp [bottom]

include hm2 in
/-- **The twisted models.** -/
theorem modelSpecG_twisted (odd : Bool) (h' : ℂ) :
    ModelSpecG m hm hm2 (twLabel m t odd) h' φT ψT := by
  have hy := topTensor_mem_bottom m hm t odd
  have hyΩ := mem_Omega_bottom m hm t odd hy
  obtain ⟨l', z, hz, -, hz0, hzL, hχ⟩ := exists_pure_top m hm hm2 (BW m hm t)
    (⊤ : Submodule (modeAlg (BW m hm t)) _) (y := topTensor m odd) Submodule.mem_top hyΩ
    (topTensor_ne_zero m odd) (L0_bottom m hm t odd hy)
    (fun z _ hzL => mem_Omega_bottom m hm t odd (VOA.eigenvector_mem_weight _ hzL))
  have hzw : z ∈ (NW m hm t).weight (bottom odd) := VOA.eigenvector_mem_weight _ hzL
  have hvals := chiT_hasValues m hm hm2 l'
  -- the `E`-value
  have hE1 := hχ (VOA.mk (V2mPlus m hm) (EP m hm))
  rw [topEvaluation_mk, oLevW_homogeneous _ 0 (EP_mem_grading m hm), oE_bottom m hm t odd hzw]
    at hE1
  have hE2 : chiT m hm hm2 l' (VOA.mk (V2mPlus m hm) (EP m hm)) = eValue m t odd := by
    have h3 : (eValue m t odd - chiT m hm hm2 l' (VOA.mk (V2mPlus m hm) (EP m hm))) • z = 0 := by
      rw [sub_smul, hE1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hz0)).symm
  -- the `ω`-value
  have hω1 := hχ (generator m hm 0)
  rw [topEvaluation_omega m hm _ hz, L0_bottom m hm t odd hzw] at hω1
  have hω2 : chiT m hm hm2 l' (generator m hm 0) = bottom odd := by
    have h3 : (bottom odd - chiT m hm hm2 l' (generator m hm 0)) • z = 0 := by
      rw [sub_smul, hω1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hz0)).symm
  have hl : l' = twLabel m t odd := by
    apply label_of_values m hm2 t odd l'
    · apply Complex.ofReal_injective
      rw [← bottom_real, ← hω2]
      exact hvals.1.symm
    · apply Complex.ofReal_injective
      rw [← eValue_eq, ← hE2]
      exact hvals.2.2.symm
  subst hl
  refine ⟨_, inferInstance, inferInstance, BW m hm t, z, hz, hz0, ?_, hχ,
    fun w => specSpan_tw m hm t w, ?_⟩
  · rw [weight_twLabel]; exact hzL
  · obtain ⟨C, hC⟩ := specSpan_tw m hm t h'
    refine ⟨C, fun y hy => Submodule.span_mono ?_ (hC y hy)⟩
    rintro u ⟨a, b, -, ha, hb, h1, h2⟩
    exact ⟨a, b, φT_ne_zero a, ha, hb, h1, h2⟩

end VOA.Classification.COne.PlusRat6
