import VOA.Classification.COne.PlusRat2Charged

/-! # Both vacuum/sign orientations for every `m ≥ 2`

The files `PlusRatVacuumSign` and `PlusRatReverse` prove both orientations of the
vacuum/sign pair under `OnlySignWeightOne m`, which is used only to know that `zetaE` takes a
nonzero value at every character-table row of weight one.  `zetaSeparates` proves that for every
`m ≥ 2`: the weight-one rows are the sign row (`sign_zetaE`), the charged row `s = 2k` at
`m = k²` (`charged_zetaE_ne_zero`) and the two half rows at `m = 4` (`half_zetaE`).

The theorems below are the previous proofs verbatim, with the hypothesis
`hw1 : OnlySignWeightOne m` replaced by `hs : ZetaSeparates m hm` (suffix `_sep`).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat2
open VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.SparseRational
open PlusUnitary PlusC2 PlusC2Eval PlusCharacterTable PlusSplitting PlusRatTelescope LatMod
open PlusZhuSchur PlusZhuNormalForms PlusResonantPairs VOA.Huang.LogRemovalAdmissible
open ABDWeakAdmissible PlusRational PlusRatSign

variable (m : ℕ) (hm : 1 ≤ m)

@[reducible] local instance zhuRing3 : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebra3 : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- Every character-table row of weight one takes a nonzero value on `zetaE`. -/
def ZetaSeparates : Prop :=
  ∀ (i : Label m) (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ), HasValues m hm i χ →
    weight m i = 1 → χ (zetaE m hm) ≠ 0

/-- `ZetaSeparates` holds for every `m ≥ 2`. -/
theorem zetaSeparates (hm2 : 2 ≤ m) : ZetaSeparates m hm := by
  intro i χ hχ hw
  rcases i with r | i
  · exact charged_zetaE_ne_zero m hm hm2 r χ hχ
  · fin_cases i
    · simp [weight] at hw
    · rw [sign_zetaE m hm hm2 χ hχ]
      exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (cc_ne_zero m hm))
    · have hv : HasValues m hm (.inr 2) χ := hχ
      simp only [HasValues, values, exceptional] at hv
      rw [half_zetaE m hm hm2 1 (by norm_num) χ (by simpa using hv.1) (by simpa using hv.2.1)
        (by simpa using hv.2.2)]
      exact_mod_cast (show m ≠ 0 by omega)
    · have hv : HasValues m hm (.inr 3) χ := hχ
      simp only [HasValues, values, exceptional] at hv
      rw [half_zetaE m hm hm2 (-1) (by norm_num) χ (by simpa using hv.1) (by simpa using hv.2.1)
        (by simpa using hv.2.2)]
      exact_mod_cast (show m ≠ 0 by omega)
    all_goals (exfalso; simp [weight] at hw <;> norm_num at hw)

/-- Unit combination for `zetaE` at weight one. -/
theorem exists_unit_combination_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) :
    ∃ ξ₁ ξ₂ : VOA.A (V2mPlus m hm),
      ξ₁ * zetaE m hm + ξ₂ * (generator m hm 0 - algebraMap ℂ _ 1) = 1 := by
  apply exists_unit_combination_of_rows m hm hm2
  intro i χ hχ hw
  have hw' : weight m i = 1 := by exact_mod_cast hw
  exact hs i χ hχ hw'

/-- A weight-one top vector killed by `zetaE` vanishes. -/
theorem weightOne_top_eq_zero_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
    {y : M} (hy : y ∈ Omega A) (hL : L0 A y = y)
    (hz : topEvaluation A y hy (zetaE m hm) = 0) : y = 0 := by
  obtain ⟨ξ₁, ξ₂, hunit⟩ := exists_unit_combination_sep m hm hm2 hs
  exact top_eq_zero_of_unit m hm A hy 1 (by rw [one_smul]; exact hL) _ ξ₁ ξ₂ hunit hz

/-- **The translation of the generalized vacuum lift vanishes** (kernel bottom one). -/
theorem translation_zero_of_onlySign_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
    (π : A.Hom (adjointWeakModule (V2mPlus m hm)))
    (hb : FactorBottom A ⊥ (modeComap π ⊥) 1)
    {x : M} (hx : x ∈ (L0 A).maxGenEigenspace 0)
    (he : π.toLinearMap x = (V2mPlus m hm).vacuum) : translation A x = 0 := by
  have ht := translation_vacuum_lift_eigen_one A π 1 hb (by norm_num) hx he
  have hyΩ : translation A x ∈ Omega A := by
    apply kernel_bottom_mem_Omega A (modeComap π ⊥) 1 hb
    · change π.toLinearMap (A.act (V2mPlus m hm).conformalVector 0 x) = 0
      rw [π.map_act, he]
      exact ((V2mPlus m hm).creation _).2 0 le_rfl
    · apply Module.End.eigenspace_le_maxGenEigenspace
      apply Module.End.mem_eigenspace_iff.mpr
      simpa only [one_smul] using ht
  apply weightOne_top_eq_zero_sep m hm hm2 hs A hyΩ ht
  rw [← telescopeE_eq m hm A hyΩ]
  exact translation_telescope A π 1 hb (by norm_num) hx he (EP_mem_grading m hm)
    (EP_mem_grading m hm) m (2 * m - 2) rfl hm (by omega)

/-- **`W₂ v = 0`** (`VacuumWeightFourAnnihilation`), for every `m` with only the sign row
at weight one. -/
theorem vacuumWeightFourAnnihilation_of_onlySign_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) :
    VacuumWeightFourAnnihilation m hm := by
  intro M _ _ A P _ _ hb _ π hk x hx he
  have hb' : FactorBottom A ⊥ (modeComap π ⊥) 1 := by rw [hk]; exact hb
  have ht := translation_zero_of_onlySign_sep m hm hm2 hs A π hb' hx he
  exact nonnegative_modes_zero_of_translation_zero A ht _ 2 (by norm_num)

/-- **The sign-kernel / vacuum-quotient ordered pair splits.** -/
theorem pairSplitting_sign_vacuum_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) :
    PairSplitting m hm (.inr 1) (.inr 0) :=
  (vacuumWeightFourAnnihilation_iff_sign m hm hm2).mp
    (vacuumWeightFourAnnihilation_of_onlySign_sep m hm hm2 hs)

/-- With the sign pair, every positive-integral vacuum-quotient row splits. -/
theorem vacuum_quotient_family_of_onlySign_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) :
    ∀ i : Label m, (.inr 0, i) ∈ positivePairs m → PairSplitting m hm i (.inr 0) :=
  (vacuum_quotient_family_iff_weightFour m hm hm2).mpr
    (vacuumWeightFourAnnihilation_of_onlySign_sep m hm hm2 hs)


section Kernel
variable {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
  (P : Submodule (modeAlg A) M)

/-- A weight-zero eigenvector of a bottom-zero kernel is vacuum-like. -/
theorem translation_zero_of_kernel_zero_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm)
    (hbP : FactorBottom A ⊥ P 0) {z : M} (hzP : z ∈ P) (hL : L0 A z = 0) :
    translation A z = 0 := by
  have hzg : z ∈ (L0 A).maxGenEigenspace 0 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hL
  have hzΩ : z ∈ Omega A := kernel_bottom_mem_Omega A P 0 hbP hzP hzg
  have hyL : L0 A (translation A z) = translation A z := by
    have hc := L0_commutator_weak A (V2mPlus m hm).conformal_mem z 0
    rw [hL, map_zero, add_zero] at hc
    norm_num at hc
    exact hc
  have hyΩ : translation A z ∈ Omega A := by
    intro β v hv n hn
    rw [mode_translation_defect A v n z, Omega_mode_vanish hzΩ hv hn, map_zero, zero_add]
    by_cases hβ : β < 0
    · rw [(V2mPlus m hm).positivity β hβ, Submodule.mem_bot] at hv
      subst hv
      simp
    by_cases hnβ : n = β
    · subst hnβ
      by_cases hn0 : n = 0
      · subst hn0; simp
      · rw [zeroWeight_top_zeroMode m hm hm2 A hzΩ hL hv (by omega), smul_zero]
    · rw [Omega_mode_vanish hzΩ hv (show β ≤ n - 1 by omega), smul_zero]
  apply weightOne_top_eq_zero_sep m hm hm2 hs A hyΩ hyL
  rw [← telescopeE_eq m hm A hyΩ]
  apply telescope_core A (EP m hm) (EP m hm) m (2 * m - 2) z
  · exact zeroWeight_top_zeroMode m hm hm2 A hzΩ hL (EP_mem_grading m hm) (by omega)
  · intro n hn
    by_cases hlast : n = m - 1
    · rw [hlast, show (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 by omega,
        zeroWeight_top_zeroMode m hm hm2 A hzΩ hL (EP_mem_grading m hm) (by omega), map_zero]
    · have hJn : ((2 * m - 2 : ℕ) : ℤ) - n = ((2 * m - 2 - n : ℕ) : ℤ) := by omega
      rw [hJn, lowering_composite_eq A (EP_mem_grading m hm) (EP_mem_grading m hm) hzΩ
        (2 * m - 2 - n) n (by omega) (by omega)]
      rw [zstate, map_sum, LinearMap.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i ≤ 2 * m - 2 - n := by have := Finset.mem_range.mp hi; omega
      have hgr := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading (EP_mem_grading m hm)
        (EP_mem_grading m hm) (i : ℤ)
      rw [map_smul, LinearMap.smul_apply, oLevW_homogeneous A 0 hgr, add_zero,
        zeroWeight_top_zeroMode m hm hm2 A hzΩ hL hgr (by omega), smul_zero]

/-- **The bottom-zero kernel has no generalized weight one.** -/
theorem kernel_weightOne_eq_zero_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm)
    (hP : IsAtom P) (hbP : FactorBottom A ⊥ P 0) {w : M} (hwP : w ∈ P)
    (hw : w ∈ (L0 A).maxGenEigenspace 1) : w = 0 := by
  obtain ⟨v, hv, hv0⟩ := SetLike.not_le_iff_exists.mp hbP.1
  have hv0' : v ≠ 0 := fun h => hv0 (by rw [h]; exact Submodule.zero_mem _)
  obtain ⟨z, hzP, hz0, hzL⟩ := exists_eigen_in m hm A P 0 hv.1 hv.2 hv0'
  have hzL' : L0 A z = 0 := by simpa using hzL
  have hT := translation_zero_of_kernel_zero_sep m hm A P hm2 hs hbP hzP hzL'
  have hcyc : cyclic A z = P := by
    have hle : cyclic A z ≤ P := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzP)
    rcases hP.le_iff.mp hle with h | h
    · exfalso
      have hz : z ∈ cyclic A z := Submodule.mem_span_singleton_self z
      rw [h] at hz
      exact hz0 ((Submodule.mem_bot _).mp hz)
    · exact h
  have hzg : z ∈ (L0 A).maxGenEigenspace 0 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hzL'
  have hdeg := cyclic_inf_gen_eq_degreeSpan (V2mPlus_c2Cofinite m hm) A hzg 1
  have hw' : w ∈ homogeneousDegreeSpan A z 1 := by
    rw [← hdeg]
    refine ⟨?_, ?_⟩
    · change w ∈ cyclic A z
      rw [hcyc]; exact hwP
    · simpa using hw
  have hzero : homogeneousDegreeSpan A z 1 = ⊥ := by
    rw [eq_bot_iff]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    change homogeneousDegree l = 1 at hl
    have hmem := homogeneousWord_vacuum_mem (W := V2mPlus m hm) l
    rw [hl, grading_one_eq_bot m hm hm2, Submodule.mem_bot] at hmem
    change homogeneousWord A l z ∈ (⊥ : Submodule ℂ M)
    have h := homogeneousWord_hom _ A (vacuumLiftHom A z hT) l (V2mPlus m hm).vacuum
    rw [vacuumLiftHom_vacuum, hmem, map_zero] at h
    rw [h]
    exact Submodule.zero_mem _
  rw [hzero] at hw'
  exact (Submodule.mem_bot ℂ).mp hw'

/-- Every weight-zero kernel vector is vacuum-like. -/
theorem kernel_zero_vacuumLike_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm)
    (hP : IsAtom P) (hbP : FactorBottom A ⊥ P 0) {z : M} (hzP : z ∈ P)
    (hz : z ∈ (L0 A).maxGenEigenspace 0) : translation A z = 0 := by
  apply kernel_weightOne_eq_zero_sep m hm A P hm2 hs hP hbP
    (mem_P_mode m hm A P _ 0 hzP)
  have h := mode_mem_maxGenEigenspace A (V2mPlus m hm).conformal_mem 0 hz
  have hc : (0 : ℂ) + ((2 - 0 - 1 : ℤ) : ℂ) = 1 := by norm_num
  rw [hc] at h
  exact h

end Kernel

section Extension
variable {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
  (P : Submodule (modeAlg A) M)

/-- `L(1)` kills the E-telescope of every generalized weight-one vector. -/
theorem L1_Zop_eq_zero_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M}
    (hw : w ∈ (L0 A).maxGenEigenspace 1) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (Zop m hm A w) = 0 := by
  apply lowering_telescope_core A m hm (EP_mem_grading m hm) (L1_E m hm) w
  · intro n
    have hL1w : mode (A.YM (V2mPlus m hm).conformalVector) 2 w ∈
        (L0 A).maxGenEigenspace 0 := by
      have h := mode_mem_maxGenEigenspace A (V2mPlus m hm).conformal_mem 2 hw
      have hc : (1 : ℂ) + ((2 - 2 - 1 : ℤ) : ℂ) = 0 := by norm_num
      rwa [hc] at h
    have hP' := low_mem_P m hm A P hbQ hL1w (by norm_num)
    have hT := kernel_zero_vacuumLike_sep m hm A P hm2 hs hP hbP hP' hL1w
    exact nonnegative_modes_zero_of_translation_zero A hT _ n (by positivity)
  · have hEw : mode (A.YM (EP m hm)) (m : ℤ) w ∈ (L0 A).maxGenEigenspace 0 := by
      have h := mode_mem_maxGenEigenspace A (EP_mem_grading m hm) (m : ℤ) hw
      have hc : (1 : ℂ) + (((m : ℤ) - m - 1 : ℤ) : ℂ) = 0 := by push_cast; ring
      rwa [hc] at h
    have hP' := low_mem_P m hm A P hbQ hEw (by norm_num)
    have hT := kernel_zero_vacuumLike_sep m hm A P hm2 hs hP hbP hP' hEw
    exact nonnegative_modes_zero_of_translation_zero A hT _ _ (by omega)

/-- **`L(1)` kills every weight-one eigenvector of the extension.** -/
theorem L1_kill_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M} (hL : L0 A w = w) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 w = 0 := by
  have hwg : w ∈ (L0 A).maxGenEigenspace 1 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hL
  obtain ⟨ξ₁, ξ₂, hunit⟩ := exists_unit_combination_sep m hm hm2 hs
  obtain ⟨s₁, hs₁⟩ := VOA.mk_surjective (V2mPlus m hm) ξ₁
  obtain ⟨s₂, hs₂⟩ := VOA.mk_surjective (V2mPlus m hm) ξ₂
  set w' := oLevW A 0 s₁ w with hw'def
  have hw'g : w' ∈ (L0 A).maxGenEigenspace 1 := oLevW_mem_maxGen A s₁ hwg
  set B := WeakModule.quotient A (ofR A P)
  set q : A.Hom B := WeakModule.quotientMk A (ofR A P)
  have hqΩ := quotient_mem_Omega m hm A P hbQ hwg
  have hq'Ω := quotient_mem_Omega m hm A P hbQ hw'g
  have hZq : q.toLinearMap (Zop m hm A w') =
      topEvaluation B (q.toLinearMap w') hq'Ω (zetaE m hm) := by
    rw [← telescopeE_eq m hm B hq'Ω, Zop, map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_smul]
    congr 1
  have hshift : ∀ r, topEvaluation B (q.toLinearMap w') hq'Ω r =
      topEvaluation B (q.toLinearMap w) hqΩ (r * ξ₁) := by
    intro r
    obtain ⟨t, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) r
    rw [topEvaluation_mk, ← hs₁, topEvaluation_mk_mul, topEvaluation_mk, hw'def,
      hom_oLevW A B q s₁ w]
  have hLq : L0 B (q.toLinearMap w) = q.toLinearMap w := by
    have h := q.map_act (V2mPlus m hm).conformalVector 1 w
    simp only [WeakModule.act_def] at h
    change mode (B.YM (V2mPlus m hm).conformalVector) 1 (q.toLinearMap w) = _
    rw [← h]
    change q.toLinearMap (L0 A w) = _
    rw [hL]
  have hqZ : q.toLinearMap (Zop m hm A w') = q.toLinearMap w := by
    rw [hZq, hshift, zhu_mul_comm m hm hm2, eq_sub_of_add_eq hunit, map_sub,
      topEvaluation_one, ← hs₂, topEvaluation_mk_mul]
    have hω : topEvaluation B (q.toLinearMap w) hqΩ
        (generator m hm 0 - algebraMap ℂ _ 1) = 0 := by
      rw [map_sub, topEvaluation_omega m hm B hqΩ, Algebra.algebraMap_eq_smul_one, map_smul,
        topEvaluation_one, one_smul, hLq, sub_self]
    rw [hω, map_zero, sub_zero]
  have hdiff : Zop m hm A w' - w ∈ P := by
    have h0 : q.toLinearMap (Zop m hm A w' - w) = 0 := by rw [map_sub, hqZ, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  have hZ : Zop m hm A w' = w := sub_eq_zero.mp
    (kernel_weightOne_eq_zero_sep m hm A P hm2 hs hP hbP hdiff
      (Submodule.sub_mem _ (Zop_mem_maxGen m hm A hw'g) hwg))
  rw [← hZ]
  exact L1_Zop_eq_zero_sep m hm A P hm2 hs hP hbP hbQ hw'g

/-- All lowering-by-one modes kill a weight-one eigenvector of the extension. -/
theorem lowering_one_kill_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M} (hL : L0 A w = w) :
    ∀ (k : ℕ) (a : VP m hm), a ∈ (V2mPlus m hm).grading (k : ℤ) →
      mode (A.YM a) (k : ℤ) w = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a ha
  have hc := L1_comm A ha ((k : ℤ) - 1) w
  have hzm : L0 A (mode (A.YM a) ((k : ℤ) - 1) w) = mode (A.YM a) ((k : ℤ) - 1) w := by
    have h := L0_commutator_weak A ha w ((k : ℤ) - 1)
    rw [hL] at h
    rw [h]
    simp
  rw [L1_kill_sep m hm A P hm2 hs hP hbP hbQ hzm, L1_kill_sep m hm A P hm2 hs hP hbP hbQ hL,
    map_zero, sub_zero] at hc
  have hgr : (V2mPlus m hm).L 1 a ∈ (V2mPlus m hm).grading ((k : ℤ) - 1) := by
    have h := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading
      (V2mPlus m hm).conformal_mem ha 2
    have he : (V2mPlus m hm).L 1 a = (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 2 a := by
      rw [VertexOperatorAlgebra.L_def]; rfl
    rw [he]
    have hk : (2 : ℤ) + k - 2 - 1 = (k : ℤ) - 1 := by ring
    rwa [hk] at h
  have hlow : mode (A.YM ((V2mPlus m hm).L 1 a)) ((k : ℤ) - 1) w = 0 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hz : (V2mPlus m hm).L 1 a = 0 := by
        have := hgr
        rw [(V2mPlus m hm).positivity _ (by norm_num), Submodule.mem_bot] at this
        exact this
      rw [hz, map_zero]
      rfl
    · have h := ih (k - 1) (by omega) _ (by rwa [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega])
      rwa [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega] at h
  rw [hlow, add_zero, show (k : ℤ) - 1 + 1 = k by ring] at hc
  by_cases hk1 : k = 1
  · subst hk1
    have hz : a = 0 := by
      have := ha
      rw [show ((1 : ℕ) : ℤ) = 1 by norm_num, grading_one_eq_bot m hm hm2,
        Submodule.mem_bot] at this
      exact this
    rw [hz, map_zero]
    rfl
  · have hne : ((2 * (k : ℤ) - ((k : ℤ) - 1) - 2 : ℤ) : ℂ) ≠ 0 := by
      have : (2 * (k : ℤ) - ((k : ℤ) - 1) - 2 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    exact (smul_eq_zero.mp hc.symm).resolve_left hne

/-- A weight-one eigenvector of the extension is a top vector. -/
theorem eigen_one_mem_Omega_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M} (hL : L0 A w = w) :
    w ∈ Omega A := by
  have hwg : w ∈ (L0 A).maxGenEigenspace 1 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hL
  intro β v hv n hn
  by_cases hβ : β < 0
  · rw [(V2mPlus m hm).positivity β hβ, Submodule.mem_bot] at hv
    subst hv
    simp
  by_cases hnβ : n = β
  · subst hnβ
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    exact lowering_one_kill_sep m hm A P hm2 hs hP hbP hbQ hL k v hv
  · have hg := mode_mem_maxGenEigenspace A hv n hwg
    have hre : (1 + ((β - n - 1 : ℤ) : ℂ)).re < 0 := by
      simp only [Complex.add_re, Complex.one_re, Complex.intCast_re]
      have : ((β - n - 1 : ℤ) : ℝ) < -1 := by exact_mod_cast (show β - n - 1 < -1 by omega)
      linarith
    have hP' := low_mem_P m hm A P hbQ hg (by linarith)
    exact kernel_generalized_below_bottom_eq_zero A P 0 hbP hP' hg (by simpa using hre)

end Extension

/-- **The vacuum-kernel / sign-quotient ordered pair splits.** -/
theorem pairSplitting_vacuum_sign_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) :
    PairSplitting m hm (.inr 0) (.inr 1) := by
  intro M _ _ A P hP hQ hb ht
  have hbP : FactorBottom A ⊥ P 0 := by simpa [weight] using hb
  have hbQ : FactorBottom A P ⊤ 1 := by simpa [weight] using ht
  apply (exists_cyclic_lift_iff_complement A P hQ 1 hbQ).mp
  obtain ⟨x, hx, hxP⟩ := exists_generalized_lift_of_factorBottom A P 1 hbQ
  -- an honest eigenvector lift
  classical
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  set f := L0 A - (1 : ℂ) • (1 : Module.End ℂ M)
  have hfmem : ∀ j : ℕ, (f ^ j) x ∈ (L0 A).maxGenEigenspace 1 := by
    intro j
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    refine ⟨k, ?_⟩
    rw [← Module.End.mul_apply, ← pow_add, add_comm, pow_add, Module.End.mul_apply, hk,
      map_zero]
  have hex : ∃ j : ℕ, (f ^ (j + 1)) x ∈ P := ⟨k, by
    rw [show k + 1 = 1 + k by ring, pow_add, Module.End.mul_apply, hk, map_zero]
    exact Submodule.zero_mem _⟩
  let j := Nat.find hex
  have hj : (f ^ (j + 1)) x ∈ P := Nat.find_spec hex
  have hjP : (f ^ j) x ∉ P := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero]; exact hxP
    · have := Nat.find_min hex (show j - 1 < j by omega)
      rwa [Nat.sub_add_cancel hj0] at this
  have hfe : f ((f ^ j) x) = (f ^ (j + 1)) x := by
    rw [pow_succ', Module.End.mul_apply]
  have hfz : f ((f ^ j) x) = 0 := by
    apply kernel_weightOne_eq_zero_sep m hm A P hm2 hs hP hbP
    · rw [hfe]; exact hj
    · rw [hfe]; exact hfmem (j + 1)
  set x' := (f ^ j) x
  have hL : L0 A x' = x' := by
    have h := hfz
    change L0 A x' - (1 : ℂ) • x' = 0 at h
    rw [one_smul] at h
    exact sub_eq_zero.mp h
  have hx'g : x' ∈ (L0 A).maxGenEigenspace 1 := hfmem j
  have hx'Ω := eigen_one_mem_Omega_sep m hm A P hm2 hs hP hbP hbQ hL
  refine ⟨x', hx'g, hjP, ?_⟩
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hbP.1
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0' x',
    no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite m hm) A hx'g (-1)
      (by
        have h2 : (1 : ℂ) + ((-1 : ℤ) : ℂ) = 0 := by norm_num
        rw [h2]; exact hy.2),
    degreeSpan_neg_one_eq_bot A hx'Ω 1 (by rw [one_smul]; exact hL)]
  intro h
  exact hy0' ((Submodule.mem_bot ℂ).mp h)

/-- **Both vacuum/sign orientations split** (every weight-one row separated by `zetaE`). -/
theorem vacuum_sign_both_sep (hm2 : 2 ≤ m) (hs : ZetaSeparates m hm) :
    PairSplitting m hm (.inr 0) (.inr 1) ∧ PairSplitting m hm (.inr 1) (.inr 0) :=
  ⟨pairSplitting_vacuum_sign_sep m hm hm2 hs, pairSplitting_sign_vacuum_sep m hm hm2 hs⟩

end VOA.Classification.COne.PlusRat2
