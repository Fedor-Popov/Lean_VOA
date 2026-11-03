import VOA.Classification.COne.PlusRatSign

/-! # Vacuum quotient over a weight-one kernel: splitting via the lattice generator `E`

The target `VacuumWeightFourAnnihilation` (equivalently the ordered pair
`PairSplitting m hm (.inr 1) (.inr 0)`: kernel bottom one, quotient bottom zero) is proved here
for every `m ≥ 2` whose only character-table row of weight one is the sign row.  This covers
`m = 2, 3, 5, 6, 7, 8, 10, …` and excludes exactly `m = 4` (half-lattice rows) and `m = k²`,
`k ≥ 3` (a charged row of weight one); see `onlySignWeightOne`.

Argument.  Let `x` be the generalized vacuum lift and `y = T x`.
* `translation_telescope` (with `a = b = E`, `J = 2m-2`) and `telescope_eq_topEvaluation`
  give `ζ · y = 0` for the explicit Zhu element `ζ = zeta E E m (2m-2)`.
* `(ω - 1) · y = 0`.
* `A(V_{2m}⁺) ≅ ℂ^{m+7}` through the proved character table; at a row of weight one (only the
  sign row, by hypothesis) `ζ` takes the value `2c² ≠ 0`, computed on the actual sign module
  (`PlusRatSign`).  Hence `ζ` and `ω - 1` generate the unit ideal and `y = 0`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRatSign
open VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
open PlusUnitary PlusC2 PlusCharacterTable PlusSplitting PlusRatTelescope LatMod PlusZhuSchur
open PlusZhuNormalForms PlusResonantPairs VOA.Huang.LogRemovalAdmissible

universe u

/-- The unit of Zhu's algebra evaluates to the identity on a top vector. -/
theorem topEvaluation_one {V M : Type u} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
    (A : WeakModule W M) (y : M) (hy : y ∈ Omega A) :
    (letI := instRingA W; topEvaluation A y hy 1) = y := by
  letI := instRingA W
  change oLevW A 0 W.vacuum y = y
  rw [oLevW_homogeneous A 0 W.vacuum_mem_grading_zero]
  simp [A.vacuum_YM]

variable (m : ℕ) (hm : 1 ≤ m)

/-- The sign top vector is a weak-module top vector. -/
theorem signVector_mem_Omega :
    signVector m hm ∈ Omega (signModule m hm).toWeakModule := by
  intro β v hv n hn
  exact mode_lowering_vanish (signModule m hm) (signModule_isLowestWeight m hm) hv
    (signVector_mem m hm) hn

/-- The E-telescope on the actual sign top equals `2c² u`. -/
theorem sign_telescope :
    ∑ n ∈ Finset.range m, ((-1 : ℂ) ^ n * ((2 * m - 2).choose n : ℂ)) •
      mode ((signModule m hm).toWeakModule.YM (EP m hm)) (((2 * m - 2 : ℕ) : ℤ) - n)
        (mode ((signModule m hm).toWeakModule.YM (EP m hm)) n (signVector m hm)) =
      ((2 : ℂ) * cc m ^ 2) • signVector m hm := by
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul,
      Nat.cast_zero, sub_zero]
    apply Subtype.ext
    exact E_top_E_zero_sign m hm
  · intro n _ hn
    have hz : mode ((signModule m hm).toWeakModule.YM (EP m hm)) (n : ℤ) (signVector m hm) = 0 := by
      apply Subtype.ext
      exact E_pos_sign m hm n (by omega)
    rw [hz, map_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

@[reducible] local instance zhuRingRS : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebraRS : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- The explicit Zhu element of the E-telescope. -/
def zetaE : VOA.A (V2mPlus m hm) := zeta (V2mPlus m hm) (EP m hm) (EP m hm) m (2 * m - 2)

/-- The telescope on any top vector of any weak module is the action of `zetaE`. -/
theorem telescopeE_eq {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {y : M} (hy : y ∈ Omega A) :
    ∑ n ∈ Finset.range m, ((-1 : ℂ) ^ n * ((2 * m - 2).choose n : ℂ)) •
      mode (A.YM (EP m hm)) (((2 * m - 2 : ℕ) : ℤ) - n) (mode (A.YM (EP m hm)) n y) =
      topEvaluation A y hy (zetaE m hm) :=
  telescope_eq_topEvaluation A (EP_mem_grading m hm) (EP_mem_grading m hm) hy m (2 * m - 2)
    rfl hm (by omega) (by positivity)

/-- Any character with the sign row acts on the actual sign top through the module. -/
theorem sign_topEvaluation_eq (hm2 : 2 ≤ m) (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (hχ : HasValues m hm (.inr 1) χ) (r : VOA.A (V2mPlus m hm)) :
    topEvaluation (signModule m hm).toWeakModule (signVector m hm)
      (signVector_mem_Omega m hm) r = χ r • signVector m hm := by
  set f := topEvaluation (signModule m hm).toWeakModule (signVector m hm)
    (signVector_mem_Omega m hm)
  let B : Subalgebra ℂ (VOA.A (V2mPlus m hm)) :=
    { carrier := {r | f r = χ r • signVector m hm}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨s, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) a
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [topEvaluation_mk_mul, hb, map_smul,
          ← topEvaluation_mk (signModule m hm).toWeakModule (signVector m hm)
            (signVector_mem_Omega m hm) s, ha, map_mul, smul_smul, mul_comm]
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, map_add, add_smul]
      algebraMap_mem' := by
        intro c
        change f (algebraMap ℂ _ c) = χ (algebraMap ℂ _ c) • signVector m hm
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one (A := VOA.A (V2mPlus m hm)),
          map_smul, topEvaluation_one]
        simp }
  have h0 : VOA.mk (V2mPlus m hm) (gP m hm 0) ∈ B := by
    change f (VOA.mk (V2mPlus m hm) (gP m hm 0)) = _
    rw [topEvaluation_mk, hχ.1]
    change oLevW _ 0 (V2mPlus m hm).conformalVector _ = _
    rw [oLevW_homogeneous _ 0 (V2mPlus m hm).conformal_mem]
    have hw := (signModule m hm).L0_weight 1 _ (signVector_mem m hm)
    have hv : (((values m (twistedScale m) (.inr 1)).1 : ℝ) : ℂ) = 1 := by
      simp [values, exceptional]
    rw [hv, show ((2 : ℤ) - 1 + 0) = 1 by norm_num]
    exact hw
  have h1 : VOA.mk (V2mPlus m hm) (gP m hm 1) ∈ B := by
    change f (VOA.mk (V2mPlus m hm) (gP m hm 1)) = _
    rw [topEvaluation_mk, hχ.2.1]
    change oLevW _ 0 (WP m hm) _ = _
    have hw := signVector_W m hm
    rw [oMod_homogeneous _ (WP_mem_grading m hm)] at hw
    rw [oLevW_homogeneous _ 0 (WP_mem_grading m hm)]
    simp only [values, exceptional]
    norm_num
    exact hw
  have h2 : VOA.mk (V2mPlus m hm) (gP m hm 2) ∈ B := by
    change f (VOA.mk (V2mPlus m hm) (gP m hm 2)) = _
    rw [topEvaluation_mk, hχ.2.2]
    change oLevW _ 0 (EP m hm) _ = _
    have hw := signVector_E m hm hm2
    rw [oMod_homogeneous _ (EP_mem_grading m hm)] at hw
    rw [oLevW_homogeneous _ 0 (EP_mem_grading m hm)]
    have hv : (((values m (twistedScale m) (.inr 1)).2.2 : ℝ) : ℂ) = 0 := by
      simp [values, exceptional]
    rw [hv, zero_smul, show ((m : ℤ) - 1 + 0) = (m : ℤ) - 1 by ring]
    exact hw
  have htop : B = ⊤ := by
    apply top_unique
    rw [← V2mPlus_zhu_adjoin_generators m hm hm2]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [h0, h1, h2]
  have hr : r ∈ B := htop ▸ Algebra.mem_top
  exact hr

/-- Every character with the sign row takes the value `2c² ≠ 0` on `zetaE`. -/
theorem sign_zetaE (hm2 : 2 ≤ m) (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (hχ : HasValues m hm (.inr 1) χ) : χ (zetaE m hm) = 2 * cc m ^ 2 := by
  have h1 := sign_topEvaluation_eq m hm hm2 χ hχ (zetaE m hm)
  rw [← telescopeE_eq m hm _ (signVector_mem_Omega m hm), sign_telescope] at h1
  have h2 : (χ (zetaE m hm) - 2 * cc m ^ 2) • signVector m hm = 0 := by
    rw [sub_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (fun hz => signVector_ne_zero m hm hz)

/-- The hypothesis on `m`: the only weight-one row of the table is the sign row. -/
def OnlySignWeightOne : Prop := ∀ i : Label m, weight m i = 1 → i = .inr 1

/-- The proved character table: one genuine Zhu character per label, all distinct. -/
theorem exists_characterTable (hm2 : 2 ≤ m) :
    ∃ χ : Label m → (VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ),
      (∀ i, HasValues m hm i (χ i)) ∧ Function.Injective χ := by
  have hex : ∀ i : Label m, ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm i χ := by
    intro i
    by_cases hi : IsUntwisted i
    · exact untwisted_character_exists m hm hm2 i hi
    · exact V2mPlus_twistedCharacters m hm hm2 i hi
  choose χ hχ using hex
  refine ⟨χ, hχ, ?_⟩
  intro i j h
  exact label_eq_of_hasValues m hm hm2 (χ i) i j (hχ i) (h.symm ▸ hχ j)

/-- The omega value of a table character is the table weight. -/
theorem hasValues_omega {i : Label m} {χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ}
    (hχ : HasValues m hm i χ) : χ (generator m hm 0) = ((weight m i : ℚ) : ℂ) := by
  have h0 := hχ.1
  change χ (generator m hm 0) = _ at h0
  rw [h0, ← weight_eq_table m (twistedScale m) i]
  push_cast
  rfl

/-- In `A(V_{2m}⁺) ≅ ℂ^{m+7}`, an element vanishing at no row where `ω - c` vanishes
generates the unit ideal together with `ω - c`. -/
theorem exists_unit_combination_of_rows (hm2 : 2 ≤ m) (z : VOA.A (V2mPlus m hm)) (c : ℂ)
    (hsep : ∀ (i : Label m) (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ), HasValues m hm i χ →
      ((weight m i : ℚ) : ℂ) = c → χ z ≠ 0) :
    ∃ ξ₁ ξ₂ : VOA.A (V2mPlus m hm),
      ξ₁ * z + ξ₂ * (generator m hm 0 - algebraMap ℂ _ c) = 1 := by
  classical
  obtain ⟨χ, hχ, hinj⟩ := exists_characterTable m hm hm2
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  have hdim : Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤ Fintype.card (Label m) := by
    rw [V2mPlus_zhu_finrank m hm hm2, card_label m hm]
  let e := characterAlgEquiv χ hinj hdim
  have he_apply : ∀ r i, e r i = χ i r := fun _ _ => rfl
  have hrow : ∀ i, χ i z = 0 → χ i (generator m hm 0) - c ≠ 0 := by
    intro i hzi h1
    rw [hasValues_omega m hm (hχ i), sub_eq_zero] at h1
    exact hsep i (χ i) (hχ i) h1 hzi
  let ξ₁ : VOA.A (V2mPlus m hm) :=
    e.symm (fun i => if χ i z = 0 then 0 else (χ i z)⁻¹)
  let ξ₂ : VOA.A (V2mPlus m hm) :=
    e.symm (fun i => if χ i z = 0 then (χ i (generator m hm 0) - c)⁻¹ else 0)
  refine ⟨ξ₁, ξ₂, ?_⟩
  apply e.injective
  funext i
  rw [map_add, map_mul, map_mul, map_one, map_sub, AlgEquiv.commutes,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, Pi.sub_apply, he_apply,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hzi : χ i z = 0
  · rw [if_pos hzi, if_pos hzi, hzi, zero_mul, zero_add]
    exact inv_mul_cancel₀ (hrow i hzi)
  · rw [if_neg hzi, if_neg hzi, zero_mul, add_zero]
    exact inv_mul_cancel₀ hzi

/-- Unit combination for `zetaE` at weight one. -/
theorem exists_unit_combination (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) :
    ∃ ξ₁ ξ₂ : VOA.A (V2mPlus m hm),
      ξ₁ * zetaE m hm + ξ₂ * (generator m hm 0 - algebraMap ℂ _ 1) = 1 := by
  apply exists_unit_combination_of_rows m hm hm2
  intro i χ hχ hw hz
  have hw' : weight m i = 1 := by exact_mod_cast hw
  have hi := hw1 i hw'
  subst hi
  rw [sign_zetaE m hm hm2 χ hχ] at hz
  exact (mul_ne_zero two_ne_zero (pow_ne_zero 2 (cc_ne_zero m hm))) hz

/-- On a top vector, the generator `ω` acts by `L(0)`. -/
theorem topEvaluation_omega {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {y : M} (hy : y ∈ Omega A) :
    topEvaluation A y hy (generator m hm 0) = L0 A y := by
  change oLevW A 0 (V2mPlus m hm).conformalVector y = _
  rw [oLevW_homogeneous A 0 (V2mPlus m hm).conformal_mem]
  rfl

/-- If `z` and `ω - c` generate the unit ideal, a top vector of `L(0)`-eigenvalue `c`
annihilated by `z` vanishes. -/
theorem top_eq_zero_of_unit {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {y : M} (hy : y ∈ Omega A) (c : ℂ)
    (hL : L0 A y = c • y) (z ξ₁ ξ₂ : VOA.A (V2mPlus m hm))
    (hunit : ξ₁ * z + ξ₂ * (generator m hm 0 - algebraMap ℂ _ c) = 1)
    (hz : topEvaluation A y hy z = 0) : y = 0 := by
  set f := topEvaluation A y hy
  have hω : f (generator m hm 0 - algebraMap ℂ _ c) = 0 := by
    rw [map_sub, topEvaluation_omega m hm A hy, Algebra.algebraMap_eq_smul_one, map_smul,
      topEvaluation_one, hL, sub_self]
  have hy1 : y = f 1 := (topEvaluation_one A y hy).symm
  rw [hy1, ← hunit, map_add]
  obtain ⟨s₁, hs₁⟩ := VOA.mk_surjective (V2mPlus m hm) ξ₁
  obtain ⟨s₂, hs₂⟩ := VOA.mk_surjective (V2mPlus m hm) ξ₂
  rw [← hs₁, ← hs₂, topEvaluation_mk_mul, topEvaluation_mk_mul, hz, hω, map_zero, map_zero,
    add_zero]

/-- A weight-one top vector killed by `zetaE` vanishes (only the sign row at weight one). -/
theorem weightOne_top_eq_zero (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
    {y : M} (hy : y ∈ Omega A) (hL : L0 A y = y)
    (hz : topEvaluation A y hy (zetaE m hm) = 0) : y = 0 := by
  obtain ⟨ξ₁, ξ₂, hunit⟩ := exists_unit_combination m hm hm2 hw1
  exact top_eq_zero_of_unit m hm A hy 1 (by rw [one_smul]; exact hL) _ ξ₁ ξ₂ hunit hz

/-- **The translation of the generalized vacuum lift vanishes** (kernel bottom one). -/
theorem translation_zero_of_onlySign (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m)
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
  apply weightOne_top_eq_zero m hm hm2 hw1 A hyΩ ht
  rw [← telescopeE_eq m hm A hyΩ]
  exact translation_telescope A π 1 hb (by norm_num) hx he (EP_mem_grading m hm)
    (EP_mem_grading m hm) m (2 * m - 2) rfl hm (by omega)

/-- **`W₂ v = 0`** (`VacuumWeightFourAnnihilation`), for every `m` with only the sign row
at weight one. -/
theorem vacuumWeightFourAnnihilation_of_onlySign (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) :
    VacuumWeightFourAnnihilation m hm := by
  intro M _ _ A P _ _ hb _ π hk x hx he
  have hb' : FactorBottom A ⊥ (modeComap π ⊥) 1 := by rw [hk]; exact hb
  have ht := translation_zero_of_onlySign m hm hm2 hw1 A π hb' hx he
  exact nonnegative_modes_zero_of_translation_zero A ht _ 2 (by norm_num)

/-- **The sign-kernel / vacuum-quotient ordered pair splits.** -/
theorem pairSplitting_sign_vacuum (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) :
    PairSplitting m hm (.inr 1) (.inr 0) :=
  (vacuumWeightFourAnnihilation_iff_sign m hm hm2).mp
    (vacuumWeightFourAnnihilation_of_onlySign m hm hm2 hw1)

/-- With the sign pair, every positive-integral vacuum-quotient row splits. -/
theorem vacuum_quotient_family_of_onlySign (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) :
    ∀ i : Label m, (.inr 0, i) ∈ positivePairs m → PairSplitting m hm i (.inr 0) :=
  (vacuum_quotient_family_iff_weightFour m hm hm2).mpr
    (vacuumWeightFourAnnihilation_of_onlySign m hm hm2 hw1)

end VOA.Classification.COne.PlusRatSign
