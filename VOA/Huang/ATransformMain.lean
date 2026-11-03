/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ATransformTwist

/-!
# The FHL `A`-transform of intertwining operators (FHL Prop. 5.5.2)

For an intertwining operator `𝒴` of type `(M₃ / M₁ M₂)` the `A`-transform `𝒴ᴬ` of type
`(M₂' / M₁ M₃')` is defined by

  `⟨𝒴ᴬₙ(w) f, y⟩ = ⟨f, 𝒴°ₙ(w) y⟩`,   `𝒴°ₙ(w) = e^{πiα} Σ_t (t!)⁻¹ 𝒴_{2α−n−2−t}(L(1)ᵗ w)`

for `w ∈ (M₁)_α`, `f ∈ M₃'`, `y ∈ M₂` (FHL (5.5.4), `A_{(0)}`: the branch `e^{πi}` of `−1`).
On a homogeneous `w` and `f ∈ (M₃')_γ` the functional `y ↦ ⟨f, 𝒴°ₙ(w) y⟩` lives on the single
weight `γ − n − 1 + α` of `M₂`, so `𝒴ᴬₙ(w) f ∈ M₂'` (`Atrans`).

* `atrans_pairing` — the defining pairing identity;
* `weightCompatible_atrans` — the weight bookkeeping (hence truncation);
* `isIntertwiningOperator_atrans` — `𝒴ᴬ` is an intertwining operator: its Jacobi identity is
  the transpose of the opposite Jacobi identity `opp_jacobi`, and the `L(−1)`-derivative property
  follows from Jacobi plus weights (`isIntertwiningOperator_of_weightCompatible_jacobi`);
* `atransMap : I(M₃ / M₁ M₂) →ₗ I(M₂' / M₁ M₃')`, **injective** (`atransMap_injective`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.ATransform

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiRegular VOA.Huang.LiFusion
open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
  (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃)

/-! ## The definition -/

/-- The `(α, γ)`-component: `(w, g) ↦ ι_{γ−n−1+α}(g ∘ π_γ ∘ 𝒴°ₙ(w))`. -/
noncomputable def acomp (Y : IntertwiningModes M₁ M₂ M₃) (n α γ : ℂ) :
    M₁ →ₗ[ℂ] Module.Dual ℂ (A₃.weight γ) →ₗ[ℂ] RestrictedDual A₂ :=
  LinearMap.mk₂ ℂ (fun w g => iota A₂ (γ - n - 1 + α)
      ((g.comp (internalProjTo A₃.isInternal γ)).comp (twI A₁ Y α n w)))
    (fun w w' g => by simp only [map_add, LinearMap.comp_add])
    (fun c w g => by simp only [map_smul, LinearMap.comp_smul])
    (fun w g g' => by simp only [LinearMap.add_comp, map_add])
    (fun c w g => by simp only [LinearMap.smul_comp, map_smul])

/-- The `α`-component, summed over the weights of `M₃'`. -/
noncomputable def atransL (Y : IntertwiningModes M₁ M₂ M₃) (n α : ℂ) :
    M₁ →ₗ[ℂ] RestrictedDual A₃ →ₗ[ℂ] RestrictedDual A₂ :=
  (DirectSum.toModule ℂ ℂ (M₁ →ₗ[ℂ] RestrictedDual A₂)
    (fun γ => (acomp A₁ A₂ A₃ Y n α γ).flip)).flip

/-- **The FHL `A`-transform** `𝒴ᴬ` of type `(M₂' / M₁ M₃')`. -/
noncomputable def atrans (Y : IntertwiningModes M₁ M₂ M₃) :
    IntertwiningModes M₁ (RestrictedDual A₃) (RestrictedDual A₂) := fun n =>
  letI := DirectSum.IsInternal.chooseDecomposition A₁.weight A₁.isInternal
  (DirectSum.toModule ℂ ℂ _
    (fun α => (atransL A₁ A₂ A₃ Y n α).comp (A₁.weight α).subtype)).comp
    (DirectSum.decomposeLinearEquiv A₁.weight).toLinearMap

variable {A₁ A₂ A₃}

theorem atrans_homog (Y : IntertwiningModes M₁ M₂ M₃) (n : ℂ) {α : ℂ} {w : M₁}
    (hw : w ∈ A₁.weight α) : atrans A₁ A₂ A₃ Y n w = atransL A₁ A₂ A₃ Y n α w := by
  letI := DirectSum.IsInternal.chooseDecomposition A₁.weight A₁.isInternal
  change (DirectSum.toModule ℂ ℂ _ _) (DirectSum.decompose A₁.weight w) = _
  rw [DirectSum.decompose_of_mem A₁.weight hw, ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]
  rfl

theorem atransL_lof (Y : IntertwiningModes M₁ M₂ M₃) (n α : ℂ) (w : M₁) (γ : ℂ)
    (g : Module.Dual ℂ (A₃.weight γ)) :
    atransL A₁ A₂ A₃ Y n α w (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A₃.weight β)) γ g)
      = iota A₂ (γ - n - 1 + α)
          ((g.comp (internalProjTo A₃.isInternal γ)).comp (twI A₁ Y α n w)) := by
  change (DirectSum.toModule ℂ ℂ (M₁ →ₗ[ℂ] RestrictedDual A₂)
    (fun γ => (acomp A₁ A₂ A₃ Y n α γ).flip) (DirectSum.lof ℂ ℂ _ γ g)) w = _
  rw [DirectSum.toModule_lof]
  rfl

/-! ## Weights -/

/-- **Weight compatibility** of the `A`-transform: `𝒴ᴬₙ(w) f ∈ (M₂')_{α+γ−n−1}`. -/
theorem weightCompatible_atrans (Y : IntertwiningModes M₁ M₂ M₃) :
    WeightCompatible A₁ (contragredientModule A₃) (contragredientModule A₂)
      (atrans A₁ A₂ A₃ Y) := by
  intro α γ w f hw hf n
  obtain ⟨g, rfl⟩ := hf
  rw [atrans_homog Y n hw]
  erw [atransL_lof]
  rw [show α + γ - n - 1 = γ - n - 1 + α by ring]
  exact ⟨restrictToWeight A₂ (γ - n - 1 + α)
    ((g.comp (internalProjTo A₃.isInternal γ)).comp (twI A₁ Y α n w)), rfl⟩

/-! ## The pairing identity -/

section Pairing

variable {Y : IntertwiningModes M₁ M₂ M₃}

/-- Only the weight `γ − n − 1 + α` of `y` contributes to the `γ`-component of `𝒴°ₙ(w) y`. -/
theorem proj_twI (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) {α : ℂ} {w : M₁}
    (hw : w ∈ A₁.weight α) (γ n : ℂ) (y : M₂) :
    internalProjTo A₃.isInternal γ (twI A₁ Y α n w (weightProjection A₂ (γ - n - 1 + α) y))
      = internalProjTo A₃.isInternal γ (twI A₁ Y α n w y) := by
  induction y using FusionTop.induction_weight (A₁ := A₂) with
  | h0 => simp only [map_zero]
  | hadd y y' hy hy' => simp only [map_add, hy, hy']
  | hhom β y hy =>
    by_cases h : β = γ - n - 1 + α
    · subst h
      rw [weightProjection_of_mem A₂ hy]
    · rw [weightProjection_of_mem_ne A₂ hy (Ne.symm h)]
      simp only [map_zero]
      symm
      apply internalProjTo_eq_zero_of_ne A₃ (twI_mem_weight hY hw hy n)
      intro hc
      apply h
      rw [hc]; ring

/-- **The defining pairing of the `A`-transform**:
`⟨𝒴ᴬₙ(w) f, y⟩ = ⟨f, 𝒴°ₙ(w) y⟩` for `w ∈ (M₁)_α`. -/
theorem atrans_pairing (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (n : ℂ) {α : ℂ} {w : M₁}
    (hw : w ∈ A₁.weight α) (f : RestrictedDual A₃) (y : M₂) :
    dualPairing A₂ y (atrans A₁ A₂ A₃ Y n w f) = dualPairing A₃ (twI A₁ Y α n w y) f := by
  rw [atrans_homog Y n hw]
  induction f using DirectSum.induction_on with
  | zero => erw [map_zero]
  | of γ g =>
    rw [← DirectSum.lof_eq_of ℂ]
    erw [atransL_lof]
    rw [dualPairing_iota, dualPairing_lof]
    simp only [LinearMap.comp_apply]
    rw [proj_twI hY hw γ n y]
  | add f f' hf hf' => erw [map_add, map_add, map_add, hf, hf']

end Pairing

/-! ## Truncation of the twisted modes in the index -/

theorem twI_trunc {Y : IntertwiningModes M₁ M₂ M₃} (hY : IsIntertwiningOperator A₁ A₂ A₃ Y)
    (α : ℂ) (w : M₁) (y : M₂) (c : ℂ) :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i → twI A₁ Y α (c - i) w y = 0 := by
  classical
  obtain ⟨J, hJ⟩ := L1m_pow_eventually A₁ w
  choose Nf hNf using fun t : ℕ => hY.truncation ((L1m A₁ ^ t) w) y (2 * α - c - 2 - t)
  refine ⟨∑ t ∈ Finset.range J, ((Nf t).natAbs : ℤ), fun i hi => ?_⟩
  rw [twI_apply_eq_sum A₁ Y α _ hJ y]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero (fun t ht => ?_))
  have hle : ((Nf t).natAbs : ℤ) ≤ ∑ t ∈ Finset.range J, ((Nf t).natAbs : ℤ) :=
    Finset.single_le_sum (f := fun t => ((Nf t).natAbs : ℤ)) (fun _ _ => by positivity) ht
  have h0 := hNf t i (by have := Int.le_natAbs (a := Nf t); omega)
  rw [show 2 * α - (c - i) - 2 - t = 2 * α - c - 2 - t + i by ring, h0, smul_zero]

/-! ## The Jacobi identity -/

section Jacobi

variable {Y : IntertwiningModes M₁ M₂ M₃}

/-- **The Jacobi identity of the `A`-transform**, the transpose of `opp_jacobi`. -/
theorem modeJacobi_atrans (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    ModeJacobi A₁ (contragredientModule A₃) (contragredientModule A₂) (atrans A₁ A₂ A₃ Y) := by
  have hwc := weightCompatible_atrans (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) Y
  have htr := truncation_of_weightCompatible hwc
  intro a x f l m n
  refine modeJacobiAt_of_homog htr l m n (fun k a ha α β x hx f _ => ?_) a x f
  unfold ModeJacobiAt
  refine restrictedDual_ext A₂ (fun z => ?_)
  rw [map_finsum (dualPairing A₂ z) (IsIntertwiningOperator.jacL_support_finite htr a x f l m n),
    map_finsum (dualPairing A₂ z) (IsIntertwiningOperator.jacR_support_finite (A₁ := A₁)
      (atrans A₁ A₂ A₃ Y) a x f l m n)]
  -- the vector families of the opposite Jacobi identity
  set OJL : ℤ → M₃ := fun i => (negOnePow i * cbz l i) •
    (twI A₁ Y α (n + i) x (oppB A₂ a (l + m - i) z)
      - negOnePow l • oppB A₃ a (m + i) (twI A₁ Y α (l + n - i) x z)) with hOJL
  set OJR : ℤ → M₃ := fun i => cbz m i •
    twI A₁ Y (α + k - (l + i) - 1) (m + n - i) (mode (A₁.YM a) (l + i) x) z with hOJR
  have hLt : ∀ i, dualPairing A₂ z (IsIntertwiningOperator.jacL (contragredientModule A₃)
      (contragredientModule A₂) (atrans A₁ A₂ A₃ Y) a x f l m n i) = dpx A₃ f (OJL i) := by
    intro i
    simp only [IsIntertwiningOperator.jacL, map_smul, map_sub, hOJL]
    rw [dualPairing_contra_mode, atrans_pairing hY _ hx, atrans_pairing hY _ hx,
      dualPairing_contra_mode]
    rfl
  have hRt : ∀ i, dualPairing A₂ z (IsIntertwiningOperator.jacR A₁ (atrans A₁ A₂ A₃ Y)
      a x f l m n i) = dpx A₃ f (OJR i) := by
    intro i
    have hmem : mode (A₁.YM a) (l + i) x ∈ A₁.weight (α + k - (l + i) - 1) := by
      have := mode_mem_weight A₁ ha hx (l + i)
      convert this using 2
      push_cast; ring
    simp only [IsIntertwiningOperator.jacR, map_smul, hOJR]
    rw [atrans_pairing hY _ hmem]
    rfl
  have hfinL : (Function.support OJL).Finite := by
    obtain ⟨K, hK⟩ := oppB_trunc A₂ a z
    obtain ⟨N, hN⟩ := twI_trunc hY α x z ((l : ℂ) + n)
    refine (Set.finite_Icc 0 (max (l + m - K) N)).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · simp only [hOJL, cbz_apply_neg l h, mul_zero, zero_smul]
    · simp only [hOJL]
      rw [hK _ (by omega), hN i (by omega)]
      simp only [map_zero, smul_zero, sub_zero]
  have hfinR : (Function.support OJR).Finite := by
    obtain ⟨N, hN⟩ := A₁.toWeakModule.truncation a x
    refine (Set.finite_Icc 0 (N - l)).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · simp only [hOJR, cbz_apply_neg m h, zero_smul]
    · simp only [hOJR]
      rw [hN (l + i) (by omega)]
      simp only [map_zero, LinearMap.zero_apply, smul_zero]
  rw [finsum_congr hLt, finsum_congr hRt, ← map_finsum _ hfinL, ← map_finsum _ hfinR]
  congr 1
  exact opp_jacobi hY ha α x z l m n

/-- **The `A`-transform is an intertwining operator** of type `(M₂' / M₁ M₃')`
(FHL Prop. 5.5.2). -/
theorem isIntertwiningOperator_atrans (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    IsIntertwiningOperator A₁ (contragredientModule A₃) (contragredientModule A₂)
      (atrans A₁ A₂ A₃ Y) :=
  isIntertwiningOperator_of_weightCompatible_jacobi (weightCompatible_atrans Y)
    (modeJacobi_atrans hY)

end Jacobi

/-! ## The linear map and its injectivity -/

section Map

/-- A vector all of whose pairings with the restricted dual vanish is zero. -/
theorem eq_zero_of_pairing {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)
    {x : M} (h : ∀ f : RestrictedDual N, dualPairing N x f = 0) : x = 0 := by
  classical
  have hproj : ∀ γ, internalProjTo N.isInternal γ x = 0 := by
    intro γ
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro g
    have := h (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g)
    rwa [dualPairing_lof] at this
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  have hdec : DirectSum.decompose N.weight x = 0 := by
    ext γ
    exact congrArg Subtype.val (hproj γ)
  rw [← (DirectSum.decompose N.weight).symm_apply_apply x, hdec]
  exact map_zero (DirectSum.decomposeAddEquiv N.weight).symm

variable {Y Y' : IntertwiningModes M₁ M₂ M₃}

theorem atrans_ext {Z Z' : IntertwiningModes M₁ (RestrictedDual A₃) (RestrictedDual A₂)}
    (h : ∀ n α w, w ∈ A₁.weight α → ∀ f y,
      dualPairing A₂ y (Z n w f) = dualPairing A₂ y (Z' n w f)) :
    Z = Z' := by
  funext n
  refine LinearMap.ext (fun w => ?_)
  induction w using FusionTop.induction_weight (A₁ := A₁) with
  | h0 => simp only [map_zero]
  | hadd w w' hw hw' => simp only [map_add, hw, hw']
  | hhom α w hw =>
    refine LinearMap.ext (fun f => restrictedDual_ext A₂ (fun y => h n α w hw f y))

theorem atrans_add (hY : IsIntertwiningOperator A₁ A₂ A₃ Y)
    (hY' : IsIntertwiningOperator A₁ A₂ A₃ Y') :
    atrans A₁ A₂ A₃ (Y + Y') = atrans A₁ A₂ A₃ Y + atrans A₁ A₂ A₃ Y' := by
  have hYY' : IsIntertwiningOperator A₁ A₂ A₃ (Y + Y') :=
    (intertwiningSpace A₁ A₂ A₃).add_mem hY hY'
  refine atrans_ext (A₁ := A₁) (fun n α w hw f y => ?_)
  rw [atrans_pairing hYY' n hw, Pi.add_apply, LinearMap.add_apply, LinearMap.add_apply, map_add,
    atrans_pairing hY n hw, atrans_pairing hY' n hw, twI_add_Y, dualPairing_add_left]

theorem atrans_smul (c : ℂ) (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    atrans A₁ A₂ A₃ (c • Y) = c • atrans A₁ A₂ A₃ Y := by
  have hcY : IsIntertwiningOperator A₁ A₂ A₃ (c • Y) :=
    (intertwiningSpace A₁ A₂ A₃).smul_mem c hY
  refine atrans_ext (A₁ := A₁) (fun n α w hw f y => ?_)
  rw [atrans_pairing hcY n hw, Pi.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    map_smul, atrans_pairing hY n hw, twI_smul_Y, dualPairing_smul_left]

/-- If all twisted modes of `𝒴` vanish on homogeneous vectors then `𝒴 = 0`. -/
theorem eq_zero_of_twI (h : ∀ β z, z ∈ A₁.weight β → ∀ n y, twI A₁ Y β n z y = 0) : Y = 0 := by
  have key : ∀ d : ℕ, ∀ β z, z ∈ A₁.weight β → (L1m A₁ ^ d) z = 0 → ∀ k y, Y k z y = 0 := by
    intro d
    induction d with
    | zero =>
      intro β z _ hz k y
      rw [pow_zero, Module.End.one_apply] at hz
      rw [hz, map_zero, LinearMap.zero_apply]
    | succ d ih =>
      intro β z hz hd k y
      have hJ : ∀ t, d + 1 ≤ t → (L1m A₁ ^ t) z = 0 := fun t ht => pow_apply_eq_zero_of_le hd ht
      have hhigh : ∀ t : ℕ, ∀ k' : ℂ, Y k' ((L1m A₁ ^ (t + 1)) z) y = 0 := by
        intro t k'
        refine ih (β - (t + 1 : ℕ)) _ (L1m_pow_mem A₁ hz (t + 1)) ?_ k' y
        rw [← Module.End.mul_apply, ← pow_add]
        exact pow_apply_eq_zero_of_le hd (by omega)
      have h0 := h β z hz (2 * β - k - 2) y
      rw [twI_apply_eq_sum A₁ Y β _ hJ y, Finset.sum_range_succ'] at h0
      simp only [hhigh, smul_zero, Finset.sum_const_zero, zero_add, Nat.factorial_zero,
        Nat.cast_one, inv_one, one_smul, pow_zero, Module.End.one_apply, CharP.cast_eq_zero,
        sub_zero] at h0
      rw [show 2 * β - (2 * β - k - 2) - 2 = k by ring] at h0
      exact (smul_eq_zero.mp h0).resolve_left (phase_ne_zero β)
  funext k
  refine LinearMap.ext (fun w => LinearMap.ext (fun y => ?_))
  induction w using FusionTop.induction_weight (A₁ := A₁) with
  | h0 => simp only [map_zero, LinearMap.zero_apply, Pi.zero_apply]
  | hadd w w' hw hw' =>
    simp only [map_add, LinearMap.add_apply, hw, hw', add_zero, Pi.zero_apply,
      LinearMap.zero_apply]
  | hhom β w hw =>
    obtain ⟨J, hJ⟩ := L1m_pow_eventually A₁ w
    rw [key J β w hw (hJ J le_rfl) k y]
    rfl

/-- `𝒴ᴬ = 0 ⟹ 𝒴 = 0`. -/
theorem eq_zero_of_atrans_eq_zero (hY : IsIntertwiningOperator A₁ A₂ A₃ Y)
    (h0 : atrans A₁ A₂ A₃ Y = 0) : Y = 0 := by
  refine eq_zero_of_twI (A₁ := A₁) (fun β z hz n y => eq_zero_of_pairing A₃ (fun f => ?_))
  rw [← atrans_pairing hY n hz, h0]
  simp only [Pi.zero_apply, LinearMap.zero_apply]
  exact map_zero (dualPairing A₂ y)

variable (A₁ A₂ A₃)

/-- **The `A`-transform as a linear map** `I(M₃ / M₁ M₂) → I(M₂' / M₁ M₃')`. -/
noncomputable def atransMap : intertwiningSpace A₁ A₂ A₃ →ₗ[ℂ]
    intertwiningSpace A₁ (contragredientModule A₃) (contragredientModule A₂) where
  toFun Y := ⟨atrans A₁ A₂ A₃ Y.1, isIntertwiningOperator_atrans Y.2⟩
  map_add' Y Y' := Subtype.ext (atrans_add Y.2 Y'.2)
  map_smul' c Y := Subtype.ext (atrans_smul c Y.2)

/-- **The `A`-transform is injective.** -/
theorem atransMap_injective : Function.Injective (atransMap A₁ A₂ A₃) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  apply Subtype.ext
  exact eq_zero_of_atrans_eq_zero Y.2 (congrArg Subtype.val hY)

/-- **FHL Prop. 5.5.2, inequality form**: if `I(M₂' / M₁ M₃')` is finite-dimensional then so
is `I(M₃ / M₁ M₂)`, and `N^{M₃}_{M₁M₂} ≤ N^{M₂'}_{M₁M₃'}`. -/
theorem finiteDimensional_of_atrans
    [FiniteDimensional ℂ (intertwiningSpace A₁ (contragredientModule A₃)
      (contragredientModule A₂))] :
    FiniteDimensional ℂ (intertwiningSpace A₁ A₂ A₃) :=
  Module.Finite.of_injective (atransMap A₁ A₂ A₃) (atransMap_injective A₁ A₂ A₃)

theorem fusionRule_le_atrans
    [FiniteDimensional ℂ (intertwiningSpace A₁ (contragredientModule A₃)
      (contragredientModule A₂))] :
    fusionRule A₁ A₂ A₃ ≤ fusionRule A₁ (contragredientModule A₃) (contragredientModule A₂) :=
  LinearMap.finrank_le_finrank_of_injective (atransMap_injective A₁ A₂ A₃)

end Map

end VOA.Huang.ATransform
