/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStark
import VOA.Classification.COne.ThetaGalois

/-!
# Serre–Stark, stage S2-1: theta series at every cusp, and the weight-one form `f θ`

* `norm_rankOneTheta_le`: `‖θ_{n₀,r,t}(τ)‖` is bounded on `Im τ ≥ 1`;
* `weilTheta_cusp_bound`, `rankOneTheta_cusp_bound`, `thetaRef_cusp_bound`: for every
  `γ ∈ SL₂(ℤ)`, `‖θ_{n₀,r,t}(γτ)‖ ≤ C ‖cτ + d‖^{1/2}` on `Im τ ≥ 1` (Weil words + `|η(γτ)|`);
* `isThetaTypeForm_thetaRef`: `θ` itself is a θ-type form of every level;
* `IsThetaTypeForm.weightOneForm`: for `4 ∣ N`, `f θ` as a Mathlib `ModularForm (Γ₁(N)) 1`.
-/

open Complex Filter Topology UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace VOA.Classification.COne

/-! ## Uniform bounds for theta series -/

theorem norm_rankOneThetaTerm (n₀ r : ℤ) (t : ℝ) (τ : ℂ) (m : ℤ) :
    ‖rankOneThetaTerm n₀ r t τ m‖ =
      Real.exp (-(2 * Real.pi * t * (((n₀ + r * m : ℤ) : ℝ)) ^ 2 * τ.im)) := by
  rw [rankOneThetaTerm, Complex.norm_exp]
  congr 1
  have : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * ((n₀ + r * m : ℤ) : ℂ) ^ 2 * τ) =
      ((2 * Real.pi * t * (((n₀ + r * m : ℤ) : ℝ)) ^ 2 : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  simp

theorem norm_rankOneThetaTerm_le (n₀ r : ℤ) {t : ℝ} (ht : 0 ≤ t) {τ : ℂ} (hτ : 1 ≤ τ.im)
    (m : ℤ) : ‖rankOneThetaTerm n₀ r t τ m‖ ≤ ‖rankOneThetaTerm n₀ r t Complex.I m‖ := by
  rw [norm_rankOneThetaTerm, norm_rankOneThetaTerm, Complex.I_im]
  refine Real.exp_le_exp.2 ?_
  have h0 : 0 ≤ 2 * Real.pi * t * (((n₀ + r * m : ℤ) : ℝ)) ^ 2 := by positivity
  nlinarith

/-- `‖θ_{n₀,r,t}(τ)‖ ≤ Σ_m ‖term(i)‖` on `Im τ ≥ 1`. -/
theorem norm_rankOneTheta_le (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 1 ≤ τ.im) :
    ‖rankOneTheta n₀ r t τ‖ ≤ ∑' m, ‖rankOneThetaTerm n₀ r t Complex.I m‖ := by
  have hs : Summable fun m => ‖rankOneThetaTerm n₀ r t Complex.I m‖ :=
    (summable_rankOneThetaTerm n₀ hr ht (τ := Complex.I) (by simp)).norm
  have hle := norm_rankOneThetaTerm_le n₀ r ht.le hτ
  have hs' : Summable fun m => ‖rankOneThetaTerm n₀ r t τ m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
  exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hle hs)

/-! ## Cusp bounds through Weil words -/

/-- `‖Θ_{N,μ}(γτ)‖ ≤ C ‖cτ + d‖^{1/2}` on `Im τ ≥ 1`, for every `γ ∈ SL₂(ℤ)`. -/
theorem weilTheta_cusp_bound {N : ℕ} (hN : 0 < N) (μ : ℤ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖weilTheta N μ (mobius γ τ)‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨A, hA⟩ := exists_weilWord N γ
  set μ' := weilIdx hN μ
  have hr : (((2 * N : ℕ)) : ℤ) ≠ 0 := by exact_mod_cast (show 2 * N ≠ 0 by omega)
  have ht : (0 : ℝ) < 1 / (4 * (N : ℝ)) := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 hN
    positivity
  refine ⟨∑ j : Fin (2 * N), ‖A μ' j‖ *
    ∑' m, ‖rankOneThetaTerm ((j : ℕ) : ℤ) ((2 * N : ℕ) : ℤ) (1 / (4 * (N : ℝ))) Complex.I m‖,
    fun τ hτ => ?_⟩
  have hτ0 : 0 < τ.im := by linarith
  have hη : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ0
  have hηγ : ModularForm.eta (mobius γ τ) ≠ 0 := ModularForm.eta_ne_zero (im_mobius_pos γ hτ0)
  have hT := weilWord_transform hN hA hτ0 μ'
  rw [weilVec_congr N (weilIdx_modEq hN μ)] at hT
  have hrepr : weilTheta N μ (mobius γ τ) = ModularForm.eta (mobius γ τ) / ModularForm.eta τ *
      ∑ j, A μ' j * weilTheta N ((j : ℕ) : ℤ) τ := by
    simp only [weilVec] at hT
    rw [Finset.mul_sum]
    have hT' : weilTheta N μ (mobius γ τ) =
        ModularForm.eta (mobius γ τ) * ∑ j, A μ' j * (weilTheta N ((j : ℕ) : ℤ) τ /
          ModularForm.eta τ) := by
      rw [← hT]; field_simp
    rw [hT', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have hnorm : ‖ModularForm.eta (mobius γ τ) / ModularForm.eta τ‖ =
      ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
    rw [norm_div, norm_eta_mobius γ hτ0, mul_div_assoc, div_self (norm_ne_zero_iff.2 hη),
      mul_one]
  rw [hrepr, norm_mul, hnorm, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact norm_rankOneTheta_le _ hr ht hτ

/-- Cusp bound for `θ_{n₀,r,t}`, `r, t ≥ 1`. -/
theorem rankOneTheta_cusp_bound (n₀ : ℤ) {r t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖rankOneTheta n₀ r t (mobius γ τ)‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := weilTheta_cusp_bound (N := t * r ^ 2) (by positivity) (2 * t * r * n₀) γ
  exact ⟨C, fun τ hτ => by rw [rankOneTheta_eq_weilTheta n₀ hr ht]; exact hC τ hτ⟩

theorem thetaRef_eq_rankOneTheta_nat (τ : ℂ) :
    thetaRef τ = rankOneTheta 0 ((1 : ℕ) : ℤ) ((1 : ℕ) : ℝ) τ := by
  simp [thetaRef]

/-- `‖θ(γτ)‖ ≤ C ‖cτ + d‖^{1/2}` on `Im τ ≥ 1`. -/
theorem thetaRef_cusp_bound (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖thetaRef (mobius γ τ)‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := rankOneTheta_cusp_bound 0 one_pos one_pos γ
  exact ⟨C, fun τ hτ => by rw [thetaRef_eq_rankOneTheta_nat]; exact hC τ hτ⟩

/-- `θ` is a θ-type form of every level. -/
theorem isThetaTypeForm_thetaRef (N : ℕ) : IsThetaTypeForm N thetaRef where
  holo := differentiableOn_thetaRef
  multiplier _ _ _ _ := rfl
  cusps := thetaRef_cusp_bound

/-! ## The weight-one modular form `f θ` -/

namespace IsThetaTypeForm

variable {N : ℕ} {f : ℂ → ℂ}

theorem denom_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by
  simp [denom]

/-- Weight-one cusp bound: `‖f(γτ) θ(γτ)‖ ≤ C ‖cτ + d‖` on `Im τ ≥ 1`. -/
theorem cusp_bound_mul_theta (hf : IsThetaTypeForm N f) (γ : SL(2, ℤ)) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖f (mobius γ τ) * thetaRef (mobius γ τ)‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
  obtain ⟨C, hC⟩ := hf.cusps γ
  obtain ⟨D, hD⟩ := thetaRef_cusp_bound γ
  refine ⟨C * D, fun τ hτ => ?_⟩
  have hτ0 : 0 < τ.im := by linarith
  have hj : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := norm_pos_iff.2 (denom_ne_zero γ hτ0)
  set x := ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ)
  have hx : x * x = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    rw [← Real.rpow_add hj]; norm_num
  have h1 := hC τ hτ
  have h2 := hD τ hτ
  rw [norm_mul, ← hx]
  calc ‖f (mobius γ τ)‖ * ‖thetaRef (mobius γ τ)‖ ≤ (C * x) * (D * x) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = C * D * (x * x) := by ring

/-- `f θ` as a slash-invariant form of weight one for `Γ₁(N)`. -/
def weightOneSIF (h4 : 4 ∣ N) (hf : IsThetaTypeForm N f) :
    SlashInvariantForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 1 where
  toFun τ := f τ * thetaRef τ
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    ext τ
    change ((fun τ : ℍ => f τ * thetaRef τ) ∣[(1 : ℤ)] A) τ = _
    rw [ModularForm.SL_slash_apply, denom_eq,
      ← mobius_eq_smul, hf.weight_one h4 hA τ.2]
    have hd := denom_ne_zero A τ.2
    rw [zpow_neg, zpow_one]
    field_simp

theorem weightOneSIF_apply (h4 : 4 ∣ N) (hf : IsThetaTypeForm N f) (τ : ℍ) :
    weightOneSIF h4 hf τ = f τ * thetaRef τ := rfl

theorem mdifferentiable_mul_theta (hf : IsThetaTypeForm N f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ * thetaRef τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (hf.holo.mul differentiableOn_thetaRef).congr fun z hz => ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- **The weight-one form.** For `4 ∣ N` and `f` θ-type of level `N`, `f θ` is a holomorphic
modular form of weight one for `Γ₁(N)` (trivial character), as a Mathlib `ModularForm`. -/
def weightOneForm (h4 : 4 ∣ N) (hf : IsThetaTypeForm N f) :
    ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 1 where
  __ := weightOneSIF h4 hf
  holo' := hf.mdifferentiable_mul_theta
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c 𝒮ℒ := by
      have : (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
        rintro _ ⟨g, -, rfl⟩
        exact ⟨g, rfl⟩
      exact hc.mono this
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
    intro γ _
    obtain ⟨C, hC⟩ := hf.cusp_bound_mul_theta γ
    rw [UpperHalfPlane.isBoundedAtImInfty_iff]
    refine ⟨C, 1, fun τ hτ => ?_⟩
    rw [ModularForm.SL_slash_apply, denom_eq]
    change ‖f ((γ • τ : ℍ) : ℂ) * thetaRef ((γ • τ : ℍ) : ℂ) *
      ((γ 1 0 : ℂ) * τ + γ 1 1) ^ (-1 : ℤ)‖ ≤ C
    rw [← mobius_eq_smul, zpow_neg, zpow_one, norm_mul, norm_inv]
    have hj : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := norm_pos_iff.2 (denom_ne_zero γ τ.2)
    rw [mul_inv_le_iff₀ hj]
    exact hC τ hτ

theorem weightOneForm_apply (h4 : 4 ∣ N) (hf : IsThetaTypeForm N f) (τ : ℍ) :
    weightOneForm h4 hf τ = f τ * thetaRef τ := rfl

end IsThetaTypeForm

end VOA.Classification.COne
