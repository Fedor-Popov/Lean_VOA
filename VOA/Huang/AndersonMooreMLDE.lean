/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMooreWronskian
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# The modular linear differential equation of an `S`-closed family (Anderson–Moore, step 3)

Let `F_j = q^{ν_j} U_j` (`j < n`) be a family with pairwise distinct `ν_j`, `U_j(0) ≠ 0`, closed
under `S`: `F_i(−1/z) = Σ_j S_ij F_j(z)`.  Then

* `sq_det_eq_one`, `det_mul_prod_cube_eq_one` — the character of the Wronskian satisfies
  `s² = 1`, `(st)³ = 1` (`s = det S`, `t = Π e^{2πiν_j}`), from `S² = 1` and `(ST)³ = 1` acting on
  `ℍ`; hence `s⁶ = t⁶ = 1` and `6 Σ ν_j ∈ ℤ`;
* `exists_mlde` — there are **holomorphic level-one modular forms** `B` of weight `k` and `A_r`
  of weight `k + 2(n − r)`, `B ≢ 0`, with

    `B · ϑⁿ F_j = Σ_r A_r · ϑ^r F_j`   on `ℍ`, for every `j`.

  Explicitly `B = wr⁶ Δᴹ`, `A_r = wrc_r · wr⁵ · Δᴹ` (`wr` the modular Wronskian, `wrc_r` its Cramer
  minors, `M = |6Σν|`).

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

open Complex Filter Topology Matrix UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace VOA.Huang.AndersonMoore

open VOA

/-! ## Building level-one modular forms from functions on `ℂ` -/

/-- A function on `ℂ`, holomorphic on the upper half-plane, with the weight-`k` laws at `S` and `T`
and bounded at `i∞`, as a level-one modular form. -/
def mkLevelOne (g : ℂ → ℂ) (k : ℕ) (hg : DifferentiableOn ℂ g (imGT 0))
    (hS : ∀ z ∈ imGT 0, g (-1 / z) = z ^ k * g z) (hT : ∀ z ∈ imGT 0, g (z + 1) = g z)
    (hB : IsBoundedAtImInfty (fun τ : ℍ => g τ)) : ModularForm 𝒮ℒ (k : ℤ) :=
  have hS' : (fun τ : ℍ => g τ) ∣[(k : ℤ)] ModularGroup.S = fun τ : ℍ => g τ := by
    ext τ
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
    have hτ : (τ : ℂ) ∈ imGT 0 := τ.im_pos
    have h1 := hS τ hτ
    have hne : (τ : ℂ) ≠ 0 := τ.ne_zero
    change g ((-(τ : ℂ))⁻¹) * (τ : ℂ) ^ (-(k : ℤ)) = g τ
    rw [show (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) from by rw [inv_neg, neg_div, one_div], h1,
      zpow_neg, zpow_natCast]
    field_simp
  have hT' : (fun τ : ℍ => g τ) ∣[(k : ℤ)] ModularGroup.T = fun τ : ℍ => g τ := by
    ext τ
    rw [SL_slash_apply, UpperHalfPlane.modular_T_smul]
    have hd :
        UpperHalfPlane.denom (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) τ = 1 := by
      rw [ModularGroup.denom_apply, ModularGroup.T]
      simp
    rw [hd, one_zpow, mul_one, UpperHalfPlane.coe_vadd]
    rw [show ((1 : ℝ) : ℂ) + (τ : ℂ) = (τ : ℂ) + 1 from by push_cast; ring]
    exact hT τ τ.im_pos
  { toFun := fun τ : ℍ => g τ
    slash_action_eq' := fun A hA => by
      obtain ⟨A, rfl⟩ := hA
      exact SlashInvariantForm.slash_action_generators_SL2Z hS' hT' A
    holo' := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      refine hg.congr fun z hz => ?_
      simp [ofComplex_apply_of_im_pos hz]
    bdd_at_cusps' := fun hc => by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
      intro γ _
      rw [SlashInvariantForm.slash_action_generators_SL2Z hS' hT' γ]
      exact hB }

@[simp] theorem mkLevelOne_apply (g : ℂ → ℂ) (k : ℕ) (hg) (hS) (hT) (hB) (τ : ℍ) :
    mkLevelOne g k hg hS hT hB τ = g τ := rfl

/-! ## The character of the Wronskian -/

theorem pow_neg_one_mul_self_eq_one (n : ℕ) : (-1 : ℂ) ^ (n * (n - 1)) = 1 :=
  (Nat.even_mul_pred_self n).neg_one_pow

/-- `S² = 1` on `ℍ` forces `(det S)² = 1`. -/
theorem sq_det_eq_one {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : ∀ i, ∀ z ∈ imGT 0, f i (-1 / z) = ∑ j, S i j * f j z)
    {z₁ : ℂ} (hz₁ : z₁ ∈ imGT 0) (hW : wr f z₁ ≠ 0) : S.det ^ 2 = 1 := by
  have hz0 := ne_zero_of_mem_imGT hz₁
  have h1 := wr_S hf S hS (neg_one_div_mem_imGT hz₁)
  have h2 := wr_S hf S hS hz₁
  rw [show -1 / (-1 / z₁) = z₁ from by field_simp, h2] at h1
  have h3 : wr f z₁ * (1 - ((-1 / z₁) * z₁) ^ (n * (n - 1)) * S.det ^ 2) = 0 := by
    rw [mul_pow]; linear_combination h1
  rw [show (-1 / z₁) * z₁ = -1 from by field_simp, pow_neg_one_mul_self_eq_one, one_mul] at h3
  have := (mul_eq_zero.mp h3).resolve_left hW
  linear_combination -this

/-- `(ST)³ = 1` on `ℍ` forces `(det S · Π tⱼ)³ = 1`. -/
theorem det_mul_prod_cube_eq_one {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ i, ∀ z ∈ imGT 0, famF ν U i (-1 / z) = ∑ j, S i j * famF ν U j z)
    {z₁ : ℂ} (hz₁ : z₁ ∈ imGT 0) (hW : wr (famF ν U) z₁ ≠ 0) :
    (S.det * ∏ j, tvec ν j) ^ 3 = 1 := by
  set w := n * (n - 1)
  set c := S.det * ∏ j, tvec ν j
  have hf := analyticAt_famF ν hU
  have hφ : ∀ z ∈ imGT 0, wr (famF ν U) (-1 / (z + 1)) = (z + 1) ^ w * c * wr (famF ν U) z := by
    intro z hz
    rw [wr_S hf S hS (add_one_mem_imGT hz), wr_T ν hU hz]
    ring
  have hφmem : ∀ z ∈ imGT 0, -1 / (z + 1) ∈ imGT 0 := fun z hz =>
    neg_one_div_mem_imGT (add_one_mem_imGT hz)
  set z₂ := -1 / (z₁ + 1)
  set z₃ := -1 / (z₂ + 1)
  have hz₂ := hφmem z₁ hz₁
  have hz₃ := hφmem z₂ hz₂
  have h10 : z₁ + 1 ≠ 0 := ne_zero_of_mem_imGT (add_one_mem_imGT hz₁)
  have h0 : z₁ ≠ 0 := ne_zero_of_mem_imGT hz₁
  have hz₂1 : z₂ + 1 = z₁ / (z₁ + 1) := by simp only [z₂]; field_simp; ring
  have hz₃1 : z₃ + 1 = -1 / z₁ := by
    simp only [z₃]; rw [hz₂1]; field_simp; ring
  have hcyc : -1 / (z₃ + 1) = z₁ := by rw [hz₃1]; field_simp
  have key := hφ z₃ hz₃
  rw [hcyc, hφ z₂ hz₂, hφ z₁ hz₁] at key
  have hprod : (z₃ + 1) * (z₂ + 1) * (z₁ + 1) = -1 := by
    rw [hz₃1, hz₂1]; field_simp
  have h3 : wr (famF ν U) z₁ * (1 - ((z₃ + 1) * (z₂ + 1) * (z₁ + 1)) ^ w * c ^ 3) = 0 := by
    rw [mul_pow, mul_pow]; linear_combination key
  rw [hprod, pow_neg_one_mul_self_eq_one, one_mul] at h3
  have := (mul_eq_zero.mp h3).resolve_left hW
  linear_combination -this

/-- `t⁶ = 1`, i.e. `6 Σ νⱼ ∈ ℤ`. -/
theorem exists_int_six_sum {n : ℕ} (ν : Fin n → ℂ) (s : ℂ) (hs : s ^ 2 = 1)
    (hst : (s * ∏ j, tvec ν j) ^ 3 = 1) : ∃ K : ℤ, 6 * ∑ j, ν j = K := by
  have ht : (∏ j, tvec ν j) ^ 6 = 1 := by
    have h6 : (s * ∏ j, tvec ν j) ^ 6 = 1 := by
      rw [show 6 = 3 * 2 from rfl, pow_mul, hst, one_pow]
    rw [mul_pow, show s ^ 6 = (s ^ 2) ^ 3 from by ring, hs, one_pow, one_mul] at h6
    exact h6
  have hexp : (∏ j, tvec ν j) ^ 6
      = Complex.exp (6 * (∑ j, ν j) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    simp only [tvec]
    rw [← Complex.exp_sum, ← Complex.exp_nat_mul]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  rw [hexp, Complex.exp_eq_one_iff] at ht
  obtain ⟨K, hK⟩ := ht
  refine ⟨K, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := two_pi_I_ne_zero
  exact mul_right_cancel₀ h2 hK

/-! ## Analyticity and boundedness of determinants -/

theorem analyticAt_det {n : ℕ} {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (h : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) : AnalyticAt ℂ (fun w => (M w).det) z := by
  simp_rw [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem det_mem_subalgebra {X : Type*} {n : ℕ} (A : Subalgebra ℂ (X → ℂ))
    {M : X → Matrix (Fin n) (Fin n) ℂ} (h : ∀ i j, (fun x => M x i j) ∈ A) :
    (fun x => (M x).det) ∈ A := by
  have hfun : (fun x => (M x).det)
      = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ i, fun x => M x (σ i) i := by
    funext x
    simp [Matrix.det_apply, Units.smul_def, Finset.prod_apply, Finset.sum_apply, zsmul_eq_mul]
  rw [hfun]
  exact Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun i _ => h _ _) _

theorem isBoundedAtImInfty_amEval_zero {P : PowerSeries ℂ} (hP : P ∈ SubexpPS) :
    IsBoundedAtImInfty (fun τ : ℍ => amEval 0 P τ) := by
  rw [isBoundedAtImInfty_iff]
  have hr0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * Real.pi)) < 1 := by
    have := Real.pi_pos
    simpa using Real.exp_lt_exp.mpr (show -(2 * Real.pi) < 0 by linarith)
  have hsum := summable_of_subexponential (fun n => norm_nonneg (PowerSeries.coeff n P)) hP hr0 hr1
  refine ⟨∑' n : ℕ, ‖PowerSeries.coeff n P‖ * Real.exp (-(2 * Real.pi)) ^ n, 1, fun τ hτ => ?_⟩
  have hz : (τ : ℂ) ∈ imGT 0 := τ.im_pos
  rw [amEval_zero_left]
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_coeff_qexp hP hz)) ?_
  refine (summable_norm_coeff_qexp hP hz).tsum_le_tsum (fun n => ?_) hsum
  rw [norm_mul, qexp_eq_qC_pow, norm_pow, norm_qC]
  have h1 : (1 : ℝ) ≤ (τ : ℂ).im := hτ
  have := Real.pi_pos
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le
    (Real.exp_le_exp.mpr (by nlinarith)) n) (norm_nonneg _)

theorem isBoundedAtImInfty_exp_mul_disc (K : ℤ) (M : ℕ) (hKM : 0 ≤ K + M) :
    IsBoundedAtImInfty (fun τ : ℍ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ * K) * ModularForm.discriminant τ ^ M) := by
  have hO := CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  obtain ⟨C, hC, hCb⟩ := hO.exists_pos
  rw [Asymptotics.IsBigOWith_def] at hCb
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hCb
  rw [isBoundedAtImInfty_iff]
  refine ⟨C ^ M, max A 0, fun τ hτ => ?_⟩
  have hb := hA τ (le_trans (le_max_left _ _) hτ)
  simp only [Set.mem_setOf_eq, CuspForm.coe_discriminant, div_one, Real.norm_eq_abs,
    Real.abs_exp] at hb
  have him : 0 ≤ τ.im := le_trans (le_max_right _ _) hτ
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * τ * K).re = -(2 * Real.pi * K * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [hre]
  calc Real.exp (-(2 * Real.pi * K * τ.im)) * ‖ModularForm.discriminant τ‖ ^ M
      ≤ Real.exp (-(2 * Real.pi * K * τ.im)) * (C * Real.exp (-2 * Real.pi * τ.im)) ^ M := by
        gcongr
    _ = C ^ M * Real.exp (-(2 * Real.pi * τ.im * (K + M))) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
        congr 2; ring
    _ ≤ C ^ M * 1 := by
        gcongr
        rw [Real.exp_le_one_iff]
        have := Real.pi_pos
        have hKM' : (0 : ℝ) ≤ (K : ℝ) + (M : ℝ) := by exact_mod_cast hKM
        have : 0 ≤ 2 * Real.pi * τ.im * (K + M) := mul_nonneg (by positivity) hKM'
        linarith
    _ = C ^ M := mul_one _

/-! ## Level-one forms in the `ℂ` variable -/

theorem slashInv_S_apply {G : Type*} [FunLike G ℍ ℂ] {k : ℤ} [SlashInvariantFormClass G 𝒮ℒ k]
    (F : G) {z : ℂ} (hz : z ∈ imGT 0) :
    F (ofComplex (-1 / z)) = z ^ k * F (ofComplex z) := by
  have h := congrFun (SlashInvariantForm.slash_action_eqn F _ ⟨ModularGroup.S, rfl⟩)
    (⟨z, hz⟩ : ℍ)
  change (⇑F ∣[k] ModularGroup.S) ⟨z, hz⟩ = F ⟨z, hz⟩ at h
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S] at h
  have hz0 : z ≠ 0 := ne_zero_of_mem_imGT hz
  have hm : -1 / z ∈ imGT 0 := neg_one_div_mem_imGT hz
  rw [ofComplex_apply_of_im_pos hm, ofComplex_apply_of_im_pos hz]
  have he : (UpperHalfPlane.mk (-(⟨z, hz⟩ : ℍ) : ℂ)⁻¹
      (by simpa using (⟨z, hz⟩ : ℍ).im_inv_neg_coe_pos) : ℍ) = ⟨-1 / z, hm⟩ := by
    ext; simp [neg_div, inv_neg]
  rw [he] at h
  rw [← h]
  change F ⟨-1 / z, hm⟩ = z ^ k * (F ⟨-1 / z, hm⟩ * z ^ (-k))
  rw [zpow_neg]
  field_simp

theorem slashInv_T_apply {G : Type*} [FunLike G ℍ ℂ] {k : ℤ} [SlashInvariantFormClass G 𝒮ℒ k]
    (F : G) {z : ℂ} (hz : z ∈ imGT 0) :
    F (ofComplex (z + 1)) = F (ofComplex z) := by
  have h := congrFun (SlashInvariantForm.slash_action_eqn F _ ⟨ModularGroup.T, rfl⟩)
    (⟨z, hz⟩ : ℍ)
  change (⇑F ∣[k] ModularGroup.T) ⟨z, hz⟩ = F ⟨z, hz⟩ at h
  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul] at h
  have hd : UpperHalfPlane.denom (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (⟨z, hz⟩ : ℍ) = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.T]; simp
  rw [hd, one_zpow, mul_one] at h
  have hm : z + 1 ∈ imGT 0 := add_one_mem_imGT hz
  rw [ofComplex_apply_of_im_pos hm, ofComplex_apply_of_im_pos hz, ← h]
  congr 1
  ext; simp [add_comm]

theorem analyticAt_slashInv {G : Type*} [FunLike G ℍ ℂ] {k : ℤ} [ModularFormClass G 𝒮ℒ k]
    (F : G) {z : ℂ} (hz : z ∈ imGT 0) : AnalyticAt ℂ (fun w => F (ofComplex w)) z := by
  have h := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo F)
  exact (h.analyticAt ((isOpen_imGT 0).mem_nhds hz))

/-! ## The reduced matrices -/

/-- `jetMat F = M̃ · diag(e^{2πizν_j})` on `ℍ`. -/
def redMat {n : ℕ} (ν : Fin n → ℂ) (U : Fin n → PowerSeries ℂ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun m j => amEval 0 (amSerreF (ν j) m (U j)) z

def redVec {n : ℕ} (ν : Fin n → ℂ) (U : Fin n → PowerSeries ℂ) (z : ℂ) : Fin n → ℂ :=
  fun j => amEval 0 (amSerreF (ν j) n (U j)) z

def expVec {n : ℕ} (ν : Fin n → ℂ) (z : ℂ) : Fin n → ℂ :=
  fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * ν j)

theorem jetMat_eq_red {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) :
    jetMat (famF ν U) z = 1 * redMat ν U z * (Matrix.diagonal (expVec ν z))ᵀ := by
  ext m j
  rw [Matrix.diagonal_transpose, one_mul, Matrix.mul_diagonal]
  simp only [jetMat, redMat, Matrix.of_apply, famF, expVec]
  rw [amSerreIter_amEval _ m (hU j) hz, amEval_eq_exp_mul, mul_comm]

theorem topVec_eq_red {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) :
    topVec (famF ν U) z = (1 : ℂ) • (Matrix.diagonal (expVec ν z) *ᵥ redVec ν U z) := by
  funext j
  rw [one_smul, Matrix.mulVec_diagonal]
  simp only [topVec, redVec, famF, expVec]
  rw [amSerreIter_amEval _ n (hU j) hz, amEval_eq_exp_mul]

theorem wr_eq_red {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) :
    wr (famF ν U) z = (∏ j, expVec ν z j) * (redMat ν U z).det := by
  rw [wr, jetMat_eq_red ν hU hz, Matrix.det_mul, Matrix.det_mul, Matrix.det_one,
    Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem wrc_eq_red {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) (r : Fin n) :
    wrc (famF ν U) z r
      = (∏ j, expVec ν z j) * Matrix.cramer (redMat ν U z)ᵀ (redVec ν U z) r := by
  rw [wrc, jetMat_eq_red ν hU hz, topVec_eq_red ν hU hz, cramer_transpose_mul,
    Matrix.transpose_one, Matrix.adjugate_one, Matrix.one_mulVec, Matrix.det_diagonal, one_mul]
  rfl

theorem prod_expVec_pow_six {n : ℕ} (ν : Fin n → ℂ) {K : ℤ} (hK : 6 * ∑ j, ν j = K) (z : ℂ) :
    (∏ j, expVec ν z j) ^ 6 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * K) := by
  simp only [expVec]
  rw [← Complex.exp_sum, ← Complex.exp_nat_mul, ← hK]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem mem_bdd_redMat {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (m j : Fin n) :
    (fun τ : ℍ => redMat ν U τ m j) ∈ boundedAtImInftySubalgebra ℂ :=
  isBoundedAtImInfty_amEval_zero (amSerreF_mem _ m (hU j))

theorem mem_bdd_det_redMat {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) :
    (fun τ : ℍ => (redMat ν U τ).det) ∈ boundedAtImInftySubalgebra ℂ :=
  det_mem_subalgebra _ fun m j => mem_bdd_redMat ν hU m j

theorem mem_bdd_cramer_redMat {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (r : Fin n) :
    (fun τ : ℍ => Matrix.cramer (redMat ν U τ)ᵀ (redVec ν U τ) r)
      ∈ boundedAtImInftySubalgebra ℂ := by
  simp only [Matrix.cramer_apply]
  refine det_mem_subalgebra _ fun i j => ?_
  simp only [Matrix.updateCol_apply, Matrix.transpose_apply]
  by_cases hj : j = r
  · simp only [hj, if_true]
    exact isBoundedAtImInfty_amEval_zero (amSerreF_mem _ n (hU i))
  · simp only [hj, if_false]
    exact mem_bdd_redMat ν hU j i

/-! ## The MLDE -/

/-- `Δ` in the `ℂ` variable. -/
def DeltaC (z : ℂ) : ℂ := ModularForm.discriminant (ofComplex z)

theorem analyticAt_wr {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    {z : ℂ} (hz : z ∈ imGT 0) : AnalyticAt ℂ (wr f) z :=
  analyticAt_det (M := jetMat f) fun m j => analyticAt_amSerreIter m (hf j) hz

theorem analyticAt_wrc {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    {z : ℂ} (hz : z ∈ imGT 0) (r : Fin n) : AnalyticAt ℂ (fun w => wrc f w r) z := by
  simp only [wrc, Matrix.cramer_apply]
  refine analyticAt_det fun i j => ?_
  simp only [Matrix.updateCol_apply, Matrix.transpose_apply]
  by_cases hj : j = r
  · simp only [hj, if_true]
    exact analyticAt_amSerreIter n (hf i) hz
  · simp only [hj, if_false]
    exact analyticAt_amSerreIter j (hf i) hz

theorem DeltaC_S {z : ℂ} (hz : z ∈ imGT 0) : DeltaC (-1 / z) = z ^ 12 * DeltaC z := by
  have := slashInv_S_apply CuspForm.discriminant hz
  simpa [DeltaC] using this

theorem DeltaC_T {z : ℂ} (hz : z ∈ imGT 0) : DeltaC (z + 1) = DeltaC z := by
  have := slashInv_T_apply CuspForm.discriminant hz
  simpa [DeltaC] using this

/-- **The modular linear differential equation of an `S`-closed `q^ν`-family.** -/
theorem exists_mlde {n : ℕ} {ν : Fin n → ℂ} {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (hν : Function.Injective ν)
    (hU0 : ∀ j, PowerSeries.coeff 0 (U j) ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ i, ∀ z ∈ imGT 0, famF ν U i (-1 / z) = ∑ j, S i j * famF ν U j z) :
    ∃ (k : ℕ) (B : ModularForm 𝒮ℒ (k : ℤ))
      (A : (r : Fin n) → ModularForm 𝒮ℒ ((k + 2 * (n - (r : ℕ)) : ℕ) : ℤ)),
      (∃ z ∈ imGT 0, B (ofComplex z) ≠ 0) ∧
      ∀ j, ∀ z ∈ imGT 0, B (ofComplex z) * amSerreIter n (famF ν U j) z
        = ∑ r : Fin n, A r (ofComplex z) * amSerreIter r (famF ν U j) z := by
  classical
  have hf := analyticAt_famF ν hU
  obtain ⟨z₁, hz₁, hW⟩ := exists_wr_ne_zero hU hν hU0
  have hs := sq_det_eq_one hf S hS hz₁ hW
  have hst := det_mul_prod_cube_eq_one ν hU S hS hz₁ hW
  obtain ⟨K, hK⟩ := exists_int_six_sum ν S.det hs hst
  set M : ℕ := K.natAbs with hMdef
  have hKM : 0 ≤ K + (M : ℤ) := by rcases Int.natAbs_eq K with h | h <;> omega
  have hs6 : S.det ^ 6 = 1 := by rw [show S.det ^ 6 = (S.det ^ 2) ^ 3 by ring, hs, one_pow]
  set t := ∏ j, tvec ν j with ht
  have ht6 : t ^ 6 = 1 := by
    have h6 : (S.det * t) ^ 6 = 1 := by
      rw [show (S.det * t) ^ 6 = ((S.det * t) ^ 3) ^ 2 by ring, hst, one_pow]
    rwa [mul_pow, hs6, one_mul] at h6
  set w := n * (n - 1) with hw
  set k : ℕ := 6 * w + 12 * M with hk
  -- the functions
  let Bf : ℂ → ℂ := fun z => wr (famF ν U) z ^ 6 * DeltaC z ^ M
  let Af : Fin n → ℂ → ℂ := fun r z => wrc (famF ν U) z r * wr (famF ν U) z ^ 5 * DeltaC z ^ M
  have hΔan : ∀ z ∈ imGT 0, AnalyticAt ℂ DeltaC z := fun z hz => by
    have := analyticAt_slashInv CuspForm.discriminant hz
    simpa [DeltaC] using this
  have hBan : DifferentiableOn ℂ Bf (imGT 0) := fun z hz =>
    (((analyticAt_wr hf hz).pow 6).mul ((hΔan z hz).pow M)).differentiableAt.differentiableWithinAt
  have hAan : ∀ r, DifferentiableOn ℂ (Af r) (imGT 0) := fun r z hz =>
    ((((analyticAt_wrc hf hz r).mul ((analyticAt_wr hf hz).pow 5)).mul
      ((hΔan z hz).pow M))).differentiableAt.differentiableWithinAt
  have hBS : ∀ z ∈ imGT 0, Bf (-1 / z) = z ^ k * Bf z := by
    intro z hz
    simp only [Bf]
    rw [wr_S hf S hS hz, DeltaC_S hz, hk]
    linear_combination (z ^ (6 * w) * wr (famF ν U) z ^ 6 * (z ^ 12 * DeltaC z) ^ M) * hs6
  have hAS : ∀ r : Fin n, ∀ z ∈ imGT 0,
      Af r (-1 / z) = z ^ (k + 2 * (n - (r : ℕ))) * Af r z := by
    intro r z hz
    have hP : z ^ (2 * (r : ℕ)) * ∏ l ∈ Finset.univ.erase r, z ^ (2 * (l : ℕ)) = z ^ w := by
      rw [Finset.mul_prod_erase Finset.univ (fun l : Fin n => z ^ (2 * (l : ℕ)))
        (Finset.mem_univ r), prod_pow_two_mul]
    have hnr : z ^ (2 * n) = z ^ (2 * (n - (r : ℕ))) * z ^ (2 * (r : ℕ)) := by
      rw [← pow_add]; congr 1; have := r.isLt; omega
    simp only [Af]
    rw [wrc_S hf S hS hz r, wr_S hf S hS hz, DeltaC_S hz, hk, hnr]
    set P := ∏ l ∈ Finset.univ.erase r, z ^ (2 * (l : ℕ))
    set Y := z ^ (2 * (n - (r : ℕ))) * z ^ (5 * w) * wrc (famF ν U) z r *
      wr (famF ν U) z ^ 5 * z ^ (12 * M) * DeltaC z ^ M
    linear_combination (Y * (z ^ (2 * (r : ℕ)) * P)) * hs6 + Y * hP
  have hBT : ∀ z ∈ imGT 0, Bf (z + 1) = Bf z := by
    intro z hz
    simp only [Bf]
    rw [wr_T ν hU hz, DeltaC_T hz]
    linear_combination (wr (famF ν U) z ^ 6 * DeltaC z ^ M) * ht6
  have hAT : ∀ r : Fin n, ∀ z ∈ imGT 0, Af r (z + 1) = Af r z := by
    intro r z hz
    simp only [Af]
    rw [wrc_T ν hU hz r, wr_T ν hU hz, DeltaC_T hz]
    linear_combination (wrc (famF ν U) z r * wr (famF ν U) z ^ 5 * DeltaC z ^ M) * ht6
  have hcoe : ∀ τ : ℍ, DeltaC (τ : ℂ) = ModularForm.discriminant τ := fun τ => by
    simp [DeltaC]
  have hE : (fun τ : ℍ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ * K) *
      ModularForm.discriminant τ ^ M) ∈ boundedAtImInftySubalgebra ℂ :=
    isBoundedAtImInfty_exp_mul_disc K M hKM
  have hBb : IsBoundedAtImInfty (fun τ : ℍ => Bf τ) := by
    have hfeq : (fun τ : ℍ => Bf τ) = (fun τ : ℍ => (redMat ν U τ).det) ^ 6 *
        (fun τ : ℍ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ * K) *
          ModularForm.discriminant τ ^ M) := by
      funext τ
      simp only [Bf, Pi.mul_apply, Pi.pow_apply]
      rw [wr_eq_red ν hU τ.im_pos, mul_pow, prod_expVec_pow_six ν hK, hcoe]
      ring
    have := Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (mem_bdd_det_redMat ν hU) 6) hE
    rw [← hfeq] at this
    exact this
  have hAb : ∀ r, IsBoundedAtImInfty (fun τ : ℍ => Af r τ) := by
    intro r
    have hfeq : (fun τ : ℍ => Af r τ) =
        (fun τ : ℍ => Matrix.cramer (redMat ν U τ)ᵀ (redVec ν U τ) r) *
        (fun τ : ℍ => (redMat ν U τ).det) ^ 5 *
        (fun τ : ℍ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ * K) *
          ModularForm.discriminant τ ^ M) := by
      funext τ
      simp only [Af, Pi.mul_apply, Pi.pow_apply]
      rw [wrc_eq_red ν hU τ.im_pos, wr_eq_red ν hU τ.im_pos, ← prod_expVec_pow_six ν hK, hcoe]
      ring
    have := Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (mem_bdd_cramer_redMat ν hU r)
      (Subalgebra.pow_mem _ (mem_bdd_det_redMat ν hU) 5)) hE
    rw [← hfeq] at this
    exact this
  have hcoeC : ∀ z ∈ imGT 0, ((ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [ofComplex_apply_of_im_pos hz]
  refine ⟨k, mkLevelOne Bf k hBan hBS hBT hBb,
    fun r => mkLevelOne (Af r) (k + 2 * (n - (r : ℕ))) (hAan r) (hAS r) (hAT r) (hAb r),
    ⟨z₁, hz₁, ?_⟩, ?_⟩
  · rw [mkLevelOne_apply, hcoeC z₁ hz₁]
    refine mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ ?_)
    exact ModularForm.discriminant_ne_zero _
  · intro j z hz
    simp only [mkLevelOne_apply, hcoeC z hz, Bf, Af]
    have hc := wr_cramer (famF ν U) z j
    have : ∑ r : Fin n, wrc (famF ν U) z r * wr (famF ν U) z ^ 5 * DeltaC z ^ M *
        amSerreIter r (famF ν U j) z
        = (∑ r : Fin n, wrc (famF ν U) z r * amSerreIter r (famF ν U j) z) *
          (wr (famF ν U) z ^ 5 * DeltaC z ^ M) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [this, hc]
    ring

end VOA.Huang.AndersonMoore
