/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkCusp
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# `θ` has no zeros on the upper half plane

With `ϑ₂(τ) = Σ_{n odd} e^{πi n² τ/4}`, `ϑ₃ = jacobiTheta`, `ϑ₄(τ) = ϑ₃(τ + 1)`:

* `jacobiTheta₂_add_one_right`: `ϑ(z, τ + 1) = ϑ(z + ½, τ)`;
* the `S`- and `T`-laws of `ϑ₂, ϑ₃, ϑ₄` (from Mathlib's `jacobiTheta₂_functional_equation`);
* `thetaProd8 = (ϑ₂ϑ₃ϑ₄)⁸` is a level-one cusp form of weight `12`, hence `c Δ`
  (`CuspForm.exists_smul_discriminant_of_weight_eq_twelve`), with `c ≠ 0` (evaluation at `i`,
  where `ϑ₂(i) > 0`). Since `Δ` has no zeros,
* `jacobiTheta_ne_zero`, `thetaRef_ne_zero_of_im_pos`: `ϑ₃` and `θ(τ) = ϑ₃(2τ)` vanish nowhere
  on `ℍ` (the classical identity is `ϑ₂ϑ₃ϑ₄ = 2η³`; only its eighth power up to a constant is
  needed).
-/

open Complex Filter Topology
open scoped MatrixGroups ModularForm Manifold UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace ThetaZeroFree

/-! ## The three theta constants -/

/-- `ϑ₂(τ) = Σ_{n odd} e^{πi n² τ / 4}`. -/
def th2 (τ : ℂ) : ℂ := rankOneTheta 1 2 (1 / 8) τ

/-- `ϑ₃ = jacobiTheta`. -/
def th3 (τ : ℂ) : ℂ := jacobiTheta τ

/-- `ϑ₄(τ) = ϑ₃(τ + 1) = Σ (-1)ⁿ e^{πi n² τ}`. -/
def th4 (τ : ℂ) : ℂ := jacobiTheta (τ + 1)

theorem th2_eq (τ : ℂ) :
    th2 τ = cexp (Real.pi * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  rw [th2, rankOneTheta_eq_jacobiTheta₂]
  congr 1
  · congr 1; push_cast; ring
  · congr 1 <;> push_cast <;> ring

/-- `ϑ(z, τ + 1) = ϑ(z + ½, τ)`. -/
theorem jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  unfold jacobiTheta₂
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂_term
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self n
  have e : 2 * Real.pi * I * n * z + Real.pi * I * (n : ℂ) ^ 2 * (τ + 1) =
      (2 * Real.pi * I * n * (z + 1 / 2) + Real.pi * I * (n : ℂ) ^ 2 * τ) +
        (k : ℤ) * (2 * Real.pi * I) := by
    have hk' : ((n : ℂ) * (n - 1)) = (k : ℂ) + k := by exact_mod_cast hk
    linear_combination (Real.pi * I) * hk'
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem th4_eq (τ : ℂ) : th4 τ = jacobiTheta₂ (1 / 2) τ := by
  rw [th4, jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_add_one_right, zero_add]

/-! ## `T`-laws -/

theorem th3_add_one (τ : ℂ) : th3 (τ + 1) = th4 τ := rfl

theorem th4_add_one (τ : ℂ) : th4 (τ + 1) = th3 τ := by
  rw [th4, th3, add_assoc, one_add_one_eq_two, add_comm, jacobiTheta_two_add]

theorem th2_add_one (τ : ℂ) : th2 (τ + 1) = cexp (Real.pi * I / 4) * th2 τ := by
  rw [th2_eq, th2_eq, jacobiTheta₂_add_one_right,
    show (τ + 1) / 2 + 1 / 2 = τ / 2 + 1 by ring, jacobiTheta₂_add_left, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-! ## `S`-laws -/

theorem neg_I_mul_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : -I * τ ≠ 0 :=
  mul_ne_zero (neg_ne_zero.2 I_ne_zero) fun h => by simp [h] at hτ

theorem sqrt_ne_zero' {τ : ℂ} (hτ : 0 < τ.im) : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (neg_I_mul_ne_zero hτ)

theorem th3_S {τ : ℂ} (hτ : 0 < τ.im) : th3 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * th3 τ := by
  have h := jacobiTheta_S_smul ⟨τ, hτ⟩
  rw [UpperHalfPlane.modular_S_smul] at h
  simpa [th3, neg_div, inv_neg] using h

theorem th4_S {τ : ℂ} (hτ : 0 < τ.im) : th4 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * th2 τ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have h := jacobiTheta₂_functional_equation (τ / 2) τ
  rw [show τ / 2 / τ = 1 / 2 by field_simp,
    show -(Real.pi : ℂ) * I * (τ / 2) ^ 2 / τ = -(Real.pi * I * τ / 4) by field_simp; ring] at h
  rw [th4_eq, th2_eq, h, Complex.exp_neg]
  have hs := sqrt_ne_zero' hτ
  have he := Complex.exp_ne_zero (Real.pi * I * τ / 4)
  field_simp

theorem th2_S {τ : ℂ} (hτ : 0 < τ.im) : th2 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * th4 τ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have h := jacobiTheta₂_functional_equation (1 / 2) τ
  rw [show (1 / 2 : ℂ) / τ = -(-1 / τ / 2) by ring, jacobiTheta₂_neg_left,
    show -(Real.pi : ℂ) * I * (1 / 2) ^ 2 / τ = Real.pi * I * (-1 / τ) / 4 by ring] at h
  rw [th4_eq, h, th2_eq]
  have hs := sqrt_ne_zero' hτ
  have he := Complex.exp_ne_zero (Real.pi * I * (-1 / τ) / 4)
  field_simp

/-! ## The weight-12 product -/

/-- `(ϑ₂ϑ₃ϑ₄)⁸`. -/
def thetaProd8 (τ : ℂ) : ℂ := (th2 τ * th3 τ * th4 τ) ^ 8

theorem sqrt_pow_24 (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 24 = x ^ 12 := by
  rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, one_div, cpow_ofNat_inv_pow]

theorem thetaProd8_S {τ : ℂ} (hτ : 0 < τ.im) : thetaProd8 (-1 / τ) = τ ^ 12 * thetaProd8 τ := by
  rw [thetaProd8, thetaProd8, th2_S hτ, th3_S hτ, th4_S hτ]
  have h : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 24 = τ ^ 12 := by
    rw [sqrt_pow_24, mul_pow]
    have : (-I) ^ 12 = (1 : ℂ) := by
      rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul, neg_sq, I_sq]; norm_num
    rw [this, one_mul]
  rw [← h]
  ring

theorem thetaProd8_T (τ : ℂ) : thetaProd8 (τ + 1) = thetaProd8 τ := by
  rw [thetaProd8, thetaProd8, th2_add_one, th3_add_one, th4_add_one]
  have h : cexp (Real.pi * I / 4) ^ 8 = 1 := by
    rw [← Complex.exp_nat_mul, show ((8 : ℕ) : ℂ) * (Real.pi * I / 4) = 2 * Real.pi * I by
      push_cast; ring, Complex.exp_two_pi_mul_I]
  calc (cexp (Real.pi * I / 4) * th2 τ * th4 τ * th3 τ) ^ 8
      = cexp (Real.pi * I / 4) ^ 8 * (th2 τ * th3 τ * th4 τ) ^ 8 := by ring
    _ = _ := by rw [h, one_mul]

/-! ## Holomorphy and decay -/

theorem differentiableOn_rankOneTheta_real (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (rankOneTheta n₀ r t) upperSet := by
  intro τ hτ
  have hfun : rankOneTheta n₀ r t = fun z =>
      cexp (2 * Real.pi * I * t * (n₀ : ℂ) ^ 2 * z) *
        jacobiTheta₂ (2 * t * r * n₀ * z) (2 * t * (r : ℂ) ^ 2 * z) :=
    funext (rankOneTheta_eq_jacobiTheta₂ n₀ r t)
  rw [hfun]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine ((differentiableAt_id.const_mul _).cexp).mul ?_
  have him : 0 < (2 * t * (r : ℂ) ^ 2 * τ).im := im_two_mul_sq_mul_pos hr ht hτ
  have hJ := (hasFDerivAt_jacobiTheta₂ (2 * t * r * n₀ * τ) him).differentiableAt
  have hg : DifferentiableAt ℂ (fun z : ℂ => (2 * t * r * n₀ * z, 2 * t * (r : ℂ) ^ 2 * z)) τ :=
    DifferentiableAt.prodMk (differentiableAt_id.const_mul _) (differentiableAt_id.const_mul _)
  exact DifferentiableAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) τ hJ hg

theorem differentiableOn_jacobiTheta : DifferentiableOn ℂ jacobiTheta upperSet :=
  fun _ hτ => (differentiableAt_jacobiTheta hτ).differentiableWithinAt

theorem differentiableOn_thetaProd8 : DifferentiableOn ℂ thetaProd8 upperSet := by
  have h2 : DifferentiableOn ℂ th2 upperSet :=
    differentiableOn_rankOneTheta_real 1 (by norm_num) (by norm_num)
  have h4 : DifferentiableOn ℂ th4 upperSet := by
    have hmaps : Set.MapsTo (fun z : ℂ => z + 1) upperSet upperSet := fun z hz => by
      simpa using hz
    exact differentiableOn_jacobiTheta.comp ((differentiableOn_id).add_const 1) hmaps
  exact ((h2.mul differentiableOn_jacobiTheta).mul h4).pow 8

theorem th3_eq_thetaRef (τ : ℂ) : th3 τ = thetaRef (τ / 2) := by
  rw [th3, thetaRef_eq_jacobiTheta]; congr 1; ring

theorem norm_th3_le {τ : ℂ} (hτ : 1 ≤ τ.im) : ‖th3 τ‖ ≤ 2 := by
  rw [th3_eq_thetaRef]
  have h := norm_thetaRef_sub_one_lt (τ := τ / 2) (by simp; linarith)
  have h' := norm_sub_norm_le (thetaRef (τ / 2)) 1
  rw [norm_one] at h'
  linarith

theorem norm_th4_le {τ : ℂ} (hτ : 1 ≤ τ.im) : ‖th4 τ‖ ≤ 2 := by
  have := norm_th3_le (τ := τ + 1) (by simpa using hτ)
  simpa [th3, th4] using this

theorem one_le_sq_odd (m : ℤ) : (1 : ℝ) ≤ (((1 + 2 * m : ℤ) : ℝ)) ^ 2 := by
  have h : (1 + 2 * m : ℤ) ≠ 0 := by omega
  have h1 : (1 : ℝ) ≤ |(((1 + 2 * m : ℤ) : ℝ))| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
  nlinarith [abs_nonneg (((1 + 2 * m : ℤ) : ℝ)), sq_abs (((1 + 2 * m : ℤ) : ℝ))]

/-- `‖ϑ₂(τ)‖ ≤ A e^{-π Im τ / 4}` on `Im τ ≥ 1`. -/
theorem norm_th2_le : ∃ A : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
    ‖th2 τ‖ ≤ A * Real.exp (-(Real.pi / 4 * τ.im)) := by
  have hs : Summable fun m => ‖rankOneThetaTerm 1 2 (1 / 8) I m‖ :=
    (summable_rankOneThetaTerm 1 (r := 2) (by norm_num) (t := 1 / 8) (by norm_num)
      (τ := I) (by simp)).norm
  refine ⟨Real.exp (Real.pi / 4) * ∑' m, ‖rankOneThetaTerm 1 2 (1 / 8) I m‖, fun τ hτ => ?_⟩
  have hle : ∀ m, ‖rankOneThetaTerm 1 2 (1 / 8) τ m‖ ≤
      Real.exp (-(Real.pi / 4 * (τ.im - 1))) * ‖rankOneThetaTerm 1 2 (1 / 8) I m‖ := by
    intro m
    rw [norm_rankOneThetaTerm, norm_rankOneThetaTerm, I_im, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hk := one_le_sq_odd m
    have hpi := Real.pi_pos
    have e : (((1 + 2 * m : ℤ) : ℝ)) = (((1 + 2 * m : ℤ) : ℝ)) := rfl
    nlinarith [mul_nonneg (mul_nonneg hpi.le (sub_nonneg.2 hk)) (sub_nonneg.2 hτ)]
  have hs' : Summable fun m => ‖rankOneThetaTerm 1 2 (1 / 8) τ m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hs.mul_left _)
  calc ‖th2 τ‖ ≤ ∑' m, ‖rankOneThetaTerm 1 2 (1 / 8) τ m‖ := norm_tsum_le_tsum_norm hs'
    _ ≤ ∑' m, Real.exp (-(Real.pi / 4 * (τ.im - 1))) * ‖rankOneThetaTerm 1 2 (1 / 8) I m‖ :=
        hs'.tsum_le_tsum hle (hs.mul_left _)
    _ = _ := by
        rw [tsum_mul_left, show -(Real.pi / 4 * (τ.im - 1)) = Real.pi / 4 +
          -(Real.pi / 4 * τ.im) by ring, Real.exp_add]
        ring

theorem norm_thetaProd8_le : ∃ K : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
    ‖thetaProd8 τ‖ ≤ K * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨A, hA⟩ := norm_th2_le
  refine ⟨(4 * A) ^ 8, fun τ hτ => ?_⟩
  have h2 := hA τ hτ
  have hA0 : 0 ≤ A * Real.exp (-(Real.pi / 4 * τ.im)) := (norm_nonneg _).trans h2
  rw [thetaProd8, norm_pow, norm_mul, norm_mul]
  calc (‖th2 τ‖ * ‖th3 τ‖ * ‖th4 τ‖) ^ 8
      ≤ (A * Real.exp (-(Real.pi / 4 * τ.im)) * 2 * 2) ^ 8 := by
        gcongr
        · exact norm_th3_le hτ
        · exact norm_th4_le hτ
    _ = (4 * A) ^ 8 * Real.exp (-(Real.pi / 4 * τ.im)) ^ 8 := by ring
    _ = _ := by
        rw [← Real.exp_nat_mul]; congr 2; push_cast; ring

/-! ## The cusp form and the comparison with `Δ` -/

theorem coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
  rw [← mobius_eq_smul, mobius_S]

theorem coe_T_smul (z : ℍ) : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
  rw [← mobius_eq_smul, mobius_T]; simp

theorem slash_S : (fun τ : ℍ => thetaProd8 τ) ∣[(12 : ℤ)] ModularGroup.S =
    fun τ : ℍ => thetaProd8 τ := by
  ext z
  rw [ModularForm.SL_slash_apply, coe_S_smul, thetaProd8_S z.2]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hd : UpperHalfPlane.denom ModularGroup.S z = z := by
    simp [UpperHalfPlane.denom, ModularGroup.S]
  rw [hd, zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast]
  field_simp

theorem slash_T : (fun τ : ℍ => thetaProd8 τ) ∣[(12 : ℤ)] ModularGroup.T =
    fun τ : ℍ => thetaProd8 τ := by
  ext z
  rw [ModularForm.SL_slash_apply, coe_T_smul, thetaProd8_T]
  have : UpperHalfPlane.denom ModularGroup.T z = 1 := by
    simp [UpperHalfPlane.denom, ModularGroup.T]
  rw [this, one_zpow, mul_one]

theorem isZeroAtImInfty_thetaProd8 :
    UpperHalfPlane.IsZeroAtImInfty (fun τ : ℍ => thetaProd8 τ) := by
  obtain ⟨K, hK⟩ := norm_thetaProd8_le
  have hev : ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty, 1 ≤ τ.im :=
    Filter.tendsto_comap.eventually (eventually_ge_atTop 1)
  have hlim : Tendsto (fun τ : ℍ => K * Real.exp (-(2 * Real.pi * τ.im)))
      UpperHalfPlane.atImInfty (𝓝 0) := by
    have h1 : Tendsto (fun τ : ℍ => 2 * Real.pi * τ.im) UpperHalfPlane.atImInfty atTop :=
      Filter.tendsto_comap.const_mul_atTop (by positivity)
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
  exact squeeze_zero_norm' (hev.mono fun τ hτ => hK τ hτ) hlim

/-- `(ϑ₂ϑ₃ϑ₄)⁸` as a level-one cusp form of weight `12`. -/
def thetaCusp : CuspForm 𝒮ℒ 12 where
  toFun τ := thetaProd8 τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z slash_S slash_T A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine differentiableOn_thetaProd8.congr fun z hz => ?_
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z slash_S slash_T]
    exact isZeroAtImInfty_thetaProd8

/-! ## Non-vanishing at `i` -/

theorem rankOneThetaTerm_I (m : ℤ) : rankOneThetaTerm 1 2 (1 / 8) I m =
    ((Real.exp (-(2 * Real.pi * (1 / 8) * (((1 + 2 * m : ℤ) : ℝ)) ^ 2)) : ℝ) : ℂ) := by
  rw [rankOneThetaTerm, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem th2_I_ne_zero : th2 I ≠ 0 := by
  have hs : Summable fun m : ℤ =>
      Real.exp (-(2 * Real.pi * (1 / 8) * (((1 + 2 * m : ℤ) : ℝ)) ^ 2)) := by
    have := (summable_rankOneThetaTerm 1 (r := 2) (by norm_num) (t := 1 / 8) (by norm_num)
      (τ := I) (by simp)).norm
    refine this.congr fun m => ?_
    rw [rankOneThetaTerm_I, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hpos : 0 < ∑' m : ℤ, Real.exp (-(2 * Real.pi * (1 / 8) * (((1 + 2 * m : ℤ) : ℝ)) ^ 2)) :=
    hs.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  have h : th2 I = ((∑' m : ℤ,
      Real.exp (-(2 * Real.pi * (1 / 8) * (((1 + 2 * m : ℤ) : ℝ)) ^ 2)) : ℝ) : ℂ) := by
    rw [th2, rankOneTheta, Complex.ofReal_tsum]
    exact tsum_congr rankOneThetaTerm_I
  rw [h]
  exact_mod_cast hpos.ne'

theorem thetaProd8_I_ne_zero : thetaProd8 I ≠ 0 := by
  have h3 : th3 I ≠ 0 := by
    rw [th3_eq_thetaRef]; exact thetaRef_ne_zero (by simp)
  have h4 : th4 I ≠ 0 := by
    have : th4 I = th3 (I + 1) := rfl
    rw [this, th3_eq_thetaRef]; exact thetaRef_ne_zero (by simp)
  exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero th2_I_ne_zero h3) h4)

/-- **`(ϑ₂ϑ₃ϑ₄)⁸` vanishes nowhere on `ℍ`.** -/
theorem thetaProd8_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : thetaProd8 τ ≠ 0 := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve thetaCusp
  have hval : ∀ z : ℍ, thetaProd8 z = c * ModularForm.discriminant z := fun z => by
    have := congrArg (fun g : CuspForm 𝒮ℒ 12 => g z) hc
    simpa using this.symm
  have hc0 : c ≠ 0 := by
    intro h0
    have := hval UpperHalfPlane.I
    rw [h0, zero_mul] at this
    exact thetaProd8_I_ne_zero (by simpa using this)
  have := hval ⟨τ, hτ⟩
  change thetaProd8 τ = _ at this
  rw [this]
  exact mul_ne_zero hc0 (ModularForm.discriminant_ne_zero _)

end ThetaZeroFree

open ThetaZeroFree in
/-- **`ϑ₃ = jacobiTheta` has no zeros on the upper half plane.** -/
theorem jacobiTheta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  intro h
  apply thetaProd8_ne_zero hτ
  rw [thetaProd8]
  change (th2 τ * jacobiTheta τ * th4 τ) ^ 8 = 0
  rw [h]; simp

/-- **`θ(τ) = Σ qⁿ²` has no zeros on the upper half plane.** -/
theorem thetaRef_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : thetaRef τ ≠ 0 := by
  rw [thetaRef_eq_jacobiTheta]
  exact jacobiTheta_ne_zero (by simpa using hτ)

namespace ThetaZeroFree
end ThetaZeroFree

end VOA.Classification.COne
