/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.ThetaZeroFree

/-!
# Serre–Stark, stage S2-4: the `θ`-slash action of `Γ₀(N)` (diamond operators)

With `θ` zero-free (`thetaRef_ne_zero_of_im_pos`) the `θ`-normalised slash
`(f ‖ γ)(τ) = f(γτ) θ(τ) / θ(γτ)` is a genuine right action, and a θ-type form of level `N` is
exactly an `f` with `f ‖ γ = f` for `γ ∈ Γ₁(N)`. Proved here:

* `norm_thetaRef_mobius`: `‖θ(γτ)‖ = ‖cτ + d‖^{1/2} ‖θ(τ)‖` for `γ ∈ Γ₀(4)` (squared law with
  the character `χ₋₄(d)`, via `-γ`);
* `conj_mem_Gamma1`: `Γ₁(N)` is normal in `Γ₀(N)`;
* `IsThetaTypeForm.thetaSlash`: for `4 ∣ N` and `γ ∈ Γ₀(N)`, `f ‖ γ` is again θ-type of level `N`;
* `thetaSlash_mul`, `IsThetaTypeForm.thetaSlash_of_mem_Gamma1`: action laws.
-/

open Complex Filter Topology
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

/-! ## `θ` on `Γ₀(4)`, in norm -/

theorem mobius_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) :
    mobius (-γ) τ = mobius γ τ := by
  simp only [mobius, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
  rw [show (-(γ 0 0 : ℂ) * τ + -(γ 0 1 : ℂ)) = -((γ 0 0 : ℂ) * τ + γ 0 1) by ring,
    show (-(γ 1 0 : ℂ) * τ + -(γ 1 1 : ℂ)) = -((γ 1 0 : ℂ) * τ + γ 1 1) by ring, neg_div_neg_eq]

/-- `θ(γτ)² = ±(cτ + d) θ(τ)²` for `4 ∣ c`. -/
theorem thetaRef_mobius_sq_pm {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hc : 4 ∣ γ 1 0)
    {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef (mobius γ τ) ^ 2 = ((γ 1 0 : ℂ) * τ + γ 1 1) * thetaRef τ ^ 2 ∨
      thetaRef (mobius γ τ) ^ 2 = -(((γ 1 0 : ℂ) * τ + γ 1 1) * thetaRef τ ^ 2) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨k, hk⟩ := hc
  have hodd : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3 := by
    have hP : γ 0 0 * γ 1 1 = 1 + 4 * (γ 0 1 * k) := by rw [hk] at hdet; linarith
    rcases Int.emod_two_eq_zero_or_one (γ 1 1) with h | h
    · exfalso
      obtain ⟨e, he⟩ : (2 : ℤ) ∣ γ 1 1 := Int.dvd_of_emod_eq_zero h
      rw [he] at hP
      have h21 : (2 : ℤ) ∣ 1 := ⟨γ 0 0 * e - 2 * (γ 0 1 * k), by linarith⟩
      norm_num at h21
    · omega
  rcases hodd with h1 | h3
  · left
    exact thetaSqLaw_of_four_dvd _ γ rfl ⟨k, hk⟩ h1 τ hτ
  · right
    have hneg := thetaSqLaw_of_four_dvd _ (-γ) rfl
      (by simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]; exact ⟨-k, by omega⟩)
      (by simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]; omega) τ hτ
    rw [mobius_neg] at hneg
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at hneg
    rw [hneg]
    ring

/-- `‖θ(γτ)‖ = ‖cτ + d‖^{1/2} ‖θ(τ)‖` for `4 ∣ c`. -/
theorem norm_thetaRef_mobius {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hc : 4 ∣ γ 1 0)
    {τ : ℂ} (hτ : 0 < τ.im) :
    ‖thetaRef (mobius γ τ)‖ = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) * ‖thetaRef τ‖ := by
  have hsq : ‖thetaRef (mobius γ τ)‖ ^ 2 = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ * ‖thetaRef τ‖ ^ 2 := by
    rcases thetaRef_mobius_sq_pm hc hτ with h | h
    · rw [← norm_pow, h, norm_mul, norm_pow]
    · rw [← norm_pow, h, norm_neg, norm_mul, norm_pow]
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) (two_ne_zero)).1 ?_
  rw [hsq, mul_pow, ← Real.rpow_natCast (‖_‖ ^ (1 / 2 : ℝ)), ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-! ## `Γ₁(N)` is normal in `Γ₀(N)` -/

theorem conj_mem_Gamma1 {N : ℕ} {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hδ : δ ∈ CongruenceSubgroup.Gamma1 N) :
    γ * δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hδ0 : δ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hδ
  set g : CongruenceSubgroup.Gamma0 N := ⟨γ, hγ⟩
  set d : CongruenceSubgroup.Gamma0 N := ⟨δ, hδ0⟩
  have hd : CongruenceSubgroup.Gamma0Map N d = 1 :=
    ((CongruenceSubgroup.Gamma1_mem N δ).1 hδ).2.1
  have hgi : CongruenceSubgroup.Gamma0Map N g * CongruenceSubgroup.Gamma0Map N g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hk : g * d * g⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem', map_mul, map_mul, hd, mul_one, hgi]
  rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem] at hk
  rw [CongruenceSubgroup.Gamma1_mem]
  exact hk

/-! ## The `θ`-slash -/

/-- `(f ‖ γ)(τ) = f(γτ) θ(τ) / θ(γτ)`. -/
def thetaSlash (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  f (mobius γ τ) * thetaRef τ / thetaRef (mobius γ τ)

theorem thetaSlash_mul (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (f : ℂ → ℂ) {τ : ℂ}
    (hτ : 0 < τ.im) : thetaSlash δ (thetaSlash γ f) τ = thetaSlash (γ * δ) f τ := by
  have h1 := thetaRef_ne_zero_of_im_pos (im_mobius_pos δ hτ)
  have h2 := thetaRef_ne_zero_of_im_pos (im_mobius_pos (γ * δ) hτ)
  simp only [thetaSlash]
  rw [mobius_mul γ δ hτ] at h2 ⊢
  field_simp

theorem differentiableOn_comp_mobius {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperSet)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    DifferentiableOn ℂ (fun τ => f (mobius γ τ)) upperSet :=
  hf.comp (differentiableOn_mobius γ) fun _ hz => im_mobius_pos γ hz

namespace IsThetaTypeForm

variable {N : ℕ} {f : ℂ → ℂ}

/-- On a θ-type form, `Γ₁(N)` acts trivially. -/
theorem thetaSlash_of_mem_Gamma1 (hf : IsThetaTypeForm N f)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hδ : δ ∈ CongruenceSubgroup.Gamma1 N) {τ : ℂ}
    (hτ : 0 < τ.im) :
    thetaSlash δ f τ = f τ := by
  have h := thetaRef_ne_zero_of_im_pos (im_mobius_pos δ hτ)
  rw [thetaSlash, hf.multiplier δ hδ τ hτ]
  field_simp

/-- **The diamond action.** For `4 ∣ N` and `γ ∈ Γ₀(N)`, `f ‖ γ` is θ-type of level `N`. -/
theorem thetaSlash (h4 : 4 ∣ N) (hf : IsThetaTypeForm N f)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    IsThetaTypeForm N (VOA.Classification.COne.thetaSlash γ f) where
  holo := by
    refine ((differentiableOn_comp_mobius hf.holo γ).mul differentiableOn_thetaRef).div
      (differentiableOn_comp_mobius differentiableOn_thetaRef γ) fun τ hτ =>
        thetaRef_ne_zero_of_im_pos (im_mobius_pos γ hτ)
  multiplier δ hδ τ hτ := by
    -- `γ δ = δ' γ` with `δ' = γ δ γ⁻¹ ∈ Γ₁(N)`
    have hδ' := conj_mem_Gamma1 hγ hδ
    have hγτ := im_mobius_pos γ hτ
    have hδτ := im_mobius_pos δ hτ
    have e : mobius γ (mobius δ τ) = mobius (γ * δ * γ⁻¹) (mobius γ τ) := by
      rw [← mobius_mul _ _ hτ, ← mobius_mul _ _ hτ, inv_mul_cancel_right]
    have hm := hf.multiplier _ hδ' (mobius γ τ) hγτ
    have n1 := thetaRef_ne_zero_of_im_pos hγτ
    have n2 := thetaRef_ne_zero_of_im_pos (im_mobius_pos γ hδτ)
    simp only [VOA.Classification.COne.thetaSlash]
    rw [e] at n2 ⊢
    field_simp
    linear_combination (thetaRef τ * thetaRef (mobius δ τ)) * hm
  cusps δ := by
    obtain ⟨C, hC⟩ := hf.cusps (γ * δ)
    refine ⟨C, fun τ hτ => ?_⟩
    have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos hτ
    have hδτ := im_mobius_pos δ hτ0
    have hc4 : 4 ∣ γ 1 0 := by
      have := (CongruenceSubgroup.Gamma0_mem.1 hγ)
      have hN : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 this
      exact (Int.natCast_dvd_natCast.2 h4).trans hN
    have hθ := norm_thetaRef_mobius hc4 hδτ
    have hθ0 := thetaRef_ne_zero_of_im_pos hδτ
    have hj : 0 < ‖(γ 1 0 : ℂ) * mobius δ τ + γ 1 1‖ := norm_pos_iff.2 (denom_ne_zero γ hδτ)
    have hjδ : 0 < ‖(δ 1 0 : ℂ) * τ + δ 1 1‖ := norm_pos_iff.2 (denom_ne_zero δ hτ0)
    simp only [VOA.Classification.COne.thetaSlash]
    rw [norm_div, norm_mul, hθ, ← mobius_mul γ δ hτ0]
    have hb := hC τ hτ
    rw [denom_mul γ δ hτ0, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at hb
    have hθn : 0 < ‖thetaRef (mobius δ τ)‖ := norm_pos_iff.2 hθ0
    set x := ‖(γ 1 0 : ℂ) * mobius δ τ + γ 1 1‖ ^ (1 / 2 : ℝ)
    have hx : 0 < x := Real.rpow_pos_of_pos hj _
    rw [mul_div_mul_right _ _ hθn.ne', div_le_iff₀ hx]
    calc ‖f (mobius (γ * δ) τ)‖ ≤ C * (x * ‖(δ 1 0 : ℂ) * τ + δ 1 1‖ ^ (1 / 2 : ℝ)) := hb
      _ = C * ‖(δ 1 0 : ℂ) * τ + δ 1 1‖ ^ (1 / 2 : ℝ) * x := by ring

end IsThetaTypeForm

end VOA.Classification.COne
