/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeCusp

/-!
# Serre–Stark S3-1g: `T(p²)` maps `M_{1/2}(N, χ)` to itself

`SSHecke.isThetaTypeFormChar_heckeT`: for `24 ∣ N`, `p ∤ N` an odd prime and `χ` a Dirichlet
character mod `N`, Shimura's Hecke operator `T(p²)` preserves `IsThetaTypeFormChar N χ`
(holomorphy, the `χ`-twisted `θ`-multiplier law on `Γ₀(N)`, and holomorphy at every cusp).
-/

open Complex Filter Topology
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

variable {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ}

theorem mobZ_cosetMat_eq (i : HIdx p) (τ : ℂ) :
    mobZ (cosetMat p i) τ = ((aCo p i : ℂ) * τ + cosetMat p i 0 1) / (dCo p i : ℂ) := by
  simp [mobZ, cosetMat_00, cosetMat_10, cosetMat_11]

theorem differentiable_mobZ_cosetMat (i : HIdx p) : Differentiable ℂ (mobZ (cosetMat p i)) := by
  have : mobZ (cosetMat p i) = fun τ =>
      ((aCo p i : ℂ) * τ + cosetMat p i 0 1) / (dCo p i : ℂ) := funext (mobZ_cosetMat_eq i)
  rw [this]
  exact ((differentiable_id.const_mul _).add_const _).div_const _

theorem heckeT_holo [Fact p.Prime] {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperSet) :
    DifferentiableOn ℂ (heckeT χ p f) upperSet := by
  have hp0 := (Fact.out : p.Prime).pos
  have : heckeT χ p f = fun τ => ∑ i : HIdx p, hw p i * kap χ p i * f (mobZ (cosetMat p i) τ) :=
    rfl
  rw [this]
  refine DifferentiableOn.fun_sum fun i _ => ?_
  exact (hf.comp (differentiable_mobZ_cosetMat i).differentiableOn
    (fun τ hτ => im_mobZ_cosetMat hp0 i hτ)).const_mul _

/-! ## Cusps -/

theorem denZ_cosetMat_mul (i : HIdx p) (γ : SL(2, ℤ)) (τ : ℂ) :
    denZ (cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ =
      (dCo p i : ℂ) * ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  simp only [denZ, Matrix.mul_apply, Fin.sum_univ_two, cosetMat_10, cosetMat_11]
  push_cast; ring

theorem dCo_le (hp : 0 < p) (i : HIdx p) : (dCo p i : ℝ) ≤ (p : ℝ) ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rcases i with b | h | u <;> simp [dCo] <;> nlinarith

/-- Each coset term is bounded at every cusp. -/
theorem coset_cusp_bound (hp : p.Prime) (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) (i : HIdx p) (γ : SL(2, ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℂ, 1 ≤ τ.im →
      ‖f (mobZ (cosetMat p i) (mobius γ τ))‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
  have hp0 := hp.pos
  have hpR : (0 : ℝ) < p := Nat.cast_pos.2 hp0
  set X := cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) with hX
  have hdetX : X.det = (p : ℤ) ^ 2 := by rw [hX, Matrix.det_mul, det_cosetMat, γ.det_coe, mul_one]
  obtain ⟨δ, U, hXU, hU10, hU00, hU11, hUdet⟩ := exists_SL_mul_upper X (by rw [hdetX]; positivity)
  rw [hdetX] at hUdet
  have hε : (0 : ℝ) < 1 / (p : ℝ) ^ 2 := by positivity
  obtain ⟨C, hC⟩ := IsThetaTypeForm.cusp_bound_of_le h4 hN hf δ hε
  refine ⟨max C 0 * p, by positivity, fun τ hτ => ?_⟩
  have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos hτ
  have hU11R : (1 : ℝ) ≤ (U 1 1 : ℝ) := by exact_mod_cast hU11
  have hU00R : (1 : ℝ) ≤ (U 0 0 : ℝ) := by exact_mod_cast hU00
  have hU11le : (U 1 1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    have : (U 0 0 : ℝ) * U 1 1 = (p : ℝ) ^ 2 := by exact_mod_cast hUdet
    nlinarith
  have hdenU : denZ U τ = (U 1 1 : ℂ) := by simp [denZ, hU10]
  have hdenU0 : denZ U τ ≠ 0 := by rw [hdenU]; exact_mod_cast (by omega : U 1 1 ≠ 0)
  have hmob : mobZ (cosetMat p i) (mobius γ τ) = mobius δ (mobZ U τ) := by
    rw [← mobZ_cosetMat_mul_SL i γ hτ0, ← hX, hXU, mobZ_mul _ _ hdenU0]; rfl
  -- the imaginary part
  have hw : 1 / (p : ℝ) ^ 2 ≤ (mobZ U τ).im := by
    have : mobZ U τ = ((U 0 0 : ℂ) * τ + U 0 1) / (U 1 1 : ℂ) := by simp [mobZ, hU10]
    rw [this, show ((U 1 1 : ℤ) : ℂ) = (((U 1 1 : ℤ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_im]
    simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have h1 : 1 ≤ (U 0 0 : ℝ) * τ.im := by nlinarith
    have h2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    nlinarith
  have hb := hC _ hw
  -- the automorphy factor
  have hden : ‖(δ 1 0 : ℂ) * mobZ U τ + δ 1 1‖ =
      (dCo p i : ℝ) / (U 1 1 : ℝ) * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    have h1 := denZ_mul (δ : Matrix (Fin 2) (Fin 2) ℤ) U hdenU0
    rw [← hXU, hX, denZ_cosetMat_mul, hdenU] at h1
    have hU11C : ((U 1 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hU11.ne'
    have h2 : (δ 1 0 : ℂ) * mobZ U τ + δ 1 1 =
        (dCo p i : ℂ) * ((γ 1 0 : ℂ) * τ + γ 1 1) / (U 1 1 : ℂ) := by
      rw [eq_div_iff hU11C, h1]; rfl
    rw [h2, norm_div, norm_mul]
    simp only [Complex.norm_intCast]
    rw [abs_of_pos (by exact_mod_cast dCo_pos hp0 i), abs_of_pos (by exact_mod_cast hU11)]
    ring
  rw [hmob]
  refine hb.trans ?_
  rw [hden]
  have hd0 : (0 : ℝ) ≤ (dCo p i : ℝ) / (U 1 1 : ℝ) := by
    have := dCo_pos hp0 i; positivity
  have hdle : (dCo p i : ℝ) / (U 1 1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [dCo_le hp0 i]
  rw [Real.mul_rpow hd0 (norm_nonneg _)]
  have hsq : ((dCo p i : ℝ) / (U 1 1 : ℝ)) ^ (1 / 2 : ℝ) ≤ p := by
    calc ((dCo p i : ℝ) / (U 1 1 : ℝ)) ^ (1 / 2 : ℝ) ≤ ((p : ℝ) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hd0 hdle (by norm_num)
      _ = p := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hpR.le]; norm_num
  have hn := Real.rpow_nonneg (norm_nonneg ((γ 1 0 : ℂ) * τ + γ 1 1)) (1 / 2 : ℝ)
  have hpos := Real.rpow_nonneg hd0 (1 / 2 : ℝ)
  calc C * (((dCo p i : ℝ) / (U 1 1 : ℝ)) ^ (1 / 2 : ℝ) *
        ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ))
      ≤ max C 0 * (((dCo p i : ℝ) / (U 1 1 : ℝ)) ^ (1 / 2 : ℝ) *
        ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hpos hn)
    _ ≤ max C 0 * (p * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hn) (le_max_right _ _)
    _ = max C 0 * p * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by ring

theorem heckeT_cusps [Fact p.Prime] (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) (γ : SL(2, ℤ)) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖heckeT χ p f (mobius γ τ)‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
  have hp : p.Prime := Fact.out
  choose C hC0 hC using fun i => coset_cusp_bound hp h4 hN hf i γ
  refine ⟨∑ i : HIdx p, ‖hw p i * kap χ p i‖ * C i, fun τ hτ => ?_⟩
  unfold heckeT
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC i τ hτ) (norm_nonneg _)

/-! ## The main theorem -/

/-- **Shimura's `T(p²)` preserves `M_{1/2}(N, χ)`** (`24 ∣ N`, `p ∤ N` an odd prime). -/
theorem isThetaTypeFormChar_heckeT [hpf : Fact p.Prime] (hp2 : p ≠ 2) (h24 : 24 ∣ N)
    (hpN : Nat.Coprime p N) {f : ℂ → ℂ} (hf : IsThetaTypeFormChar N χ f) :
    IsThetaTypeFormChar N χ (heckeT χ p f) := by
  have hp : p.Prime := hpf.out
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hN : 0 < N := Nat.pos_of_ne_zero (by
    rintro rfl; exact hp.one_lt.ne' ((Nat.coprime_zero_right p).1 hpN))
  have hlaw := heckeT_chiLaw χ hp hp2 h24 hpN (f := f) (fun γ hγ τ hτ => hf.character γ hγ τ hτ)
  refine ⟨⟨heckeT_holo χ hf.thetaType.holo, fun γ hγ τ hτ => ?_,
    heckeT_cusps χ h4 hN hf.thetaType⟩, fun γ hγ τ hτ => hlaw γ hγ τ hτ⟩
  have h := hlaw γ (CongruenceSubgroup.Gamma1_in_Gamma0 N hγ) τ hτ
  have hd : ((γ 1 1 : ℤ) : ZMod N) = 1 := ((CongruenceSubgroup.Gamma1_mem N γ).1 hγ).2.1
  rw [hd, map_one, one_mul] at h
  exact h

end SSHecke

end VOA.Classification.COne
