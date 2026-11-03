/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpKatzSpanning
import VOA.Classification.COne.SerreStarkSturm

/-!
# Integral-weight Sturm bounds at Gamma1 level

The norm-to-level-one argument gives an unconditional coefficient cutoff,
injectivity of truncation, and finite dimensionality. The bound uses the SL2
index, without optimizing by the central involution. It is an upper bound,
not a dimension formula and not an arithmetic spanning theorem.
-/

open Complex Filter Topology
open UpperHalfPlane (qExpansion hasSum_qExpansion)
open scoped MatrixGroups ModularForm Manifold UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- The integral-weight norm-to-level-one coefficient cutoff. -/
def integralSturmBound (N : ℕ) (k : ℤ) : ℕ :=
  (k * (gamma1Index N : ℤ)).toNat / 12 + 1

/-- Vanishing initial coefficients give exponential decay at infinity. -/
theorem norm_le_of_coeff_lt_Gamma1 {N : ℕ} [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (B : ℕ) (hc : ∀ n < B, (qExpansion 1 F).coeff n = 0) :
    ∃ K : ℝ, ∀ τ : ℍ, 1 ≤ τ.im →
      ‖F τ‖ ≤ K * Real.exp (-(2 * Real.pi * B * τ.im)) := by
  have hasSum_exp (τ : ℍ) : HasSum
      (fun n : ℕ => (qExpansion 1 F).coeff n * cexp (2 * Real.pi * I * n * τ))
      (F τ) := by
    simpa only [smul_eq_mul, IsThetaTypeForm.qParam_one_pow] using
      hasSum_qExpansion one_pos
        (SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods_Gamma1 N))
        (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ
  -- `|a_n| e^{-π n} ≤ K₀` from convergence at `τ₀ = i/2`
  have h0 : 0 < (I / 2 : ℂ).im := by simp
  have hs := (hasSum_exp ⟨I / 2, h0⟩).summable
  have hterm : ∀ n : ℕ, ‖(qExpansion 1 F).coeff n * cexp (2 * Real.pi * I * n * (I / 2))‖ =
      ‖(qExpansion 1 F).coeff n‖ * Real.exp (-(Real.pi * n)) := by
    intro n
    rw [norm_mul, Complex.norm_exp]
    congr 2
    have : (2 * (Real.pi : ℂ) * I * n * (I / 2)) = ((-(Real.pi * n) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [this, Complex.ofReal_re]
  obtain ⟨K₀, hK₀⟩ := (hs.tendsto_atTop_zero.norm).bddAbove_range
  have hK₀' : ∀ n, ‖(qExpansion 1 F).coeff n‖ * Real.exp (-(Real.pi * n)) ≤ K₀ := fun n => by
    rw [← hterm]; exact hK₀ ⟨n, rfl⟩
  have hK₀0 : 0 ≤ K₀ := (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans (hK₀' 0)
  have hr0 : 0 ≤ Real.exp (-Real.pi) := (Real.exp_pos _).le
  have hr1 : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  refine ⟨K₀ * Real.exp (2 * Real.pi * B) * (1 - Real.exp (-Real.pi))⁻¹, fun τ hτ => ?_⟩
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (K₀ * Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)))
  have hfin : K₀ * Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
      (1 - Real.exp (-Real.pi))⁻¹ = K₀ * Real.exp (2 * Real.pi * B) *
      (1 - Real.exp (-Real.pi))⁻¹ * Real.exp (-(2 * Real.pi * B * τ.im)) := by ring
  rw [← hfin]
  refine (hasSum_exp τ).norm_le_of_bounded hg fun n => ?_
  by_cases hn : n < B
  · rw [hc n hn, zero_mul, norm_zero]
    positivity
  · push Not at hn
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * I * n * τ).re = -(2 * Real.pi * n * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hexp : Real.exp (Real.pi * n) * Real.exp (-(2 * Real.pi * n * τ.im)) ≤
        Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
          Real.exp (-Real.pi) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hnB : (B : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hnB))
        (sub_nonneg.2 hτ)]
    have h1 : Real.exp (-(Real.pi * n)) * Real.exp (Real.pi * n) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc ‖(qExpansion 1 F).coeff n‖ * Real.exp (-(2 * Real.pi * n * τ.im))
        = (‖(qExpansion 1 F).coeff n‖ * Real.exp (-(Real.pi * n))) *
          (Real.exp (Real.pi * n) * Real.exp (-(2 * Real.pi * n * τ.im))) := by
          linear_combination (-(‖(qExpansion 1 F).coeff n‖ *
            Real.exp (-(2 * Real.pi * n * τ.im)))) * h1
      _ ≤ K₀ * (Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
          Real.exp (-Real.pi) ^ n) :=
          mul_le_mul (hK₀' n) hexp (by positivity) hK₀0
      _ = K₀ * Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
          Real.exp (-Real.pi) ^ n := by ring


/-- A Gamma1 modular form with zero coefficients below the cutoff is zero. -/
theorem eq_zero_of_coeff_lt_Gamma1 {N : ℕ} [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hc : ∀ n < integralSturmBound N k, (qExpansion 1 F).coeff n = 0) : F = 0 := by
  classical
  set B := integralSturmBound N k
  set G := ModularForm.norm 𝒮ℒ F
  choose M A hMA using quotientFunc_bounded F
  obtain ⟨K, hK⟩ := norm_le_of_coeff_lt_Gamma1 F B hc
  set q₀ : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ :=
    ⟦(1 : 𝒮ℒ)⟧
  letI := Fintype.ofFinite
    (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  set P := ∏ q ∈ Finset.univ.erase q₀, M q
  set T := max 1 (∑ q, |A q|)
  have hG : ∀ τ : ℍ, T ≤ τ.im →
      ‖G τ‖ ≤ (K * P) * Real.exp (-(2 * Real.pi * B * τ.im)) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ.im := (le_max_left _ _).trans hτ
    have hAq : ∀ q, A q ≤ τ.im := fun q =>
      (le_abs_self _).trans ((Finset.single_le_sum (fun q _ => abs_nonneg (A q))
        (Finset.mem_univ q)).trans ((le_max_right _ _).trans hτ))
    rw [ModularForm.coe_norm, Finset.prod_apply, norm_prod,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀)]
    have hq₀ : SlashInvariantForm.quotientFunc F q₀ τ = F τ := by simp [q₀]
    rw [hq₀]
    have hP : ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc F q τ‖ ≤ P :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun q _ => hMA q τ (hAq q))
    calc
      _ ≤ (K * Real.exp (-(2 * Real.pi * B * τ.im))) * P :=
        mul_le_mul (hK τ hτ1) hP
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) ((norm_nonneg _).trans (hK τ hτ1))
      _ = _ := by ring
  have hcoeff : ∀ n < B, (qExpansion 1 G).coeff n = 0 :=
    fun n hn => coeff_eq_zero_of_decay G B hG n hn
  have hord : (B : ℕ∞) ≤ (qExpansion 1 G).order := PowerSeries.nat_le_order _ _ hcoeff
  have hG0 : G = 0 := by
    refine ModularForm.sturm_bound_levelOne (lt_of_lt_of_le ?_ hord)
    change (((k * (gamma1Index N : ℤ)).toNat / 12 : ℕ) : ℕ∞) < (B : ℕ∞)
    exact_mod_cast Nat.lt_succ_self ((k * (gamma1Index N : ℤ)).toNat / 12)
  exact DFunLike.coe_injective ((ModularForm.norm_eq_zero_iff 𝒮ℒ F).mp hG0)

/-- The first B coefficients as a complex linear map. -/
def gamma1CoeffMap (N : ℕ) (k : ℤ) (B : ℕ) :
    ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      (Fin B → ℂ) where
  toFun F n := (qExpansion 1 F).coeff n
  map_add' F G := by
    funext n
    change (qExpansion 1 (F + G)).coeff n = _
    rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1 N) F G, map_add]
    rfl
  map_smul' c F := by
    funext n
    change (qExpansion 1 (c • F)).coeff n = _
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1 N) c F,
      PowerSeries.coeff_smul]
    rfl

/-- Truncation at the norm bound is injective. -/
theorem gamma1CoeffMap_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (gamma1CoeffMap N k (integralSturmBound N k)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  exact eq_zero_of_coeff_lt_Gamma1 F (fun n hn => congrFun hF ⟨n, hn⟩)

/-- Finite dimensionality at every positive Gamma1 level and every integral weight. -/
theorem finiteDimensional_Gamma1 (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ
      (ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :=
  Module.Finite.of_injective _ (gamma1CoeffMap_injective N k)

/-- The norm bound also bounds the dimension, but need not equal it. -/
theorem finrank_Gamma1_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ
      (ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) ≤
        integralSturmBound N k := by
  simpa using LinearMap.finrank_le_finrank_of_injective (gamma1CoeffMap_injective N k)

end VOA.Classification.COne.SSHecke
