/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocCoeffReduction
import VOA.Huang.AssocCommutator
import VOA.Huang.LogRemovalOps

/-!
# Transformation rules of the product expansion coefficients

This file transfers the identities satisfied by
a product of intertwining operators `⟨f, 𝒴₁(w₁, 1+u) 𝒴₂(w₂, 1) w₃⟩` (`u = e^t`) to its expansion
coefficients at the iterate point `u = 0`, the coefficients `c(μ, k)` of `u^μ (log u)^k`
(`LogRemovalCoeff.logCoeff` on `overlapDomain`).  These rules are what turns the span of the
coefficient functionals `(w₁, w₂) ↦ c(μ, k)` into a module (stages HL3–HL5).

## Main results
* `prodFunZ` (the product at `z₂ = 1` summed over all of `ℤ`), `prodFunZ_shift`,
  `prodFunZ_eq_prodFun` (on a base), `logCoeff_congr`, `logCoeff_sum`, `hasLogExp_sum`.
* `prodFunZ_hasLogExp_holds`: every integer-shifted canonical product has a finite log-expansion
  (strongly rational `V`).
* **`L₋₁` on `w₁`**: `prodSeries_Lm1_left`, `hasDerivAt_prodFun`
  (`d/dt F(w₁) = e^t F(L₋₁ w₁)`), `logCoeff_Lm1_left`
  (`c_{L₋₁w₁}(μ − 1, k) = μ c(μ, k) + (k + 1) c(μ, k + 1)`), and `logCoeff_Lm1_left_holds`.
* **Commutator**: `binPS` (`(1 + y)ⁿ`, `n ∈ ℤ`), `psEval_binPS`, `prodFunZ_commutator_holds`
  (function identity on `overlapDomain`), `logCoeff_commutator_holds` (the identity on
  coefficients, with the binomial Cauchy product for the `w₁`-terms).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.AssocCoeffRules

open VOA VOA.Huang.MatrixCoeff VOA.Huang.Convergence VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.FuchsianODE
open VOA.Huang.AssocCommutator VOA.Huang.AssocCoeffReduction VOA.Huang.HuangODEIterPoint
open VOA.Huang.HuangODEAlgebra
open VOA.Huang.FrobeniusLog (logFun halfPlane LogGood psEval)
open Filter Topology
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-! ## Generalities on `logCoeff` -/

section General

variable {U : Set ℂ}

theorem hasLogExp_congr {F G : ℂ → ℂ} (h : ∀ t ∈ U, F t = G t) (hF : HasLogExp U F) :
    HasLogExp U G := by
  obtain ⟨E, hE⟩ := hF
  exact ⟨E, fun t ht => by rw [← h t ht, hE t ht]⟩

theorem logCoeff_congr (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F G : ℂ → ℂ} (h : ∀ t ∈ U, F t = G t) (hF : HasLogExp U F) (μ : ℂ) (k : ℕ) :
    logCoeff U F μ k = logCoeff U G μ k := by
  obtain ⟨E, hE⟩ := hF
  have hG : IsExpOn U G E := fun t ht => by rw [← h t ht, hE t ht]
  rw [logCoeff_eq hU hsub hne hE, logCoeff_eq hU hsub hne hG]

theorem hasLogExp_zero : HasLogExp U (fun _ => 0) :=
  ⟨⟨Empty, (fun _ => 0), (fun _ => fun _ => 0), fun j => j.elim⟩,
    fun t _ => by simp [LogExp.eval]⟩

theorem hasLogExp_sum {ι : Type*} (S : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ S, HasLogExp U (F i)) : HasLogExp U (fun t => ∑ i ∈ S, F i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (hasLogExp_zero (U := U))
  | insert i S hi ih =>
    have h := hasLogExp_add (hF i (Finset.mem_insert_self i S))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
    refine hasLogExp_congr (fun t _ => ?_) h
    simp only [Pi.add_apply, Finset.sum_insert hi]

theorem logCoeff_zero (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty) (μ : ℂ)
    (k : ℕ) : logCoeff U (fun _ => 0) μ k = 0 := by
  have h : IsExpOn U (fun _ => 0)
      ⟨Empty, (fun _ => 0), (fun _ => fun _ => 0), fun j => j.elim⟩ :=
    fun t _ => by simp [LogExp.eval]
  rw [logCoeff_eq hU hsub hne h]
  simp [LogExp.coeff]

theorem logCoeff_sum (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {ι : Type*} (S : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i ∈ S, HasLogExp U (F i)) (μ : ℂ)
    (k : ℕ) : logCoeff U (fun t => ∑ i ∈ S, F i t) μ k = ∑ i ∈ S, logCoeff U (F i) μ k := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using logCoeff_zero hU hsub hne μ k
  | insert i S hi ih =>
    have hS : HasLogExp U (fun t => ∑ j ∈ S, F j t) :=
      hasLogExp_sum S fun j hj => hF j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, ← ih fun j hj => hF j (Finset.mem_insert_of_mem hj),
      ← logCoeff_add hU hsub hne (hF i (Finset.mem_insert_self i S)) hS]
    refine logCoeff_congr hU hsub hne (fun t _ => ?_) ?_ μ k
    · simp only [Pi.add_apply, Finset.sum_insert hi]
    · refine hasLogExp_congr (fun t _ => ?_)
        (hasLogExp_add (hF i (Finset.mem_insert_self i S)) hS)
      simp only [Pi.add_apply, Finset.sum_insert hi]

end General

/-! ## The product summed over `ℤ` at `z₂ = 1` -/

/-- The product at `z₂ = 1`, `z₁ = 1 + e^t`, summed over all `k ∈ ℤ` (line `S`, coset `ν − ℤ`). -/
noncomputable def prodFunZ (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν t : ℂ) : ℂ :=
  prodValueZ Y₁ Y₂ f w₁ w₂ w₃ S ν (1 + Complex.exp t) 1

theorem prodFunZ_shift (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν : ℂ) (d : ℤ) (t : ℂ) :
    prodFunZ Y₁ Y₂ f w₁ w₂ w₃ S (ν + d) t = prodFunZ Y₁ Y₂ f w₁ w₂ w₃ S ν t :=
  prodValueZ_shift _ _ _ _ _ _ _ _ _ _ d

theorem prodFunZ_eq_prodFun {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) {w₂ : M₂} {w₃ : M₃}
    {S ν : ℂ} (hb : IsBase Y₂ w₂ w₃ ν) (t : ℂ) :
    prodFunZ Y₁ Y₂ f w₁ w₂ w₃ S ν t = prodFun Y₁ Y₂ f w₁ w₂ w₃ S ν t :=
  prodValueZ_eq_prodValue f w₁ _ _ hb

/-- **Every integer-shifted canonical product has a finite log-expansion** at the iterate
point (strongly rational `V`, irreducible modules). -/
theorem prodFunZ_hasLogExp_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {S ν : ℂ} (hS : S = α₁ + α₂ + α₃ - h₄ - 2) (d : ℤ) (hν : ν = α₂ + α₃ - 1 - Q.h + d) :
    HasLogExp overlapDomain (prodFunZ Y₁ Y₂ f w₁ w₂ w₃ S ν) := by
  subst hS hν
  refine hasLogExp_congr (fun t _ => ?_) (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃ hf)
  rw [prodFunZ_shift, prodFunZ_eq_prodFun f w₁ (isBase_canonical Q hY₂ h₂ h₃)]

/-! ## `L₋₁` on the first vector -/

section Lm1

variable {A₁ : OrdVModule W M₁} {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}

/-- `prodCoeff (L₋₁ w₁) (n₁, n₂) = −n₁ · prodCoeff w₁ (n₁ − 1, n₂)`. -/
theorem prodCoeff_Lm1_left {Y₁ : IntertwiningModes M₁ M₅ M₄}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (n₁ n₂ : ℂ) :
    prodCoeff Y₁ Y₂ f (A₁.Lm1 w₁) w₂ w₃ n₁ n₂ = -n₁ * prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (n₁ - 1) n₂ := by
  simp only [prodCoeff, hY₁.L_neg_one, LinearMap.smul_apply, map_smul, smul_eq_mul]

/-- The product series of `L₋₁ w₁` (line `σ + 1`) is `−(θ + σ − ν₀ + 1)` of that of `w₁`. -/
theorem prodSeries_Lm1_left {Y₁ : IntertwiningModes M₁ M₅ M₄}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) :
    prodSeries Y₁ Y₂ f (A₁.Lm1 w₁) w₂ w₃ (σ + 1) ν₀
      = -(VOA.theta (prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀)
          + PowerSeries.C (σ - ν₀ + 1) * prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) := by
  ext k
  rw [coeff_prodSeries, prodCoeff_Lm1_left hY₁, map_neg, map_add, VOA.theta_coeff,
    PowerSeries.coeff_C_mul, coeff_prodSeries,
    show σ + 1 - ν₀ + k - 1 = σ - ν₀ + k by ring, show σ + 1 - ν₀ + k = σ - ν₀ + k + 1 by ring]
  ring

theorem prodSeries_Lm1_left_mem {Y₁ : IntertwiningModes M₁ M₅ M₄}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ)
    (hG : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS) :
    prodSeries Y₁ Y₂ f (A₁.Lm1 w₁) w₂ w₃ (σ + 1) ν₀ ∈ SubexpPS := by
  rw [prodSeries_Lm1_left hY₁]
  exact SubexpPS.neg_mem (SubexpPS.add_mem (theta_mem_subexpPS hG)
    (SubexpPS.mul_mem (C_mem_subexp _) hG))

/-- **`L₋₁`-derivative at the iterate point**: `d/dt F(w₁)(t) = e^t · F(L₋₁ w₁)(t)` on
`overlapDomain` (`F` = the product at `z₂ = 1`, `z₁ = 1 + e^t`). -/
theorem hasDerivAt_prodFun {Y₁ : IntertwiningModes M₁ M₅ M₄}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ)
    (hG : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS) {t : ℂ} (ht : t ∈ overlapDomain) :
    HasDerivAt (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀)
      (Complex.exp t * prodFun Y₁ Y₂ f (A₁.Lm1 w₁) w₂ w₃ (σ + 1) ν₀ t) t := by
  set G := prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ with hGdef
  set κ := σ - ν₀ + 1 with hκ
  have hEv : ∀ y ∈ overlapDomain, prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ y = Ev κ 0 G y := by
    intro y hy
    rw [prodFun_eq_Ev Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ 0 0 hG hy]
    simp [hκ, hGdef]
  have hev : prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ =ᶠ[𝓝 t] Ev κ 0 G :=
    Filter.eventually_of_mem (isOpen_overlapDomain.mem_nhds ht) hEv
  refine (hasDerivAt_Ev κ 0 hG ht).congr_of_eventuallyEq hev |>.congr_deriv ?_
  -- compute both sides
  have hL := prodFun_eq_Ev Y₁ Y₂ f (A₁.Lm1 w₁) w₂ w₃ (σ + 1) ν₀ 0 0
    (prodSeries_Lm1_left_mem hY₁ Y₂ f w₁ w₂ w₃ σ ν₀ hG) ht
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero] at hL
  rw [hL, prodSeries_Lm1_left hY₁, ← hκ]
  have hz := one_add_exp_ne_zero ht
  have hy := norm_xt_lt_one ht
  have hθ := theta_mem_subexpPS hG
  have hκG := SubexpPS.mul_mem (C_mem_subexp κ) hG
  have h1x : 1 - xt t = Complex.exp t * xt t := by
    simp only [xt]; field_simp; ring
  have hcp : (1 + Complex.exp t) ^ (-(σ + 1 - ν₀ + 1)) = (1 + Complex.exp t) ^ (-κ) * xt t := by
    rw [show -(σ + 1 - ν₀ + 1) = -κ - 1 by rw [hκ]; ring, Complex.cpow_sub _ _ hz,
      Complex.cpow_one, xt, div_eq_mul_inv]
  simp only [Ev]
  rw [psEval_DOp κ 0 hG hy, psEval_neg, psEval_add hθ hκG hy, psEval_C_mul, hcp, h1x]
  ring

/-- `F(L₋₁ w₁)(t) = e^{−t} · d/dt F(w₁)(t)` on `overlapDomain`. -/
theorem prodFun_Lm1_left_eq {Y₁ : IntertwiningModes M₁ M₅ M₄}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ)
    (hG : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS) {t : ℂ} (ht : t ∈ overlapDomain) :
    prodFun Y₁ Y₂ f (A₁.Lm1 w₁) w₂ w₃ (σ + 1) ν₀ t
      = Complex.exp (-1 * t) * _root_.deriv (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) t := by
  rw [(hasDerivAt_prodFun hY₁ Y₂ f w₁ w₂ w₃ σ ν₀ hG ht).deriv, ← mul_assoc, ← Complex.exp_add,
    show -1 * t + t = 0 by ring, Complex.exp_zero, one_mul]

/-- **`L₋₁` on coefficients**: `c_{L₋₁w₁}(μ − 1, k) = μ c(μ, k) + (k + 1) c(μ, k + 1)`,
for any product with a subexponential series and a finite log-expansion at the iterate point. -/
theorem logCoeff_Lm1_left {Y₁ : IntertwiningModes M₁ M₅ M₄}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ)
    (hG : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS)
    (hF : HasLogExp overlapDomain (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀)) (μ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (prodFun Y₁ Y₂ f (A₁.Lm1 w₁) w₂ w₃ (σ + 1) ν₀) (μ - 1) k
      = μ * logCoeff overlapDomain (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) μ k
        + ((k : ℂ) + 1) * logCoeff overlapDomain (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) μ (k + 1) := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  obtain ⟨hD, hDc⟩ := logCoeff_deriv hU hs hne hF μ k
  have hE := hasLogExp_exp_mul hD (-1)
  rw [logCoeff_congr hU hs hne (fun t ht => (prodFun_Lm1_left_eq hY₁ Y₂ f w₁ w₂ w₃ σ ν₀ hG ht))
    (hasLogExp_congr (fun t ht => (prodFun_Lm1_left_eq hY₁ Y₂ f w₁ w₂ w₃ σ ν₀ hG ht).symm) hE),
    show μ - 1 = μ + -1 by ring, logCoeff_exp_mul hU hs hne hD, hDc]

end Lm1

/-- `logCoeff_Lm1_left` for irreducible modules of a strongly rational `V` (canonical data). -/
theorem logCoeff_Lm1_left_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) (μ : ℂ) (k : ℕ) :
    prodExpCoeff Y₁ Y₂ f (P₁.isMod.Lm1 w₁) w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2 + 1)
        (α₂ + α₃ - 1 - Q.h) (μ - 1) k
      = μ * prodExpCoeff Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) μ k
        + ((k : ℂ) + 1) * prodExpCoeff Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₂ + α₃ - 1 - Q.h) μ (k + 1) :=
  logCoeff_Lm1_left hY₁ Y₂ f w₁ w₂ w₃ _ _
    (prodSeries_mem_subexpPS hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf)
    (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃ hf) μ k

/-! ## The commutator identity at the iterate point -/

/-- The power series of `(1 + y)ⁿ`, `n ∈ ℤ`. -/
noncomputable def binPS (n : ℤ) : PowerSeries ℂ :=
  if 0 ≤ n then (1 + PowerSeries.X) ^ n.toNat else geom (-1) ^ (-n).toNat

theorem one_add_X_mem_subexp : (1 + PowerSeries.X : PowerSeries ℂ) ∈ SubexpPS :=
  SubexpPS.add_mem SubexpPS.one_mem X_mem_subexp

theorem binPS_mem (n : ℤ) : binPS n ∈ SubexpPS := by
  unfold binPS
  split_ifs
  · exact SubexpPS.pow_mem one_add_X_mem_subexp _
  · exact SubexpPS.pow_mem geom_neg_one_mem _

theorem psEval_binPS (n : ℤ) {y : ℂ} (hy : ‖y‖ < 1) : psEval (binPS n) y = (1 + y) ^ n := by
  unfold binPS
  split_ifs with h
  · rw [psEval_pow one_add_X_mem_subexp hy, psEval_add SubexpPS.one_mem X_mem_subexp hy,
      psEval_one, psEval_X, ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [psEval_pow geom_neg_one_mem hy, psEval_geom_neg_one hy, inv_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← zpow_neg, neg_neg]

theorem norm_exp_lt_one {t : ℂ} (ht : t ∈ overlapDomain) : ‖Complex.exp t‖ < 1 := by
  rw [Complex.norm_exp]; exact Real.exp_lt_one_iff.mpr ht.1

/-- **The commutator identity at `z₂ = 1`, `z₁ = 1 + e^t`** (functions on `overlapDomain`),
strongly rational `V`, irreducible modules, homogeneous `v ∈ V_β`. -/
theorem prodFunZ_commutator_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β) (m : ℤ) :
    ∃ N : ℤ, ∀ t ∈ overlapDomain,
    prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM v) m) w₁ w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h) t
      = prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM v) m w₃)
          (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h) t
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * (psEval (binPS (m - i)) (Complex.exp t)
            * prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM v) i w₁) w₂ w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ)) (α₂ + α₃ - 1 - Q.h) t)
        + ∑ i ∈ Finset.Ico 0 N, cbz m i
            * prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM v) i w₂) w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ))
                (α₂ + α₃ - 1 - Q.h + (m - i : ℤ)) t := by
  obtain ⟨N₁, hN₁⟩ := P₁.isMod.truncation v w₁
  obtain ⟨N₂, hN₂⟩ := P₂.isMod.truncation v w₂
  refine ⟨max N₁ N₂, fun t ht => ?_⟩
  have hz₂ : (1 : ℂ) ≠ 0 := one_ne_zero
  have hz : ‖(1 : ℂ)‖ < ‖1 + Complex.exp t‖ := by rw [norm_one]; exact one_lt_norm ht
  have hz₁ : 1 + Complex.exp t ≠ 0 := one_add_exp_ne_zero ht
  have key := prodValueZ_commutator hY₁ hY₂ v m f w₁ w₂ w₃
    (fun i hi => hN₁ i (le_of_max_le_left hi)) (fun i hi => hN₂ i (le_of_max_le_right hi))
    (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h) hz₁ hz₂
    (summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hv h₃ m) hf (by ring) (m + 1 - β)
      (by push_cast; ring) hz₂ hz)
    (fun i _ => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂
      (VOA.mode_mem_weight P₁.isMod hv h₁ i) h₂ h₃ hf (by push_cast; ring) 0
      (by push_cast; ring) hz₂ hz)
    (fun i _ => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁
      (VOA.mode_mem_weight P₂.isMod hv h₂ i) h₃ hf (by push_cast; ring) (m + 1 - β)
      (by push_cast; ring) hz₂ hz)
  unfold prodFunZ
  rw [key]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [psEval_binPS _ (norm_exp_lt_one ht), Complex.cpow_intCast]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.one_cpow, mul_one]

/-- **The commutator identity on expansion coefficients** at the iterate point (strongly
rational `V`, irreducible modules, homogeneous `v ∈ V_β`):
`c_{f∘v_m}(μ,k) = c_{v_m w₃}(μ,k) + Σᵢ C(m,i) Σⱼ [(1+u)^{m−i}]ⱼ c_{vᵢw₁}(μ−j,k)
  + Σᵢ C(m,i) c_{vᵢw₂}(μ,k)`. -/
theorem logCoeff_commutator_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β) (m : ℤ) :
    ∃ N : ℤ, ∀ (μ : ℂ) (k : ℕ),
    logCoeff overlapDomain (prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM v) m) w₁ w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h)) μ k
      = logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM v) m w₃)
          (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h)) μ k
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * ∑ᶠ j : ℕ, PowerSeries.coeff j (binPS (m - i))
            * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM v) i w₁) w₂ w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ)) (α₂ + α₃ - 1 - Q.h)) (μ - j) k
        + ∑ i ∈ Finset.Ico 0 N, cbz m i
            * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM v) i w₂) w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ))
                (α₂ + α₃ - 1 - Q.h + (m - i : ℤ))) μ k := by
  obtain ⟨N, hN⟩ := prodFunZ_commutator_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf hv m
  refine ⟨N, fun μ k => ?_⟩
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  set S := α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 with hSdef
  set ν := α₂ + α₃ - 1 - Q.h with hνdef
  -- the three families of functions and their expansions
  set F₃ := prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM v) m w₃) S ν with hF₃
  set F₁ : ℤ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM v) i w₁) w₂ w₃
    (S + (m - i : ℤ)) ν with hF₁
  set F₂ : ℤ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM v) i w₂) w₃
    (S + (m - i : ℤ)) (ν + (m - i : ℤ)) with hF₂
  have e₃ : HasLogExp overlapDomain F₃ :=
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hv h₃ m) hf (by rw [hSdef]; ring) (m + 1 - β)
      (by rw [hνdef]; push_cast; ring)
  have e₁ : ∀ i, HasLogExp overlapDomain (F₁ i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
      (VOA.mode_mem_weight P₁.isMod hv h₁ i) h₂ h₃ hf (by rw [hSdef]; push_cast; ring) 0
      (by rw [hνdef]; push_cast; ring)
  have e₂ : ∀ i, HasLogExp overlapDomain (F₂ i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁
      (VOA.mode_mem_weight P₂.isMod hv h₂ i) h₃ hf (by rw [hSdef]; push_cast; ring) (m + 1 - β)
      (by rw [hνdef]; push_cast; ring)
  have e₁' : ∀ i, HasLogExp overlapDomain
      (fun t => cbz m i * (psEval (binPS (m - i)) (Complex.exp t) * F₁ i t)) := fun i =>
    hasLogExp_smul _ (hasLogExp_psEval_mul hs (e₁ i) (binPS_mem _))
  have e₂' : ∀ i, HasLogExp overlapDomain (fun t => cbz m i * F₂ i t) := fun i =>
    hasLogExp_smul _ (e₂ i)
  have eS₁ := hasLogExp_sum (Finset.Ico 0 N) (fun i _ => e₁' i)
  have eS₂ := hasLogExp_sum (Finset.Ico 0 N) (fun i _ => e₂' i)
  have hsum : ∀ t ∈ overlapDomain,
      prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM v) m) w₁ w₂ w₃ S ν t
        = ((F₃ + fun t => ∑ i ∈ Finset.Ico 0 N,
              cbz m i * (psEval (binPS (m - i)) (Complex.exp t) * F₁ i t))
          + fun t => ∑ i ∈ Finset.Ico 0 N, cbz m i * F₂ i t) t := fun t ht => hN t ht
  have eA := hasLogExp_add e₃ eS₁
  rw [logCoeff_congr hU hs hne hsum (hasLogExp_congr (fun t ht => (hsum t ht).symm)
      (hasLogExp_add eA eS₂)),
    logCoeff_add hU hs hne eA eS₂, logCoeff_add hU hs hne e₃ eS₁,
    logCoeff_sum hU hs hne _ (fun i _ => e₁' i), logCoeff_sum hU hs hne _ (fun i _ => e₂' i)]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (hasLogExp_psEval_mul hs (e₁ i) (binPS_mem _)),
      logCoeff_psEval_mul hU hs hne (e₁ i) (binPS_mem _)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (e₂ i)]

end VOA.Huang.AssocCoeffRules
