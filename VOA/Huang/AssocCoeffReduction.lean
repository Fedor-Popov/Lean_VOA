/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangODEIterPoint
import VOA.Huang.LogRemovalCoeff

/-!
# Associativity as an identity of expansion coefficients

`HuangODEIterPoint.prod_frobenius_expansion_holds` (Huang (3.3)) gives, for strongly rational `V`,
a finite log-expansion of the product `⟨f, 𝒴₁(w₁, 1+u)𝒴₂(w₂, 1)w₃⟩` at the iterate point
`u = e^t = 0`.  By `LogRemovalCoeff` its coefficient of `u^μ (log u)^k` is a well-defined number
`prodExpCoeff … μ k`, independent of the chosen expansion.  An iterate
`⟨f, 𝒴₃(𝒴₄(w₁, u)w₂, 1)w₃⟩` is log-free with coefficients the iterate matrix coefficients
(`iterExpCoeff`).  This file proves that **associativity at `z₂ = 1` follows from the
coefficientwise identity** `AssocCoeffIdentity` — the form in which the algebraic half of the
argument
(log removal + identification with iterates) has to be proved.

## Main results
* `iterSeries_mem_subexpPS` (unconditional for strongly rational `V`).
* `prod_isExpOn`, `prod_hasLogExp`: the product has a finite log-expansion on `overlapDomain`.
* `prodExpCoeff`, `prodExpCoeff_eq` (computed by ANY expansion).
* `iterExpCoeff`, `iterExpCoeff_eq` (`= iterCoeff` at `μ = −ν₀ − 1 + n`, `k = 0`; zero otherwise).
* `AssocCoeffIdentity` (named, TRUE: it is a consequence of Huang 2005 Thm 3.5 + HL IV by
  `prodExpCoeff_eq` applied to the iterate expansion), `associativityAtOne_of_coeffIdentity`,
  `associativityInput_of_coeffIdentity`.

## Status
No `sorry`, no new axioms.  `AssocCoeffIdentity` is open in this file.
-/

namespace VOA.Huang.AssocCoeffReduction

open VOA VOA.Huang.MatrixCoeff VOA.Huang.Convergence VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.FuchsianODE
open VOA.Huang.FrobeniusLog (logFun halfPlane LogGood LogFuchsianEq logGood_const
  logGood_of_logFuchsianEq)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

theorem overlapDomain_nonempty' : overlapDomain.Nonempty := overlapDomain_nonempty

/-! ## Iterates -/

/-- The iterate series is subexponential (unconditional for strongly rational `V`). -/
theorem iterSeries_mem_subexpPS (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier}
    (hY₃ : IsIntertwiningOperator Q.isMod P₃.isMod P₄.isMod Y₃)
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod Q.isMod Y₄)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    iterSeries Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h) ∈ SubexpPS := by
  obtain ⟨s₀, b, c₀, p, hc, hG⟩ :=
    (VOA.Huang.ModuleC2.huangODEInput_holds 𝒱 W hV).2 P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ Q.isMod
      hY₃ hY₄ h₁ h₂ h₃ hf (isBase_canonical Q hY₄ h₁ h₂)
  have hc₀ : ∀ i < s₀, c₀ i ∈ SubexpPS := fun i hi =>
    VOA.Huang.FuchsianODE.mem_subexpPS_of_mul_eq' (a := -1) (by simp) (hc i hi)
  exact mem_subexpPS.mpr (subexponential_of_fuchsianEq hc₀ hG)

/-- The log-free series of an iterate: `pₙ = C (iterCoeff(ν₀ − n, σ − ν₀ + n))`. -/
noncomputable def iterPoly (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) : ℕ → Polynomial ℂ :=
  fun n => Polynomial.C (PowerSeries.coeff n (iterSeries Y₃ Y₄ f w₁ w₂ w₃ σ ν₀))

/-- The coefficient of `u^μ (log u)^k` of an iterate: `exCoeff (−ν₀ − 1) (iterPoly …) μ k`. -/
noncomputable def iterExpCoeff (Y₃ : IntertwiningModes M₅ M₃ M₄)
    (Y₄ : IntertwiningModes M₁ M₂ M₅) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (σ ν₀ μ : ℂ) (k : ℕ) : ℂ :=
  exCoeff (-ν₀ - 1) (iterPoly Y₃ Y₄ f w₁ w₂ w₃ σ ν₀) μ k

/-- **Iterate coefficients**: at `μ = −ν₀ − 1 + n` the coefficient is the iterate matrix
coefficient `⟨f, 𝒴₃((w₁)_{ν₀−n} w₂)_{σ−ν₀+n} w₃⟩` for `k = 0`, and `0` for `k ≥ 1` (no logs). -/
theorem iterExpCoeff_eq (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) (n k : ℕ) :
    iterExpCoeff Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ (-ν₀ - 1 + n) k
      = if k = 0 then iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - n) (σ - ν₀ + n) else 0 := by
  unfold iterExpCoeff iterPoly
  rw [exCoeff_C, coeff_iterSeries]

/-- Away from the coset `−ν₀ − 1 + ℕ` the iterate has no terms. -/
theorem iterExpCoeff_eq_zero (Y₃ : IntertwiningModes M₅ M₃ M₄)
    (Y₄ : IntertwiningModes M₁ M₂ M₅) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (σ ν₀ μ : ℂ) (h : ∀ n : ℕ, -ν₀ - 1 + n ≠ μ) (k : ℕ) :
    iterExpCoeff Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ μ k = 0 :=
  exCoeff_of_forall_ne h _ k

/-! ## Products -/

/-- The product has a finite log-expansion on the overlap domain (strongly rational `V`). -/
theorem prod_hasLogExp (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    HasLogExp overlapDomain
      (prodFun Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)) := by
  obtain ⟨s, hs, c, hc, ι, hι, lam, p, a, -, hlog, -, heq⟩ :=
    VOA.Huang.HuangODEIterPoint.prod_frobenius_expansion_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
      h₁ h₂ h₃ hf
  refine ⟨@LogExp.mk ι hι lam (fun j => a j • p j)
    (fun j => (logGood_of_logFuchsianEq hs hc (hlog j)).smul (a j)), fun t ht => ?_⟩
  rw [heq t ht]
  simp only [LogExp.eval]
  exact Finset.sum_congr rfl fun j _ => (VOA.Huang.FrobeniusLog.logFun_smul _ _ _ _).symm

/-- The coefficient of `u^μ (log u)^k` of the product at the iterate point (`z₂ = 1`,
`z₁ = 1 + u`, canonical coset). -/
noncomputable def prodExpCoeff (Y₁ : IntertwiningModes M₁ M₅ M₄)
    (Y₂ : IntertwiningModes M₂ M₃ M₅) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (σ ν₀ μ : ℂ) (k : ℕ) : ℂ :=
  logCoeff overlapDomain (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) μ k

/-- `prodExpCoeff` is computed by any expansion of the product on the overlap domain. -/
theorem prodExpCoeff_eq (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) {E : LogExp}
    (hE : IsExpOn overlapDomain (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) E) (μ : ℂ) (k : ℕ) :
    prodExpCoeff Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ μ k = E.coeff μ k :=
  logCoeff_eq isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hE μ k

/-! ## The coefficient identity and the reduction -/

/-- **Associativity, coefficientwise** (named; TRUE for strongly rational `W`: Huang 2005 Thm 3.5
+ Huang–Lepowsky IV, transported by `prodExpCoeff_eq`).  Every product of intertwiners among
irreducible modules has, at the iterate point, the expansion coefficients of a finite sum of
iterates with irreducible intermediate modules (in particular no `log u` terms). -/
def AssocCoeffIdentity (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningModes (Qs j).carrier P₃.carrier P₄.carrier)
    (Y₄ : ∀ j, IntertwiningModes P₁.carrier P₂.carrier (Qs j).carrier),
    (∀ j, IsIntertwiningOperator (Qs j).isMod P₃.isMod P₄.isMod (Y₃ j)) ∧
    (∀ j, IsIntertwiningOperator P₁.isMod P₂.isMod (Qs j).isMod (Y₄ j)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    ∀ (μ : ℂ) (k : ℕ),
      prodExpCoeff Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) μ k
        = ∑ j, iterExpCoeff (Y₃ j) (Y₄ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) μ k

/-- **Associativity at `z₂ = 1` from the coefficient identity** (strongly rational `V`). -/
theorem associativityAtOne_of_coeffIdentity (hV : StronglyRational W)
    (h : AssocCoeffIdentity W) : AssociativityAtOne W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, hco⟩ := h P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  refine ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf x hx0 hx1
  set σ := α₁ + α₂ + α₃ - h₄ - 2
  set ν : Fin r → ℂ := fun j => α₁ + α₂ - 1 - (Qs j).h with hν
  -- the iterate expansion
  have hgood : ∀ j, LogGood (iterPoly (Y₃ j) (Y₄ j) f w₁ w₂ w₃ σ (ν j)) := fun j =>
    logGood_const (iterSeries_mem_subexpPS hV i₁ i₂ i₃ i₄ (hY₃ j) (hY₄ j) h₁ h₂ h₃ hf)
  set E' : LogExp := LogExp.mk (Fin r) (fun j => -ν j - 1)
    (fun j => iterPoly (Y₃ j) (Y₄ j) f w₁ w₂ w₃ σ (ν j)) hgood with hE'
  obtain ⟨E, hE⟩ := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃ hf
  have hc : ∀ μ k, E.coeff μ k = E'.coeff μ k := by
    intro μ k
    rw [← prodExpCoeff_eq _ _ _ _ _ _ _ _ hE, hco α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf μ k]
    rfl
  have ht := log_mem_overlapDomain hx0 hx1
  have hP := hE _ ht
  rw [LogExp.eval_eq_of_coeff_eq E E' hc _ (overlapDomain_subset ht)] at hP
  have hI : ∀ j, iterFun (Y₃ j) (Y₄ j) f w₁ w₂ w₃ σ (ν j) (Real.log x)
      = logFun (-ν j - 1) (iterPoly (Y₃ j) (Y₄ j) f w₁ w₂ w₃ σ (ν j)) (Real.log x) :=
    fun j => iterFun_eq_logFun _ _ _ _ _ _ _ _ (im_bounds ht).1 (im_bounds ht).2
  have hsum : E'.eval (Real.log x)
      = ∑ j, iterFun (Y₃ j) (Y₄ j) f w₁ w₂ w₃ σ (ν j) (Real.log x) := by
    simp only [LogExp.eval]
    exact Finset.sum_congr rfl fun j _ => (hI j).symm
  rw [hsum] at hP
  unfold prodFun at hP
  unfold iterFun at hP
  rw [← Complex.ofReal_exp, Real.exp_log hx0] at hP
  convert hP using 2
  push_cast; rfl

/-- **`AssociativityInput` from the coefficient identity** (strongly rational `V`). -/
theorem associativityInput_of_coeffIdentity (hV : StronglyRational W)
    (h : AssocCoeffIdentity W) : AssociativityInput W :=
  associativityInput_of_atOne (associativityAtOne_of_coeffIdentity hV h)

end VOA.Huang.AssocCoeffReduction
