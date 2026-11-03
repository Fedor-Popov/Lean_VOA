/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocCoeffRules

/-!
# Log removal from `L(0)`-semisimplicity

Fix the outside data `f ∈ P₄*` (supported at `h₄`) and `w₃ ∈ P₃(α₃)` of a product
`⟨f, 𝒴₁(w₁, 1+u) 𝒴₂(w₂, 1) w₃⟩` and regard its expansion coefficients at the iterate point
(`prodExpCoeff`, the coefficient of `u^μ (log u)^k`) as functions of the inside data
`(w₁, w₂)`, graded by the **intermediate weight** `n = μ + α₁ + α₂`:
`B_{n,k}(w₁, w₂) = c_{n − α₁ − α₂, k}(w₁, w₂)`.

The `L₋₁`-rule (`AssocCoeffRules.logCoeff_Lm1_left_holds`) says exactly that the operator
`L'(0) = (L₋₁ + L₀) ⊗ 1 + 1 ⊗ L₀` (the `L(0)` of the `P(1)`-tensor action of Huang–Lepowsky,
transposed to functionals) acts on these functions by
`(L'(0) − n) B_{n,k} = (k + 1) B_{n,k+1}`
(`L0T_coefFun`): the log-degree is the nilpotent part of `L'(0)`.  So **logs vanish as soon as
`B_{n,0}` is a finite sum of `L'(0)`-eigenvectors** (`logs_vanish`, pure linear algebra plus
the independence of exponential sequences).  That hypothesis is the named, TRUE interface
`CoeffL0Semisimple` — the output of `LogRemovalAdmissible` (the span of the coefficient
functionals is a completely reducible module of ordinary modules, on which `L'(0)` is
semisimple); it also follows from the associativity target itself (each iterate functional is an
`L'(0)`-eigenvector).

## Main results
* `exCoeff_eq_zero_of_natDegree_lt`, `LogExp.exists_coeff_bound`, `logCoeff_eventually_zero`
  (finite log-degree, pointwise).
* `eq_zero_of_sum_pow_eventually_zero` (exponential sequences with distinct nonzero bases).
* `logs_vanish` (abstract log removal).
* `HomPair`, `HomPair.lm1`, `L0T`, `coefFun`, `L0T_coefFun`, `coefFun_eventually_zero`.
* `CoeffL0Semisimple` (named, TRUE), `prodExpCoeff_log_eq_zero`: under it, every product
  among irreducible modules of a strongly rational `V` is log-free at the iterate point.

## Status
No `sorry`, no new axioms.  `CoeffL0Semisimple` is open (HL3–HL5).
-/

namespace VOA.Huang.LogRemovalCoeff

open VOA.Huang.FrobeniusLog Polynomial
open scoped BigOperators

/-! ## Finite log-degree -/

theorem exCoeff_eq_zero_of_natDegree_lt {lam : ℂ} {p : ℕ → ℂ[X]} {K : ℕ}
    (hK : ∀ n, (p n).natDegree ≤ K) (μ : ℂ) {k : ℕ} (hk : K < k) : exCoeff lam p μ k = 0 := by
  unfold exCoeff
  split_ifs
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hK _) hk)
  · rfl

theorem LogExp.exists_coeff_bound (E : LogExp) : ∃ K : ℕ, ∀ μ k, K < k → E.coeff μ k = 0 := by
  classical
  choose K hK using fun j => (E.good j).deg
  refine ⟨Finset.univ.sup K, fun μ k hk => ?_⟩
  refine Finset.sum_eq_zero fun j _ => exCoeff_eq_zero_of_natDegree_lt (hK j) μ ?_
  exact lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ j)) hk

/-- A function with a finite log-expansion has bounded log-degree. -/
theorem logCoeff_eventually_zero {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ halfPlane)
    (hne : U.Nonempty) {F : ℂ → ℂ} (hF : HasLogExp U F) :
    ∃ K : ℕ, ∀ μ k, K < k → logCoeff U F μ k = 0 := by
  obtain ⟨E, hE⟩ := hF
  obtain ⟨K, hK⟩ := E.exists_coeff_bound
  exact ⟨K, fun μ k hk => by rw [logCoeff_eq hU hsub hne hE]; exact hK μ k hk⟩

/-! ## Exponential sequences -/

/-- If `Σ_{r ∈ s} c(r) rʲ = 0` for all large `j`, then `c(r) = 0` for every nonzero `r ∈ s`. -/
theorem eq_zero_of_sum_pow_eventually_zero (s : Finset ℂ) (c : ℂ → ℂ) (J : ℕ)
    (h : ∀ j, J ≤ j → ∑ r ∈ s, c r * r ^ j = 0) : ∀ r ∈ s, r ≠ 0 → c r = 0 := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => intro r hr; simp at hr
  | insert a s ha ih =>
    have hs : ∀ j, J ≤ j → ∑ r ∈ s, c r * r ^ j = -(c a * a ^ j) := by
      intro j hj
      have := h j hj
      rw [Finset.sum_insert ha] at this
      linear_combination this
    -- eliminate `a`
    have h' : ∀ j, J ≤ j → ∑ r ∈ s, (c r * (r - a)) * r ^ j = 0 := by
      intro j hj
      have e : ∑ r ∈ s, (c r * (r - a)) * r ^ j
          = ∑ r ∈ s, c r * r ^ (j + 1) - a * ∑ r ∈ s, c r * r ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
      rw [e, hs (j + 1) (by omega), hs j hj]
      ring
    have hS : ∀ r ∈ s, r ≠ 0 → c r = 0 := by
      intro r hr hr0
      have := ih (fun r => c r * (r - a)) h' r hr hr0
      have hra : r - a ≠ 0 := sub_ne_zero.mpr fun e => ha (e ▸ hr)
      exact (mul_eq_zero.mp this).resolve_right hra
    intro r hr hr0
    rcases Finset.mem_insert.mp hr with rfl | hr
    · have h1 := hs (J + 1) (by omega)
      have h2 : ∑ r' ∈ s, c r' * r' ^ (J + 1) = 0 := by
        refine Finset.sum_eq_zero fun r' hr' => ?_
        by_cases h0 : r' = 0
        · rw [h0, zero_pow (by omega), mul_zero]
        · rw [hS r' hr' h0, zero_mul]
      rw [h2] at h1
      have : c r * r ^ (J + 1) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hr0)
    · exact hS r hr hr0

/-! ## Abstract log removal -/

/-- **Abstract log removal.**  Let `T` act on functions `H → ℂ`, and let `B₀, B₁, …` satisfy
`(T − n) B_k = (k + 1) B_{k+1}` with pointwise bounded log-degree.  If `B₀` is a finite sum of
`T`-eigenvectors, then `B_k = 0` for every `k ≥ 1`. -/
theorem logs_vanish {H : Type*} (T : (H → ℂ) →ₗ[ℂ] (H → ℂ)) (n : ℂ) (B : ℕ → H → ℂ)
    (hB : ∀ k, T (B k) = n • B k + ((k : ℂ) + 1) • B (k + 1))
    (hfin : ∀ x, ∃ K : ℕ, ∀ k, K < k → B k x = 0)
    {ι : Type*} (s : Finset ι) (e : ι → H → ℂ) (lam : ι → ℂ)
    (he : ∀ i ∈ s, T (e i) = lam i • e i) (h0 : B 0 = ∑ i ∈ s, e i) :
    ∀ k, 1 ≤ k → B k = 0 := by
  classical
  set D : (H → ℂ) →ₗ[ℂ] (H → ℂ) := T - n • LinearMap.id with hD
  have hDB : ∀ k, D (B k) = ((k : ℂ) + 1) • B (k + 1) := by
    intro k
    simp only [hD, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hB k]
    abel
  have hDe : ∀ i ∈ s, D (e i) = (lam i - n) • e i := by
    intro i hi
    simp only [hD, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, he i hi,
      sub_smul]
  have hpowB : ∀ j : ℕ, (D ^ j) (B 0) = (j.factorial : ℂ) • B j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hDB, smul_smul, Nat.factorial_succ]
      push_cast
      ring_nf
  have hpowe : ∀ j : ℕ, ∀ i ∈ s, (D ^ j) (e i) = (lam i - n) ^ j • e i := by
    intro j
    induction j with
    | zero => intro i _; simp
    | succ j ih =>
      intro i hi
      rw [pow_succ', Module.End.mul_apply, ih i hi, map_smul, hDe i hi, smul_smul, pow_succ]
  -- pointwise exponential-sum representation
  have hrep : ∀ x : H, ∀ j : ℕ, (j.factorial : ℂ) * B j x
      = ∑ r ∈ s.image (fun i => lam i - n),
          (∑ i ∈ s.filter (fun i => lam i - n = r), e i x) * r ^ j := by
    intro x j
    have := congrArg (fun F => F x) (hpowB j)
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [← this, h0, map_sum, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun i hi => by rw [hpowe j i hi]]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => lam i - n)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
    ring
  intro k hk
  funext x
  obtain ⟨K, hK⟩ := hfin x
  have hc := eq_zero_of_sum_pow_eventually_zero (s.image fun i => lam i - n)
    (fun r => ∑ i ∈ s.filter (fun i => lam i - n = r), e i x) (K + 1)
    (fun j hj => by rw [← hrep x j, hK j (by omega), mul_zero])
  have hk' := hrep x k
  have hz : ∑ r ∈ s.image (fun i => lam i - n),
      (∑ i ∈ s.filter (fun i => lam i - n = r), e i x) * r ^ k = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    by_cases h0 : r = 0
    · rw [h0, zero_pow (by omega), mul_zero]
    · have h' := hc r hr h0
      simp only at h'
      rw [h', zero_mul]
  rw [hz] at hk'
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  exact (mul_eq_zero.mp hk').resolve_left hf

end VOA.Huang.LogRemovalCoeff

namespace VOA.Huang.LogRemovalSemisimple

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Homogeneous pairs and the operator `L'(0)` -/

/-- A pair of homogeneous vectors `(w₁, w₂) ∈ P₁(α₁) × P₂(α₂)` with their weights. -/
structure HomPair (P₁ P₂ : LWModule W) where
  /-- The first vector. -/
  w₁ : P₁.carrier
  /-- Its weight. -/
  α₁ : ℂ
  /-- The second vector. -/
  w₂ : P₂.carrier
  /-- Its weight. -/
  α₂ : ℂ
  /-- Homogeneity of `w₁`. -/
  h₁ : w₁ ∈ P₁.isMod.weight α₁
  /-- Homogeneity of `w₂`. -/
  h₂ : w₂ ∈ P₂.isMod.weight α₂

theorem Lm1_mem_weight' {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    {α : ℂ} {w : M} (hw : w ∈ A.weight α) : A.Lm1 w ∈ A.weight (α + 1) := by
  have h := VOA.mode_mem_weight A W.conformalVector_mem_grading_two hw 0
  have e : α + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = α + 1 := by push_cast; ring
  rw [e] at h
  exact h

/-- `(L₋₁ w₁, w₂)`. -/
def HomPair.lm1 {P₁ P₂ : LWModule W} (x : HomPair P₁ P₂) : HomPair P₁ P₂ :=
  ⟨P₁.isMod.Lm1 x.w₁, x.α₁ + 1, x.w₂, x.α₂, Lm1_mem_weight' P₁.isMod x.h₁, x.h₂⟩

/-- **`L'(0)` on functions of homogeneous pairs**: `(L'(0) G)(w₁, w₂) = G(L₋₁w₁, w₂) +
(α₁ + α₂) G(w₁, w₂)` — the transpose of `(L₋₁ + L₀) ⊗ 1 + 1 ⊗ L₀`. -/
def L0T (P₁ P₂ : LWModule W) : (HomPair P₁ P₂ → ℂ) →ₗ[ℂ] (HomPair P₁ P₂ → ℂ) where
  toFun G x := G x.lm1 + (x.α₁ + x.α₂) * G x
  map_add' G G' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' a G := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem L0T_apply {P₁ P₂ : LWModule W} (G : HomPair P₁ P₂ → ℂ) (x : HomPair P₁ P₂) :
    L0T P₁ P₂ G x = G x.lm1 + (x.α₁ + x.α₂) * G x := rfl

/-- **The coefficient functions** `B_{n,k}(w₁, w₂) = c_{n − α₁ − α₂, k}(w₁, w₂)` (intermediate
weight `n`, log-degree `k`), for fixed outside data `f`, `w₃`. -/
noncomputable def coefFun {P₁ P₂ P₃ P₄ Q : LWModule W}
    (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier)
    (f : P₄.carrier →ₗ[ℂ] ℂ) (w₃ : P₃.carrier) (α₃ h₄ n : ℂ) (k : ℕ) :
    HomPair P₁ P₂ → ℂ :=
  fun x => prodExpCoeff Y₁ Y₂ f x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h)
    (n - x.α₁ - x.α₂) k

section Rules

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
  (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf

/-- **`(L'(0) − n) B_{n,k} = (k + 1) B_{n,k+1}`** (strongly rational `V`). -/
theorem L0T_coefFun (n : ℂ) (k : ℕ) :
    L0T P₁ P₂ (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k)
      = n • coefFun Y₁ Y₂ f w₃ α₃ h₄ n k + ((k : ℂ) + 1) • coefFun Y₁ Y₂ f w₃ α₃ h₄ n (k + 1) := by
  funext x
  rw [L0T_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coefFun, HomPair.lm1]
  have key := logCoeff_Lm1_left_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf
    (n - x.α₁ - x.α₂) k
  have e1 : x.α₁ + 1 + x.α₂ + α₃ - h₄ - 2 = x.α₁ + x.α₂ + α₃ - h₄ - 2 + 1 := by ring
  have e2 : n - (x.α₁ + 1) - x.α₂ = n - x.α₁ - x.α₂ - 1 := by ring
  rw [e1, e2, key]
  ring

/-- Pointwise bounded log-degree of the coefficient functions. -/
theorem coefFun_eventually_zero (n : ℂ) (x : HomPair P₁ P₂) :
    ∃ K : ℕ, ∀ k, K < k → coefFun Y₁ Y₂ f w₃ α₃ h₄ n k x = 0 := by
  obtain ⟨K, hK⟩ := logCoeff_eventually_zero isOpen_overlapDomain overlapDomain_subset
    overlapDomain_nonempty (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf)
  exact ⟨K, fun k hk => hK _ k hk⟩

end Rules

/-! ## The semisimplicity interface and log removal -/

/-- **`L'(0)` is semisimple on the coefficient functions** (named; TRUE for strongly rational
`W`).  For irreducible modules, every product, every outside datum `(f, w₃)` and every
intermediate weight `n`, the log-free coefficient function `B_{n,0}` is a finite sum of
`L'(0)`-eigenvectors.  Source: Huang–Lepowsky IV + Huang 2005 §3 (the span of the coefficient
functionals is a generalized module, completely reducible into ordinary modules by rationality,
on which `L'(0)` is semisimple); equivalently a consequence of associativity, each iterate
coefficient functional being an `L'(0)`-eigenvector of eigenvalue `n`.  Open: stages HL3–HL5. -/
def CoeffL0Semisimple (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∀ (α₃ h₄ : ℂ) (w₃ : P₃.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ),
    w₃ ∈ P₃.isMod.weight α₃ → SupportedAt P₄.isMod f h₄ →
  ∀ n : ℂ, ∃ (s : Finset ℕ) (e : ℕ → HomPair P₁ P₂ → ℂ) (lam : ℕ → ℂ),
    (∀ i ∈ s, L0T P₁ P₂ (e i) = lam i • e i) ∧
    coefFun Y₁ Y₂ f w₃ α₃ h₄ n 0 = ∑ i ∈ s, e i

/-- **Log removal** (strongly rational `V`, conditional on `CoeffL0Semisimple` only): every
product among irreducible modules has no `log u` terms at the iterate point. -/
theorem prodExpCoeff_log_eq_zero (hV : StronglyRational W) (hS : CoeffL0Semisimple W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) (μ : ℂ) {k : ℕ}
    (hk : 1 ≤ k) :
    prodExpCoeff Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) μ k = 0 := by
  obtain ⟨s, e, lam, he, h0⟩ :=
    hS P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf (μ + α₁ + α₂)
  have hz := logs_vanish (L0T P₁ P₂) (μ + α₁ + α₂)
    (fun k => coefFun Y₁ Y₂ f w₃ α₃ h₄ (μ + α₁ + α₂) k)
    (L0T_coefFun hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf _)
    (coefFun_eventually_zero hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf _) s e lam he h0 k hk
  have := congrArg (fun F => F ⟨w₁, α₁, w₂, α₂, h₁, h₂⟩) hz
  simp only [coefFun, Pi.zero_apply] at this
  rw [show μ + α₁ + α₂ - α₁ - α₂ = μ by ring] at this
  exact this

/-! ## Sanity: the interface follows from the associativity target -/

section FromTarget

variable {P₁ P₂ P₃ P₄ Q : LWModule W}

/-- The iterate coefficient at intermediate weight `n = h + m` is
`⟨f, 𝒴₃((w₁)_{α₁+α₂−1−n} w₂)_{α₃−h₄−1+n} w₃⟩`. -/
theorem iterExpCoeff_at (Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier)
    (Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier) (α₁ α₂ α₃ h₄ h n : ℂ) (m : ℕ)
    (hm : h + m = n) :
    iterExpCoeff Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - h) (n - α₁ - α₂) 0
      = f (Y₃ (α₃ - h₄ - 1 + n) (Y₄ (α₁ + α₂ - 1 - n) w₁ w₂) w₃) := by
  rw [show n - α₁ - α₂ = -(α₁ + α₂ - 1 - h) - 1 + m by rw [← hm]; ring, iterExpCoeff_eq,
    if_pos rfl, iterCoeff,
    show α₁ + α₂ - 1 - h - m = α₁ + α₂ - 1 - n by rw [← hm]; ring,
    show α₁ + α₂ + α₃ - h₄ - 2 - (α₁ + α₂ - 1 - h) + m = α₃ - h₄ - 1 + n by rw [← hm]; ring]

theorem iterExpCoeff_off (Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier)
    (Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier) (α₁ α₂ α₃ h₄ h n : ℂ)
    (hm : ∀ m : ℕ, h + m ≠ n) :
    iterExpCoeff Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - h) (n - α₁ - α₂) 0
      = 0 :=
  iterExpCoeff_eq_zero _ _ _ _ _ _ _ _ _ (fun m hm' => hm m (by linear_combination hm')) 0

/-- The iterate coefficient function at intermediate weight `n`. -/
noncomputable def iterFunAt (Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier)
    (Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ)
    (w₃ : P₃.carrier) (α₃ h₄ n : ℂ) : HomPair P₁ P₂ → ℂ :=
  fun x => iterExpCoeff Y₃ Y₄ f x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2)
    (x.α₁ + x.α₂ - 1 - Q.h) (n - x.α₁ - x.α₂) 0

/-- **Each iterate coefficient function is an `L'(0)`-eigenvector of eigenvalue `n`** (the
`L₋₁`-derivative property of the inner intertwiner). -/
theorem L0T_iterFunAt (Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier)
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier}
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod Q.isMod Y₄) (f : P₄.carrier →ₗ[ℂ] ℂ)
    (w₃ : P₃.carrier) (α₃ h₄ n : ℂ) :
    L0T P₁ P₂ (iterFunAt Y₃ Y₄ f w₃ α₃ h₄ n) = n • iterFunAt Y₃ Y₄ f w₃ α₃ h₄ n := by
  funext x
  rw [L0T_apply]
  simp only [Pi.smul_apply, smul_eq_mul, iterFunAt, HomPair.lm1]
  by_cases hm : ∃ m : ℕ, Q.h + m = n
  · obtain ⟨m, hm⟩ := hm
    rw [iterExpCoeff_at _ _ _ _ _ _ _ _ _ _ _ _ m hm,
      show x.α₁ + 1 + x.α₂ - 1 - n = (x.α₁ + x.α₂ - n) by ring, hY₄.L_neg_one,
      iterExpCoeff_at _ _ _ _ _ _ _ _ _ _ _ _ m hm,
      show x.α₁ + x.α₂ - n - 1 = x.α₁ + x.α₂ - 1 - n by ring]
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    ring
  · push Not at hm
    rw [iterExpCoeff_off _ _ _ _ _ _ _ _ _ _ _ _ hm, iterExpCoeff_off _ _ _ _ _ _ _ _ _ _ _ _ hm]
    ring

end FromTarget

/-- **Sanity check: `CoeffL0Semisimple` follows from the coefficient form of associativity**
(so it is implied by — hence consistent with — Huang's theorem; it is not an extra assumption
beyond the target). -/
theorem coeffL0Semisimple_of_assocCoeffIdentity (h : AssocCoeffIdentity W) :
    CoeffL0Semisimple W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n
  obtain ⟨r, Qs, _, Y₃, Y₄, _, hY₄, hco⟩ := h P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  classical
  refine ⟨Finset.range r,
    fun i => if hi : i < r then iterFunAt (Y₃ ⟨i, hi⟩) (Y₄ ⟨i, hi⟩) f w₃ α₃ h₄ n else 0,
    fun _ => n, fun i _ => ?_, ?_⟩
  · by_cases hi : i < r
    · simp only [dif_pos hi]
      exact L0T_iterFunAt _ (hY₄ ⟨i, hi⟩) f w₃ α₃ h₄ n
    · simp only [dif_neg hi, map_zero, smul_zero]
  · funext x
    rw [Finset.sum_apply, Finset.sum_range]
    simp only [Fin.is_lt, dif_pos, Fin.eta]
    exact hco _ _ _ _ x.w₁ x.w₂ w₃ f x.h₁ x.h₂ h₃ hf _ 0

/-! ## Splitting the target: (i) log removal + (ii) log-free coefficients are iterates -/

/-- Iterates are log-free: their `(log u)^k` coefficients vanish for `k ≥ 1`. -/
theorem iterExpCoeff_log_eq_zero {M₁ M₂ M₃ M₄ M₅ : Type u}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
    [AddCommGroup M₅] [Module ℂ M₅] (Y₃ : IntertwiningModes M₅ M₃ M₄)
    (Y₄ : IntertwiningModes M₁ M₂ M₅) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (σ ν₀ μ : ℂ) {k : ℕ} (hk : 1 ≤ k) : iterExpCoeff Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ μ k = 0 := by
  unfold iterExpCoeff exCoeff iterPoly
  split_ifs
  · rw [Polynomial.coeff_C, if_neg (by omega)]
  · rfl

/-- **Part (ii) of the associativity target**: the *log-free* coefficients of every product are
those of
a finite sum of iterates (named; TRUE for strongly rational `W`: Huang 2005 Thm 3.5 + HL IV;
the `k = 0` part of `AssocCoeffIdentity`). -/
def AssocCoeffIdentityZero (W : VertexOperatorAlgebra 𝒱) : Prop :=
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
    ∀ μ : ℂ,
      prodExpCoeff Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) μ 0
        = ∑ j, iterExpCoeff (Y₃ j) (Y₄ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) μ 0

/-- **The split**: (i) `CoeffL0Semisimple` (log removal) + (ii) `AssocCoeffIdentityZero`
give the full coefficient identity. -/
theorem assocCoeffIdentity_of_split (hV : StronglyRational W) (hS : CoeffL0Semisimple W)
    (hZ : AssocCoeffIdentityZero W) : AssocCoeffIdentity W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, hco⟩ := hZ P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  refine ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf μ k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hco α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf μ
  · rw [prodExpCoeff_log_eq_zero hV hS i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃ hf μ hk]
    exact (Finset.sum_eq_zero fun j _ => iterExpCoeff_log_eq_zero _ _ _ _ _ _ _ _ _ hk).symm

/-- **`AssociativityInput` from the two named halves** (strongly rational `V`). -/
theorem associativityInput_of_split (hV : StronglyRational W) (hS : CoeffL0Semisimple W)
    (hZ : AssocCoeffIdentityZero W) : AssociativityInput W :=
  associativityInput_of_coeffIdentity hV (assocCoeffIdentity_of_split hV hS hZ)

/-- Conversely the coefficient identity gives both halves (so the split loses nothing). -/
theorem split_of_assocCoeffIdentity (h : AssocCoeffIdentity W) :
    CoeffL0Semisimple W ∧ AssocCoeffIdentityZero W := by
  refine ⟨coeffL0Semisimple_of_assocCoeffIdentity h, ?_⟩
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, hco⟩ := h P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  exact ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, fun α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf μ =>
    hco α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf μ 0⟩

end VOA.Huang.LogRemovalSemisimple
