/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ConvergenceBridge
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The growth bound: PBW spanning data ⟹ subexponential graded dimensions

`ConvergenceBridge` consumes the growth datum `SubexponentialCoeffs N h`.  This file proves it
from the combinatorial content of the ordered (PBW) spanning set of Zhu / Dong–Li–Mason / Buhl:

* if `M` is spanned by a family of homogeneous vectors indexed by **colored partitions** — pairs
  `(μ, j)` with `μ : Fin g × ℕ →₀ ℕ` a multiplicity function (`μ(i, m)` = how often the
  generator `sᵢ` is applied in mode `−(m+1)`) and `j` a bottom vector — each of weight
  `h + botWt j + Σ μ(i,m)·(wt sᵢ + m)` (`PBWSpanningData`),
* then `dim M_{h+n} ≤ b · pcountLe g n`, where `pcountLe g n` counts multiplicity functions of
  size `Σ μ(i,m)(m+1) ≤ n` (`finrank_weight_le_of_pbw`),
* and `pcountLe g n ≤ exp(g·t/(1−t)²)·t^{−n}` for every `t ∈ (0,1)` — the generating-function
  bound `Σ_μ t^{|μ|} = Π_k (1−t^k)^{−g}` — so `pcountLe g` is **subexponential**
  (`pcountLe_subexponential`).

Hence `subexponentialCoeffs_of_pbw : PBWSpanningData N h → SubexponentialCoeffs N h`.

## What is and is not here
The **counting** half of the growth theorem is proved in full.  The **spanning** half — that a
`C₂`-cofinite VOA supplies `PBWSpanningData` for every irreducible module (Buhl's ordered spanning
set `x¹_{−n₁}⋯x^k_{−n_k}w`, `n₁ ≥ ⋯ ≥ n_k`, over lifts of a basis of `𝒱/C₂(𝒱)`) — is the named
datum `PBWSpanningData` here (supplied downstream, see Status); the repo's `iterProdSpan_eq_top` (5.3.11a) is the unordered, VOA-level
half of it.

## Status
Proved, axiom-clean, `pbw`-free.  The spanning half is supplied downstream in
`Modularity/BuhlSpanningC2.lean`: unconditionally for the adjoint module
(`orderedSpanningData_adjoint_of_C2Cofinite`, `subexponentialCoeffs_adjoint_of_C2Cofinite`), and for
modules under an explicit finite lowest-weight generation hypothesis
(`orderedSpanningData_of_C2Cofinite`, `subexponentialCoeffs_of_C2Cofinite`).  The general
`C2Cofinite W → BuhlSpanning W` (all modules with a conformal weight) is not proved.
-/

namespace VOA

open scoped BigOperators

/-! ## Subexponential growth from a uniform bound `a n · tⁿ ≤ K` -/

/-- If `a n · tⁿ ≤ K t` for every `t ∈ (0,1)`, then `a` is subexponential. -/
theorem Subexponential.of_mul_pow_le {a : ℕ → ℝ} (K : ℝ → ℝ)
    (h : ∀ t : ℝ, 0 < t → t < 1 → ∀ n, a n * t ^ n ≤ K t) : Subexponential a := by
  intro r hr
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  refine ⟨K r⁻¹, fun n => ?_⟩
  have ht0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have ht1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have := h r⁻¹ ht0 ht1 n
  have hpow : (r⁻¹) ^ n * r ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr0.ne', one_pow]
  calc a n = a n * (r⁻¹) ^ n * r ^ n := by rw [mul_assoc, hpow, mul_one]
    _ ≤ K r⁻¹ * r ^ n := mul_le_mul_of_nonneg_right this (pow_nonneg hr0.le n)

/-! ## Colored multiplicity functions and their count -/

/-- Multiplicity functions on `Fin g × Fin n` (generator, mode `m+1`) with values `≤ n` and total
size `Σ μ(p)·(p.2+1) ≤ n`. -/
def partMultsLe (g n : ℕ) : Finset (Fin g × Fin n → Fin (n + 1)) :=
  Finset.univ.filter (fun μ => ∑ p, (μ p : ℕ) * (p.2 + 1) ≤ n)

/-- The number of `g`-colored multiplicity functions of size `≤ n`. -/
def pcountLe (g n : ℕ) : ℕ := (partMultsLe g n).card

/-- `1/(1−x) ≤ exp(x/(1−x))` for `0 ≤ x < 1`. -/
theorem inv_one_sub_le_exp {x : ℝ} (hx1 : x < 1) :
    (1 - x)⁻¹ ≤ Real.exp (x / (1 - x)) := by
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have h := Real.add_one_le_exp (x / (1 - x))
  have heq : x / (1 - x) + 1 = (1 - x)⁻¹ := by field_simp; ring
  rw [heq] at h
  exact h

/-- **The generating-function bound**:
`pcountLe g n · tⁿ ≤ exp(g·t/(1−t)²)` for every `t ∈ (0,1)`.

`Σ_{μ} t^{|μ|} = Π_{p} Σ_{j ≤ n} t^{j(p.2+1)} ≤ Π_{k=1}^{n} (1−t^k)^{−g} ≤ exp(g Σ_k t^k/(1−t^k))`. -/
theorem pcountLe_mul_pow_le (g n : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (pcountLe g n : ℝ) * t ^ n ≤ Real.exp (g * (t / (1 - t) ^ 2)) := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  -- Step 1: `pcountLe·tⁿ ≤ Σ_μ t^{|μ|}` over all `μ`
  have hstep1 : (pcountLe g n : ℝ) * t ^ n
      ≤ ∑ μ : Fin g × Fin n → Fin (n + 1), t ^ (∑ p, (μ p : ℕ) * (p.2 + 1)) := by
    rw [pcountLe, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum (fun μ hμ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => pow_nonneg ht0.le _))
    rw [partMultsLe, Finset.mem_filter] at hμ
    rw [Nat.cast_one, one_mul]
    exact pow_le_pow_of_le_one ht0.le ht1.le hμ.2
  -- Step 2: `Σ_μ t^{|μ|} = Π_p Σ_j t^{j(p.2+1)}`
  have hstep2 : (∑ μ : Fin g × Fin n → Fin (n + 1), t ^ (∑ p, (μ p : ℕ) * (p.2 + 1)))
      = ∏ p : Fin g × Fin n, ∑ j : Fin (n + 1), (t ^ (p.2 + 1 : ℕ)) ^ (j : ℕ) := by
    rw [Finset.prod_univ_sum (fun _ : Fin g × Fin n => (Finset.univ : Finset (Fin (n + 1))))
      (fun (p : Fin g × Fin n) (j : Fin (n + 1)) => (t ^ (p.2 + 1 : ℕ)) ^ (j : ℕ)),
      Fintype.piFinset_univ]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [← pow_mul, mul_comm]
  -- Step 3: each factor `≤ (1 − t^{p.2+1})⁻¹`
  have hstep3 : (∏ p : Fin g × Fin n, ∑ j : Fin (n + 1), (t ^ (p.2 + 1 : ℕ)) ^ (j : ℕ))
      ≤ ∏ p : Fin g × Fin n, (1 - t ^ (p.2 + 1 : ℕ))⁻¹ := by
    refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun j _ => by positivity))
      (fun p _ => ?_)
    have hx0 : 0 ≤ t ^ (p.2 + 1 : ℕ) := by positivity
    have hx1 : t ^ (p.2 + 1 : ℕ) < 1 := pow_lt_one₀ ht0.le ht1 (Nat.succ_ne_zero _)
    rw [Fin.sum_univ_eq_sum_range (fun j => (t ^ (p.2 + 1 : ℕ)) ^ j) (n + 1),
      Finset.range_eq_Ico]
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n + 1) hx0 hx1
    rw [pow_zero, one_div] at this
    exact this
  -- Step 4: `Π_p (1 − t^{p.2+1})⁻¹ = Π_k ((1 − t^{k+1})⁻¹)^g ≤ exp(g Σ_k t^{k+1}/(1−t^{k+1}))`
  have hstep4 : (∏ p : Fin g × Fin n, (1 - t ^ (p.2 + 1 : ℕ))⁻¹)
      ≤ Real.exp (g * ∑ k : Fin n, t ^ (k + 1 : ℕ) / (1 - t ^ (k + 1 : ℕ))) := by
    rw [Fintype.prod_prod_type_right, Finset.mul_sum, Real.exp_sum]
    dsimp only
    refine Finset.prod_le_prod (fun k _ => Finset.prod_nonneg (fun _ _ => ?_)) (fun k _ => ?_)
    · exact inv_nonneg.mpr (sub_pos.mpr (pow_lt_one₀ ht0.le ht1 (Nat.succ_ne_zero _))).le
    · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
      have hx1 : t ^ (k + 1 : ℕ) < 1 := pow_lt_one₀ ht0.le ht1 (Nat.succ_ne_zero _)
      exact pow_le_pow_left₀ (inv_nonneg.mpr (sub_pos.mpr hx1).le)
        (inv_one_sub_le_exp hx1) g
  -- Step 5: `Σ_k t^{k+1}/(1−t^{k+1}) ≤ t/(1−t)²`
  have hstep5 : (∑ k : Fin n, t ^ (k + 1 : ℕ) / (1 - t ^ (k + 1 : ℕ))) ≤ t / (1 - t) ^ 2 := by
    have hle : ∀ k : Fin n, t ^ (k + 1 : ℕ) / (1 - t ^ (k + 1 : ℕ)) ≤ t ^ (k + 1 : ℕ) / (1 - t) := by
      intro k
      have hx1 : t ^ (k + 1 : ℕ) < 1 := pow_lt_one₀ ht0.le ht1 (Nat.succ_ne_zero _)
      refine div_le_div_of_nonneg_left (by positivity) h1t ?_
      have : t ^ (k + 1 : ℕ) ≤ t := by
        calc t ^ (k + 1 : ℕ) = t ^ (k : ℕ) * t := pow_succ _ _
          _ ≤ 1 * t := mul_le_mul_of_nonneg_right (pow_le_one₀ ht0.le ht1.le) ht0.le
          _ = t := one_mul t
      linarith
    refine le_trans (Finset.sum_le_sum (fun k _ => hle k)) ?_
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k => t ^ (k + 1)) n]
    have hgeom : (∑ k ∈ Finset.range n, t ^ (k + 1)) ≤ t / (1 - t) := by
      have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1) ht0.le ht1
      rw [pow_one] at h
      refine le_trans (le_of_eq ?_) h
      rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun i => t ^ i) 0 n 1]
    rw [div_le_div_iff₀ h1t (by positivity)]
    have := mul_le_mul_of_nonneg_right hgeom h1t.le
    rw [div_mul_cancel₀ _ h1t.ne'] at this
    nlinarith [this]
  calc (pcountLe g n : ℝ) * t ^ n ≤ _ := hstep1
    _ = _ := hstep2
    _ ≤ _ := hstep3
    _ ≤ _ := hstep4
    _ ≤ Real.exp (g * (t / (1 - t) ^ 2)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hstep5 (Nat.cast_nonneg g))

/-- **Colored multiplicity counts are subexponential.** -/
theorem pcountLe_subexponential (g : ℕ) : Subexponential (fun n => (pcountLe g n : ℝ)) :=
  Subexponential.of_mul_pow_le (fun t => Real.exp (g * (t / (1 - t) ^ 2)))
    (fun _ ht0 ht1 n => pcountLe_mul_pow_le g n ht0 ht1)

/-! ## Multiplicity functions as finitely supported maps -/

/-- The size `|μ| = Σ μ(i,m)·(m+1)` of a multiplicity function (the total mode depth). -/
def multSize {g : ℕ} (μ : Fin g × ℕ →₀ ℕ) : ℕ := μ.sum (fun p m => m * (p.2 + 1))

/-- The weighted degree `Σ μ(i,m)·(wt sᵢ + m)` of a multiplicity function. -/
def multWDeg {g : ℕ} (wt : Fin g → ℕ) (μ : Fin g × ℕ →₀ ℕ) : ℕ :=
  μ.sum (fun p m => m * (wt p.1 + p.2))

theorem multSize_le_multWDeg {g : ℕ} (wt : Fin g → ℕ) (hwt : ∀ i, 1 ≤ wt i)
    (μ : Fin g × ℕ →₀ ℕ) : multSize μ ≤ multWDeg wt μ := by
  rw [multSize, multWDeg, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_le_sum (fun p _ => Nat.mul_le_mul_left _ ?_)
  have := hwt p.1
  omega

/-- A single multiplicity is at most the size, and a positive multiplicity forces its mode
below the size. -/
theorem multSize_apply_le {g : ℕ} (μ : Fin g × ℕ →₀ ℕ) (i : Fin g) (m : ℕ) :
    μ (i, m) * (m + 1) ≤ multSize μ := by
  rw [multSize, Finsupp.sum]
  by_cases hp : (i, m) ∈ μ.support
  · exact Finset.single_le_sum (f := fun q : Fin g × ℕ => μ q * (q.2 + 1))
      (fun q _ => Nat.zero_le _) hp
  · rw [Finsupp.notMem_support_iff.mp hp, zero_mul]
    exact Nat.zero_le _

/-- Restriction of a multiplicity function to the box `Fin g × Fin n`, values clipped at `n`. -/
def multRestrict {g : ℕ} (n : ℕ) (μ : Fin g × ℕ →₀ ℕ) : Fin g × Fin n → Fin (n + 1) :=
  fun p => ⟨min (μ (p.1, p.2)) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Restriction is injective on multiplicity functions of size `≤ n`. -/
theorem multRestrict_injOn {g n : ℕ} {μ ν : Fin g × ℕ →₀ ℕ}
    (hμ : multSize μ ≤ n) (hν : multSize ν ≤ n) (h : multRestrict n μ = multRestrict n ν) :
    μ = ν := by
  refine Finsupp.ext (fun p => ?_)
  rcases p with ⟨i, m⟩
  by_cases hm : m < n
  · have := congrFun h (i, ⟨m, hm⟩)
    simp only [multRestrict, Fin.mk.injEq] at this
    have h1 : μ (i, m) ≤ n := le_trans (le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos m))
      (multSize_apply_le μ i m)) hμ
    have h2 : ν (i, m) ≤ n := le_trans (le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos m))
      (multSize_apply_le ν i m)) hν
    rwa [min_eq_left h1, min_eq_left h2] at this
  · push_neg at hm
    have h1 : μ (i, m) = 0 := by
      by_contra hc
      have := multSize_apply_le μ i m
      have : 1 * (m + 1) ≤ μ (i, m) * (m + 1) := Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hc)
      omega
    have h2 : ν (i, m) = 0 := by
      by_contra hc
      have := multSize_apply_le ν i m
      have : 1 * (m + 1) ≤ ν (i, m) * (m + 1) := Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hc)
      omega
    rw [h1, h2]

/-- The restriction of a multiplicity function of size `≤ n` lands in `partMultsLe g n`. -/
theorem multRestrict_mem {g n : ℕ} {μ : Fin g × ℕ →₀ ℕ} (hμ : multSize μ ≤ n) :
    multRestrict n μ ∈ partMultsLe g n := by
  rw [partMultsLe, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  refine le_trans ?_ hμ
  rw [multSize, Finsupp.sum]
  -- the box sum is a sub-sum of the support sum
  have hsub : ∀ p : Fin g × Fin n, ((multRestrict n μ p : ℕ)) * (p.2 + 1)
      = μ (p.1, (p.2 : ℕ)) * ((p.1, (p.2 : ℕ)).2 + 1) := by
    intro p
    simp only [multRestrict]
    have h1 : μ (p.1, (p.2 : ℕ)) ≤ n := le_trans (le_trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (multSize_apply_le μ p.1 (p.2 : ℕ))) hμ
    rw [min_eq_left h1]
  simp_rw [hsub]
  have hinj : Function.Injective (fun p : Fin g × Fin n => (p.1, (p.2 : ℕ))) := by
    intro a b h
    simp only [Prod.mk.injEq, Fin.val_inj] at h
    exact Prod.ext h.1 h.2
  rw [← Finset.sum_image (f := fun q : Fin g × ℕ => μ q * (q.2 + 1)) (fun a _ b _ h => hinj h)]
  refine Finset.sum_le_sum_of_ne_zero (fun q hq hne => ?_)
  rw [Finsupp.mem_support_iff]
  intro h0
  rw [h0, zero_mul] at hne
  exact hne rfl

/-! ## The PBW spanning datum -/

section Module
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **PBW (ordered) spanning data** for a module `N` of lowest weight `h`: a finite family of
generators `sᵢ ∈ 𝒱_{wt i}` (`wt i ≥ 1`), a finite family of bottom vectors `bot j ∈ M_{h+botWt j}`,
and a family of vectors `mono μ j` indexed by colored multiplicity functions `μ : Fin g × ℕ →₀ ℕ`
— the ordered monomial `Π_{(i,m)} (sᵢ)_{(−m−1)}^{μ(i,m)} · bot j` — homogeneous of weight
`h + botWt j + Σ μ(i,m)(wt i + m)`, which together **span** `M`.

This is precisely the combinatorial output of Buhl's ordered spanning set for modules of a
`C₂`-cofinite VOA (the ordered analogue of the repo's `iterProdSpan_eq_top`); it is carried here
as data, and the counting half of the growth theorem is proved from it. -/
structure PBWSpanningData (N : OrdVModule W M) (h : ℂ) where
  g : ℕ
  wt : Fin g → ℕ
  wt_pos : ∀ i, 1 ≤ wt i
  b : ℕ
  botWt : Fin b → ℕ
  mono : (Fin g × ℕ →₀ ℕ) → Fin b → M
  mono_mem : ∀ μ j, mono μ j ∈ N.weight (h + (botWt j : ℂ) + (multWDeg wt μ : ℂ))
  spans : (⊤ : Submodule ℂ M) = Submodule.span ℂ {x | ∃ μ j, x = mono μ j}

/-- The projection onto `M_β` kills `M_α` for `β ≠ α`. -/
theorem internalProjTo_eq_zero_of_ne' (N : OrdVModule W M) {α β : ℂ} {x : M}
    (hx : x ∈ N.weight α) (hβ : β ≠ α) : internalProjTo N.isInternal β x = 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  apply Subtype.ext
  have hdec := DirectSum.decompose_of_mem_ne N.weight hx (Ne.symm hβ)
  show ((DirectSum.component ℂ ℂ (fun j => N.weight j) β)
      (DirectSum.decomposeLinearEquiv N.weight x) : N.weight β) = ((0 : N.weight β) : M)
  rw [show (DirectSum.decomposeLinearEquiv N.weight x)
      = DirectSum.decompose N.weight x from rfl, ← DirectSum.apply_eq_component, hdec]
  rfl

/-- Graded spanning: if `M` is spanned by homogeneous vectors, each weight space is spanned by
those of that weight. -/
theorem weight_le_span_inter (N : OrdVModule W M) (F : Set M)
    (hF : ∀ f ∈ F, ∃ β : ℂ, f ∈ N.weight β) (hspan : (⊤ : Submodule ℂ M) = Submodule.span ℂ F)
    (α : ℂ) : N.weight α ≤ Submodule.span ℂ (F ∩ N.weight α) := by
  intro x hx
  have hproj : x = (internalProjTo N.isInternal α x : M) := by
    rw [show x = ((⟨x, hx⟩ : N.weight α) : M) from rfl, internalProjTo_coe]
  have hxtop : x ∈ Submodule.span ℂ F := by rw [← hspan]; exact Submodule.mem_top
  have hmap : (internalProjTo N.isInternal α x : M)
      ∈ Submodule.map ((N.weight α).subtype.comp (internalProjTo N.isInternal α))
        (Submodule.span ℂ F) := ⟨x, hxtop, rfl⟩
  rw [Submodule.map_span] at hmap
  rw [hproj]
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨β, hβ⟩ := hF f hf
  by_cases hβα : β = α
  · subst hβα
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [show f = ((⟨f, hβ⟩ : N.weight β) : M) from rfl, internalProjTo_coe]
    exact Submodule.subset_span ⟨hf, hβ⟩
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [internalProjTo_eq_zero_of_ne' N hβ (Ne.symm hβα), Submodule.coe_zero]
    exact (Submodule.span ℂ _).zero_mem

/-- A vector lying in two distinct weight spaces is zero. -/
theorem eq_zero_of_mem_weight_ne (N : OrdVModule W M) {α β : ℂ} {x : M} (hα : x ∈ N.weight α)
    (hβ : x ∈ N.weight β) (hne : β ≠ α) : x = 0 := by
  have h1 : (internalProjTo N.isInternal α x : M) = x := by
    rw [show x = ((⟨x, hα⟩ : N.weight α) : M) from rfl, internalProjTo_coe]
  have h2 : internalProjTo N.isInternal α x = 0 := internalProjTo_eq_zero_of_ne' N hβ (Ne.symm hne)
  rw [← h1, h2, Submodule.coe_zero]

/-- The inverse of restriction: a box function extended by zero to a finitely supported map. -/
noncomputable def multUnrestrict {g : ℕ} (n : ℕ) (μ : Fin g × Fin n → Fin (n + 1)) :
    Fin g × ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.univ.image (fun p : Fin g × Fin n => (p.1, (p.2 : ℕ))))
    (fun q => if hq : q.2 < n then (μ (q.1, ⟨q.2, hq⟩) : ℕ) else 0)
    (fun q hq => by
      by_cases h : q.2 < n
      · exact Finset.mem_image.mpr ⟨(q.1, ⟨q.2, h⟩), Finset.mem_univ _, rfl⟩
      · exact absurd (dif_neg h) hq)

theorem multUnrestrict_multRestrict {g n : ℕ} {μ : Fin g × ℕ →₀ ℕ} (hμ : multSize μ ≤ n) :
    multUnrestrict n (multRestrict n μ) = μ := by
  refine Finsupp.ext (fun q => ?_)
  rw [multUnrestrict, Finsupp.onFinset_apply]
  by_cases hq : q.2 < n
  · rw [dif_pos hq]
    simp only [multRestrict]
    have h1 : μ (q.1, q.2) ≤ n := le_trans (le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      (multSize_apply_le μ q.1 q.2)) hμ
    rw [min_eq_left h1]
  · rw [dif_neg hq]
    push_neg at hq
    by_contra hc
    have := multSize_apply_le μ q.1 q.2
    have : 1 * (q.2 + 1) ≤ μ (q.1, q.2) * (q.2 + 1) :=
      Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero (Ne.symm hc))
    omega

/-- **The dimension bound**: `dim M_{h+n} ≤ b · pcountLe g n` from PBW spanning data. -/
theorem finrank_weight_le_of_pbw (N : OrdVModule W M) (h : ℂ) (d : PBWSpanningData N h) (n : ℕ) :
    Module.finrank ℂ (N.weight (h + n)) ≤ d.b * pcountLe d.g n := by
  classical
  set T : Finset M := ((partMultsLe d.g n) ×ˢ (Finset.univ : Finset (Fin d.b))).image
    (fun q => d.mono (multUnrestrict n q.1) q.2) with hT
  have hle : N.weight (h + n) ≤ Submodule.span ℂ (T : Set M) := by
    refine le_trans (weight_le_span_inter N {x | ∃ μ j, x = d.mono μ j} ?_ d.spans (h + n)) ?_
    · rintro _ ⟨μ, j, rfl⟩; exact ⟨_, d.mono_mem μ j⟩
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨μ, j, rfl⟩, hmem⟩
      by_cases hw : (h + (d.botWt j : ℂ) + (multWDeg d.wt μ : ℂ)) = h + n
      · have hnat : d.botWt j + multWDeg d.wt μ = n := by
          have : ((d.botWt j + multWDeg d.wt μ : ℕ) : ℂ) = (n : ℂ) := by
            push_cast; linear_combination hw
          exact_mod_cast this
        have hsize : multSize μ ≤ n := by
          have := multSize_le_multWDeg d.wt d.wt_pos μ
          omega
        refine Submodule.subset_span ?_
        rw [hT, Finset.coe_image]
        refine ⟨(multRestrict n μ, j), ?_, ?_⟩
        · rw [Finset.coe_product]
          exact ⟨multRestrict_mem hsize, Finset.mem_univ _⟩
        · simp only
          rw [multUnrestrict_multRestrict hsize]
      · have h0 : d.mono μ j = 0 := eq_zero_of_mem_weight_ne N hmem (d.mono_mem μ j) hw
        rw [h0]
        exact (Submodule.span ℂ _).zero_mem
  haveI : Module.Finite ℂ (Submodule.span ℂ (T : Set M)) :=
    Module.Finite.span_of_finite ℂ T.finite_toSet
  calc Module.finrank ℂ (N.weight (h + n))
      ≤ Module.finrank ℂ (Submodule.span ℂ (T : Set M)) := Submodule.finrank_mono hle
    _ ≤ T.card := finrank_span_finset_le_card T
    _ ≤ ((partMultsLe d.g n) ×ˢ (Finset.univ : Finset (Fin d.b))).card := Finset.card_image_le
    _ = d.b * pcountLe d.g n := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, pcountLe, mul_comm]

/-- **PBW spanning data ⟹ subexponential graded dimensions**: the growth datum consumed
by `ConvergenceBridge` follows from the ordered spanning set. -/
theorem subexponentialCoeffs_of_pbw (N : OrdVModule W M) (h : ℂ) (d : PBWSpanningData N h) :
    SubexponentialCoeffs N (h - W.centralCharge / 24) := by
  rw [SubexponentialCoeffs]
  have hsub : Subexponential (fun n => (d.b : ℝ) * (pcountLe d.g n : ℝ)) :=
    (pcountLe_subexponential d.g).const_mul (Nat.cast_nonneg d.b)
  refine Subexponential.of_le (fun n => ?_) hsub
  rw [gradedDim, show h - W.centralCharge / 24 + (n : ℂ) + W.centralCharge / 24 = h + n from by ring,
    Complex.norm_natCast]
  have := finrank_weight_le_of_pbw N h d n
  calc (Module.finrank ℂ (N.weight (h + n)) : ℝ) ≤ ((d.b * pcountLe d.g n : ℕ) : ℝ) := by
        exact_mod_cast this
    _ = (d.b : ℝ) * (pcountLe d.g n : ℝ) := by push_cast; ring

/-! ## The concrete ordered monomials, and Buhl's theorem as a named datum -/

/-- The iterate `(sᵢ)_{(−m−1)}^{k}` raises the weight by `k·(wt sᵢ + m)`. -/
theorem mode_neg_iterate_mem_weight (N : OrdVModule W M) {β : ℤ} {s : 𝒱} (hs : s ∈ W.grading β)
    (m k : ℕ) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    ((⇑(mode (N.YM s) (-(m : ℤ) - 1)))^[k]) x ∈ N.weight (α + (k * (β + m) : ℤ)) := by
  induction k generalizing x α with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := mode_mem_weight N hs (ih hx) (-(m : ℤ) - 1)
      convert h using 2
      push_cast
      ring

/-- **The ordered monomial** `Π_{(i,m)} (sᵢ)_{(−m−1)}^{μ(i,m)} · u`, factors taken in increasing
lexicographic order of `(i, m)` from the outside in (the smallest pair acts last). -/
noncomputable def orderedMonomial (N : OrdVModule W M) {g : ℕ} (s : Fin g → 𝒱)
    (μ : Fin g × ℕ →₀ ℕ) (u : M) : M :=
  ((μ.support.map toLex.toEmbedding).sort (· ≤ ·)).foldr
    (fun (p : Lex (Fin g × ℕ)) (acc : M) =>
      ((⇑(mode (N.YM (s (ofLex p).1)) (-((ofLex p).2 : ℤ) - 1)))^[μ (ofLex p)]) acc) u

/-- The ordered monomial is homogeneous of weight `α + Σ μ(i,m)(wt sᵢ + m)`. -/
theorem orderedMonomial_mem_weight (N : OrdVModule W M) {g : ℕ} (s : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hs : ∀ i, s i ∈ W.grading (wt i)) (μ : Fin g × ℕ →₀ ℕ) {α : ℂ} {u : M}
    (hu : u ∈ N.weight α) :
    orderedMonomial N s μ u ∈ N.weight (α + (multWDeg wt μ : ℂ)) := by
  rw [orderedMonomial]
  -- general statement for any list of pairs
  have hlist : ∀ l : List (Lex (Fin g × ℕ)),
      l.foldr (fun (p : Lex (Fin g × ℕ)) (acc : M) =>
        ((⇑(mode (N.YM (s (ofLex p).1)) (-((ofLex p).2 : ℤ) - 1)))^[μ (ofLex p)]) acc) u
      ∈ N.weight (α + ((l.map (fun p => μ (ofLex p) * (wt (ofLex p).1 + (ofLex p).2))).sum : ℂ)) := by
    intro l
    induction l with
    | nil => simpa using hu
    | cons p l ih =>
        rw [List.foldr_cons, List.map_cons, List.sum_cons]
        have h := mode_neg_iterate_mem_weight N (hs (ofLex p).1) (ofLex p).2 (μ (ofLex p)) ih
        convert h using 2
        push_cast
        ring
  convert hlist _ using 3
  -- the list sum over the sorted support is the `Finsupp.sum`
  rw [multWDeg, Finsupp.sum]
  have hsum : ((μ.support.map toLex.toEmbedding).sort (· ≤ ·)).map
      (fun p : Lex (Fin g × ℕ) => μ (ofLex p) * (wt (ofLex p).1 + (ofLex p).2))
      = ((μ.support.map toLex.toEmbedding).sort (· ≤ ·)).map
        ((fun q : Fin g × ℕ => μ q * (wt q.1 + q.2)) ∘ ofLex) := rfl
  rw [hsum, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq, Finset.map_val,
    Multiset.map_map, Finset.sum_eq_multiset_sum]
  exact congrArg Nat.cast (congrArg Multiset.sum (Multiset.map_congr rfl (fun q _ => rfl)))

/-- **Ordered (Buhl) spanning data**: finitely many homogeneous generators `gen i ∈ 𝒱_{wt i}`
(`wt i ≥ 1`) and bottom vectors `bot j ∈ M_{h + botWt j}` such that the ordered monomials
`orderedMonomial N gen μ (bot j)` span `M`. -/
structure OrderedSpanningData (N : OrdVModule W M) (h : ℂ) where
  g : ℕ
  gen : Fin g → 𝒱
  wt : Fin g → ℕ
  wt_pos : ∀ i, 1 ≤ wt i
  gen_mem : ∀ i, gen i ∈ W.grading (wt i)
  b : ℕ
  bot : Fin b → M
  botWt : Fin b → ℕ
  bot_mem : ∀ j, bot j ∈ N.weight (h + botWt j)
  spans : (⊤ : Submodule ℂ M) = Submodule.span ℂ {x | ∃ μ j, x = orderedMonomial N gen μ (bot j)}

/-- Ordered spanning data is PBW spanning data. -/
noncomputable def OrderedSpanningData.toPBW {N : OrdVModule W M} {h : ℂ} (d : OrderedSpanningData N h) :
    PBWSpanningData N h where
  g := d.g
  wt := d.wt
  wt_pos := d.wt_pos
  b := d.b
  botWt := d.botWt
  mono := fun μ j => orderedMonomial N d.gen μ (d.bot j)
  mono_mem := fun μ j => orderedMonomial_mem_weight N d.gen d.wt d.gen_mem μ (d.bot_mem j)
  spans := d.spans

/-- **Ordered spanning data ⟹ the growth datum.** -/
theorem subexponentialCoeffs_of_ordered (N : OrdVModule W M) (h : ℂ) (d : OrderedSpanningData N h) :
    SubexponentialCoeffs N (h - W.centralCharge / 24) :=
  subexponentialCoeffs_of_pbw N h d.toPBW

end Module

section Buhl
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Buhl's ordered spanning theorem, as a named datum for the VOA `W`**: every module with a
conformal weight admits ordered spanning data.  For `C₂`-cofinite `W` this is a theorem
(Buhl 2002; Gaberdiel–Neitzke for `W` itself).  As stated (every module with a conformal weight,
finite bottom family) it is not proved; the adjoint case and the finitely lowest-weight-generated
case are proved in `Modularity/BuhlSpanningC2.lean`. -/
def BuhlSpanning (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) (h : ℂ),
    HasConformalWeight N h → Nonempty (OrderedSpanningData N h)

/-- **The convergence wall, reduced to Buhl's theorem**: under `BuhlSpanning W`, every
module with conformal weight `h` has subexponential graded dimensions, hence its character
converges on all of `ℍ` (`qSummable_gradedDim`). -/
theorem subexponentialCoeffs_of_buhl {W : VertexOperatorAlgebra 𝒱} (hB : BuhlSpanning W)
    {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) (h : ℂ)
    (hw : HasConformalWeight N h) : SubexponentialCoeffs N (h - W.centralCharge / 24) :=
  (hB M N h hw).elim (fun d => subexponentialCoeffs_of_ordered N h d)

end Buhl

/-! ## Residual

`C2Cofinite W → BuhlSpanning W` — the ordered spanning set for modules of a `C₂`-cofinite VOA
(Buhl, *A spanning set for VOA modules*, J. Algebra 2002; Gaberdiel–Neitzke 2003 for `W` itself).
The ordering step is proved in `Modularity/BuhlSpanningC2.lean` for the adjoint module and for
modules with a finite lowest-weight generating bottom family; what remains open is the general
`BuhlSpanning W` without that generation hypothesis.  Everything downstream (the count,
subexponentiality, summability on `ℍ`) is proved. -/

end VOA
