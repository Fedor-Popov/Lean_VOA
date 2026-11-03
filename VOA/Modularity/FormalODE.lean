/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OnePointODE
import VOA.Modularity.ZhuBlockConditions

/-!
# The formal ODE, in the repo's own `qDeriv`/`qConv` language

`Modularity.OnePointODE` reduces residual **(c)** to a hypothesis stated at the level of
`q`-coefficients.  This file restates it in the repo's *native* formal language — an identity of
`FormalQSeries` — and proves the two are equivalent, so producing the ODE does not require any
coefficient bookkeeping.

The reduction is clean because **`qDeriv` is diagonal**: `qDeriv χ e = e · χ e`
(`ZhuBlockConditions.lean:35`), so `qDeriv^[i] χ e = e^i · χ e`, which is exactly the shape
`indicialP` expects.  And `qConv f χ e = ∑ᶠ k, f k · χ (e − k)` truncates to `k ≤ n` on a
lowest-weight-supported series, giving the convolution `∑_{m ≤ n} f (n−m) · χ (λ+m)`.

`IsFormalBlock`'s `ω`-law **solves for `qDeriv`** (`IsFormalBlock.qDeriv_eq`), so the span of the
block values is `qDeriv`-stable with no hypotheses at all — the formal analogue of
`IsAnalyticBlock.serreDeriv_mem`, but unconditional.

## Main results

* `qDeriv_iterate_apply` — `qDeriv^[i] χ e = e^i · χ e`;
* `IsFormalBlock.qDeriv_eq` — `∂`-stability, unconditional;
* `indicialP_recursion_of_formalODE` — the formal ODE gives the indicial recursion;
* `onePointSubexp_of_formalODE` — hence `OnePointSubexp`, from an ODE stated as an identity
  of formal `q`-series.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  The ODE itself is an explicit hypothesis.
-/

namespace VOA

open scoped BigOperators

universe u

/-- `qDeriv` is the diagonal Euler operator, so its iterates are diagonal too. -/
theorem qDeriv_iterate_apply (χ : FormalQSeries) (i : ℕ) (e : ℂ) :
    (qDeriv^[i] χ) e = e ^ i * χ e := by
  induction i generalizing χ with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, qDeriv, pow_succ]
      ring

/-- The `k`-th term of `qConv (g) (qDeriv^[i] χ)` at `λ + n`, rewritten as a `Finset` sum over
`m ≤ n` when `χ` is supported in `λ + ℕ`. -/
theorem qConv_iterate_apply {χ : FormalQSeries} {lam : ℂ}
    (hsupp : ∀ d : ℤ, d < 0 → χ (lam + (d : ℂ)) = 0) (f : ℕ → ℂ) (i n : ℕ) :
    qConv f (qDeriv^[i] χ) (lam + (n : ℂ))
      = ∑ m ∈ Finset.range (n + 1), f (n - m) * (lam + (m : ℂ)) ^ i * χ (lam + (m : ℂ)) := by
  classical
  have hvanish : ∀ k : ℕ, n < k → f k * (qDeriv^[i] χ) (lam + (n : ℂ) - (k : ℂ)) = 0 := by
    intro k hk
    have hcast : lam + (n : ℂ) - (k : ℂ) = lam + (((n : ℤ) - (k : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    rw [hcast, qDeriv_iterate_apply, hsupp _ (by omega), mul_zero, mul_zero]
  have hsub : (Function.support fun k : ℕ => f k * (qDeriv^[i] χ) (lam + (n : ℂ) - (k : ℂ)))
      ⊆ (Finset.range (n + 1) : Finset ℕ) := by
    intro k hk
    by_contra hnot
    exact hk (hvanish k (by simpa [Finset.mem_range] using hnot))
  rw [qConv, finsum_eq_sum_of_support_subset _ hsub,
    ← Finset.sum_range_reflect
      (fun m => f (n - m) * (lam + (m : ℂ)) ^ i * χ (lam + (m : ℂ))) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hcast : lam + (n : ℂ) - (k : ℂ) = lam + ((n - k : ℕ) : ℂ) := by
    rw [Nat.cast_sub hkn]; ring
  have hnk : n - (n - k) = k := by omega
  rw [hcast, qDeriv_iterate_apply]
  change f k * ((lam + ((n - k : ℕ) : ℂ)) ^ i * χ (lam + ((n - k : ℕ) : ℂ)))
      = f (n - (n - k)) * (lam + ((n - k : ℕ) : ℂ)) ^ i * χ (lam + ((n - k : ℕ) : ℂ))
  rw [hnk]
  ring

section Block

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Formal `∂`-stability, unconditional.**  The `ω`-law of a formal block solves for `qDeriv`,
so `qDeriv (S v)` is a `zhuG`-combination of the block's values at other vectors.  This is the
formal analogue of `IsAnalyticBlock.serreDeriv_mem` — and unlike it, it needs no holomorphy. -/
theorem IsFormalBlock.qDeriv_eq {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsFormalBlock W S) (v : 𝒱) :
    qDeriv (S v)
      = S (Lsq W (-2) v)
        - ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v)) := by
  have h := hS.omega v
  rw [h]
  abel

end Block

/-- **The formal ODE gives the indicial recursion.**  Evaluating
`qDeriv^[s] χ + ∑_{i<s} qConv (g i) (qDeriv^[i] χ) = 0` at `λ + n` and splitting off the `m = n`
term produces exactly the hypothesis of `Modularity.OnePointODE.subexponential_of_indicialODE`. -/
theorem indicialP_recursion_of_formalODE {χ : FormalQSeries} {lam : ℂ}
    (hsupp : ∀ d : ℤ, d < 0 → χ (lam + (d : ℂ)) = 0) {s : ℕ} (g : ℕ → ℕ → ℂ)
    (hODE : ∀ e : ℂ, (qDeriv^[s] χ) e + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] χ) e = 0)
    (n : ℕ) :
    indicialP lam s g n * χ (lam + (n : ℂ))
      = - ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
          g i (n - m) * (lam + (m : ℂ)) ^ i * χ (lam + (m : ℂ)) := by
  classical
  have hE := hODE (lam + (n : ℂ))
  rw [qDeriv_iterate_apply] at hE
  have hconv : ∀ i ∈ Finset.range s,
      qConv (g i) (qDeriv^[i] χ) (lam + (n : ℂ))
        = (∑ m ∈ Finset.range n, g i (n - m) * (lam + (m : ℂ)) ^ i * χ (lam + (m : ℂ)))
          + g i 0 * (lam + (n : ℂ)) ^ i * χ (lam + (n : ℂ)) := by
    intro i _
    rw [qConv_iterate_apply hsupp (g i) i n, Finset.sum_range_succ]
    simp
  rw [Finset.sum_congr rfl hconv, Finset.sum_add_distrib] at hE
  have hsplit : ∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i * χ (lam + (n : ℂ))
      = (∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i) * χ (lam + (n : ℂ)) := by
    rw [Finset.sum_mul]
  rw [hsplit] at hE
  have hswap : ∑ i ∈ Finset.range s, ∑ m ∈ Finset.range n,
        g i (n - m) * (lam + (m : ℂ)) ^ i * χ (lam + (m : ℂ))
      = ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
        g i (n - m) * (lam + (m : ℂ)) ^ i * χ (lam + (m : ℂ)) := Finset.sum_comm
  rw [hswap] at hE
  rw [indicialP, add_mul]
  linear_combination hE

section VOA

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **`OnePointSubexp` from a formal ODE.**  This is residual **(c)**'s hypothesis in the
repo's native language: for each `v`, an identity of formal `q`-series
`qDeriv^[s] 𝒵_M(v) + ∑_{i<s} qConv (g i) (qDeriv^[i] 𝒵_M(v)) = 0`, monic by construction, with
subexponential coefficient sequences. -/
theorem onePointSubexp_of_formalODE (N : OrdVModule W M) (hbase : ℂ)
    (hsupp : OnePointSupported N hbase)
    (hODE : ∀ v : 𝒱, ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧
      (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (torusOnePoint N v)) e
        + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (torusOnePoint N v)) e = 0) :
    OnePointSubexp N hbase := by
  refine onePointSubexp_of_indicialODE N hbase (fun v => ?_)
  obtain ⟨s, g, hs, hg, hode⟩ := hODE v
  exact ⟨s, g, hs, hg, fun n =>
    indicialP_recursion_of_formalODE (fun d hd => hsupp v d hd) g hode n⟩

end VOA

end VOA
