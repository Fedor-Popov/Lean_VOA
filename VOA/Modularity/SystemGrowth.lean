/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockSystem

/-!
# A first-order `q`-system with subexponential coefficients has subexponential solutions

This is the analytic core of residual **(c)**, stated with no reference to vertex algebras.

Given finitely many `q`-series `z₁,…,z_g` based at `hbase` and a matrix `a` of coefficient
sequences, suppose

  `(hbase + N)·z_k(N) = ∑_l ∑_{j ≤ N} a_{kl}(j)·z_l(N − j)`   for all `k`, `N`

— the coefficient form of the system `q d/dq z = a ⋆ z`.  If every `a_{kl}` is subexponential then
so is every `z_k`.

**No matrix inverses, no eigenvalue avoidance, no indicial polynomial.**  Summing the estimate
over `k` collapses the vector recursion to the scalar one
`(‖hbase+N‖ − K)·Z_N ≤ ∑_{m<N} B_{N−m}·Z_m`, with `Z_N := ∑_k ‖z_k(N)‖`, `B_j := ∑_{k,l}‖a_{kl}(j)‖`
and `K := B₀` — which is *exactly* the hypothesis of the banked majorant theorem (★)
`Modularity.Majorant.subexponential_of_majorant_recursion`, with `b = 0` and `p N = ‖hbase+N‖ − K`.
The `‖hbase+N‖ → ∞` that makes `p` admissible is the same fact that makes the indicial polynomial
have positive degree in the scalar treatment; here it is available with no monicity argument.

## Main results

* `sum_range_shift_reflect` — the index reflection `j ↦ N − (j+1)`;
* `subexponential_of_system`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open Filter

/-- Reindex a `range N` sum by `j ↦ N − (j + 1)`. -/
theorem sum_range_shift_reflect {M : Type*} [AddCommMonoid M] (F : ℕ → M) (N : ℕ) :
    ∑ j ∈ Finset.range N, F (N - (j + 1)) = ∑ m ∈ Finset.range N, F m := by
  rw [← Finset.sum_range_reflect F N]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  congr 1
  omega

/-- `‖hbase + N‖ − K → ∞`. -/
theorem tendsto_norm_add_natCast_sub_atTop (hbase : ℂ) (K : ℝ) :
    Tendsto (fun N : ℕ => ‖hbase + (N : ℂ)‖ - K) atTop atTop := by
  refine tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ) + (-‖hbase‖ - K)) (fun N => ?_) ?_
  · have h1 : ‖(N : ℂ)‖ - ‖-hbase‖ ≤ ‖(N : ℂ) - (-hbase)‖ := norm_sub_norm_le _ _
    rw [norm_neg, sub_neg_eq_add] at h1
    have h2 : ((N : ℂ) + hbase) = hbase + (N : ℂ) := by ring
    rw [h2, Complex.norm_natCast] at h1
    linarith
  · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- **A first-order `q`-system with subexponential coefficients has subexponential
solutions.** -/
theorem subexponential_of_system {g : ℕ} {hbase : ℂ}
    (z : Fin g → ℕ → ℂ) (a : Fin g → Fin g → ℕ → ℂ)
    (ha : ∀ k l, Subexponential (fun j => ‖a k l j‖))
    (hrec : ∀ (k : Fin g) (N : ℕ),
      (hbase + (N : ℂ)) * z k N
        = ∑ l, ∑ j ∈ Finset.range (N + 1), a k l j * z l (N - j)) :
    ∀ k, Subexponential (fun N => ‖z k N‖) := by
  classical
  set Z : ℕ → ℝ := fun N => ∑ k, ‖z k N‖ with hZ
  set B : ℕ → ℝ := fun j => ∑ k, ∑ l, ‖a k l j‖ with hB
  set K : ℝ := B 0 with hK
  have hZ0 : ∀ N, 0 ≤ Z N := fun N => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hB0 : ∀ j, 0 ≤ B j := fun j =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hzle : ∀ (k : Fin g) (N : ℕ), ‖z k N‖ ≤ Z N := by
    intro k N
    exact Finset.single_le_sum (f := fun k => ‖z k N‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  have hBsub : Subexponential B := by
    refine Subexponential.finsetSum Finset.univ (fun k n => ∑ l, ‖a k l n‖) (fun k _ => ?_)
    exact Subexponential.finsetSum Finset.univ (fun l n => ‖a k l n‖) (fun l _ => ha k l)
  -- the scalar majorant estimate
  have hkey : ∀ N : ℕ, (‖hbase + (N : ℂ)‖ - K) * Z N
      ≤ (∑ m ∈ Finset.range N, B (N - m) * Z m) + 0 := by
    intro N
    rw [add_zero]
    -- per-`k` estimate
    have hrow : ∀ k : Fin g, ‖hbase + (N : ℂ)‖ * ‖z k N‖
        ≤ (∑ l, ‖a k l 0‖) * Z N
          + ∑ l, ∑ m ∈ Finset.range N, ‖a k l (N - m)‖ * ‖z l m‖ := by
      intro k
      have hsplit : ∀ l : Fin g, ∑ j ∈ Finset.range (N + 1), a k l j * z l (N - j)
          = (∑ j ∈ Finset.range N, a k l (j + 1) * z l (N - (j + 1)))
            + a k l 0 * z l N := by
        intro l
        rw [Finset.sum_range_succ']
        simp
      have he := hrec k N
      rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hsplit l),
        Finset.sum_add_distrib] at he
      have hnorm : ‖hbase + (N : ℂ)‖ * ‖z k N‖
          ≤ ‖∑ l, ∑ j ∈ Finset.range N, a k l (j + 1) * z l (N - (j + 1))‖
            + ‖∑ l, a k l 0 * z l N‖ := by
        rw [← norm_mul, he]
        exact norm_add_le _ _
      refine le_trans hnorm ?_
      have hb1 : ‖∑ l, a k l 0 * z l N‖ ≤ (∑ l, ‖a k l 0‖) * Z N := by
        refine le_trans (norm_sum_le _ _) ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hzle l N) (norm_nonneg _)
      have hb2 : ‖∑ l, ∑ j ∈ Finset.range N, a k l (j + 1) * z l (N - (j + 1))‖
          ≤ ∑ l, ∑ m ∈ Finset.range N, ‖a k l (N - m)‖ * ‖z l m‖ := by
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum (fun l _ => ?_)
        refine le_trans (norm_sum_le _ _) ?_
        have hre : ∑ j ∈ Finset.range N, ‖a k l (j + 1) * z l (N - (j + 1))‖
            = ∑ m ∈ Finset.range N, ‖a k l (N - m)‖ * ‖z l m‖ := by
          rw [← sum_range_shift_reflect (fun m => ‖a k l (N - m)‖ * ‖z l m‖) N]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [Finset.mem_range] at hj
          have hidx : N - (N - (j + 1)) = j + 1 := by omega
          show ‖a k l (j + 1) * z l (N - (j + 1))‖
            = ‖a k l (N - (N - (j + 1)))‖ * ‖z l (N - (j + 1))‖
          rw [hidx, norm_mul]
        exact le_of_eq hre
      linarith
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hrow k)
    rw [← Finset.mul_sum] at hsum
    have hstep : ∑ k : Fin g, ((∑ l, ‖a k l 0‖) * Z N
        + ∑ l, ∑ m ∈ Finset.range N, ‖a k l (N - m)‖ * ‖z l m‖)
        ≤ K * Z N + ∑ m ∈ Finset.range N, B (N - m) * Z m := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      refine add_le_add (le_of_eq (by rw [hK, hB])) ?_
      have hcomm : ∑ k : Fin g, ∑ l, ∑ m ∈ Finset.range N, ‖a k l (N - m)‖ * ‖z l m‖
          = ∑ m ∈ Finset.range N, ∑ k : Fin g, ∑ l, ‖a k l (N - m)‖ * ‖z l m‖ := by
        have h1 : ∀ k : Fin g, ∑ l, ∑ m ∈ Finset.range N, ‖a k l (N - m)‖ * ‖z l m‖
            = ∑ m ∈ Finset.range N, ∑ l, ‖a k l (N - m)‖ * ‖z l m‖ :=
          fun _ => Finset.sum_comm
        rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => h1 k), Finset.sum_comm]
      rw [hcomm]
      refine Finset.sum_le_sum (fun m _ => ?_)
      rw [hB, Finset.sum_mul]
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l _ => ?_)
      exact mul_le_mul_of_nonneg_left (hzle l m) (norm_nonneg _)
    have := le_trans hsum hstep
    rw [sub_mul]
    linarith
  have hZsub : Subexponential Z :=
    subexponential_of_majorant_recursion hZ0 hB0 (fun _ => le_refl 0) hBsub subexponential_zero
      (tendsto_norm_add_natCast_sub_atTop hbase K) 0 (fun N _ => hkey N)
  intro k
  exact Subexponential.of_le (fun N => hzle k N) hZsub

end VOA
