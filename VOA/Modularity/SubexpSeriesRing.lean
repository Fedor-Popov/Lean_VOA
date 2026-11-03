/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.QExpansionBridge
import VOA.Modularity.OnePointDescent
import VOA.Modularity.FormalODE

/-!
# Residual **(c-iii)**: `ℂ[G₂, G₄, G₆]` consists of subexponential series

`Modularity.QExpansionBridge` places every `PowerSeries.mk (zhuG j)` in the Noetherian subring
`GSeries = ℂ[G₂, G₄, G₆] ⊆ PowerSeries ℂ`.  The banked consumer
`Modularity.FormalODE.onePointSubexp_of_formalODE` needs one more thing of the ODE coefficients:
that each is **subexponential**.  This file supplies it, by exhibiting the subexponential series as
a `ℂ`-*subalgebra* of `PowerSeries ℂ` containing the three generators.

The only new ingredient is that the **Cauchy product** preserves subexponential growth; it is the
sequence-level form of the banked `Modularity.OnePointDescent.subexponential_qConv`, and is proved
the same way (choose `1 < s < r`, so that `Σ_{m ≤ n} D sᵐ · C r^{n−m} ≤ CD(1 − s/r)⁻¹ rⁿ`).

## Main results

* `subexponential_cauchy` — the Cauchy product of subexponential sequences is subexponential;
* `SubexpPS` — the `ℂ`-subalgebra of subexponential formal power series;
* `subexponential_coeff_of_mem_GSeries` — **(c-iii)**: every element of `ℂ[G₂, G₄, G₆]` has
  subexponential coefficients, i.e. `GSeries` meets the growth hypothesis of
  `onePointSubexp_of_formalODE`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

/-! ## The Cauchy product preserves subexponential growth -/

/-- **The Cauchy product preserves subexponential growth.**  With `1 < s < r` chosen between the
two ratios, `Σ_{m ≤ n} D sᵐ · C r^{n−m} = CD rⁿ Σ_m (s/r)ᵐ ≤ CD(1 − s/r)⁻¹ rⁿ`. -/
theorem subexponential_cauchy {a b : ℕ → ℂ}
    (ha : Subexponential fun m : ℕ => ‖a m‖) (hb : Subexponential fun m : ℕ => ‖b m‖) :
    Subexponential fun n : ℕ => ‖∑ m ∈ Finset.range (n + 1), a m * b (n - m)‖ := by
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  obtain ⟨s, hs1, hsr⟩ : ∃ s : ℝ, 1 < s ∧ s < r := ⟨(1 + r) / 2, by linarith, by linarith⟩
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  obtain ⟨D, hD⟩ := ha s hs1
  obtain ⟨C, hC⟩ := hb r hr
  have hD0 : 0 ≤ D := by
    have h0 := hD 0
    simp only [pow_zero, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    simp only [pow_zero, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  set x : ℝ := s / r with hx
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hr0]; exact hsr
  refine ⟨C * D * (1 - x)⁻¹, fun n => ?_⟩
  have hgeo : ∑ m ∈ Finset.range (n + 1), x ^ m ≤ (1 - x)⁻¹ := by
    have hsum : Summable (fun m : ℕ => x ^ m) := summable_geometric_of_lt_one hx0 hx1
    have hle := Summable.sum_le_tsum (Finset.range (n + 1)) (fun m _ => pow_nonneg hx0 m) hsum
    rwa [tsum_geometric_of_lt_one hx0 hx1] at hle
  calc ‖∑ m ∈ Finset.range (n + 1), a m * b (n - m)‖
      ≤ ∑ m ∈ Finset.range (n + 1), ‖a m * b (n - m)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (n + 1), (D * s ^ m) * (C * r ^ (n - m)) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (hD m) (hC (n - m)) (norm_nonneg _) (by positivity)
    _ = C * D * r ^ n * ∑ m ∈ Finset.range (n + 1), x ^ m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [Finset.mem_range] at hm
        have hle : m ≤ n := by omega
        rw [pow_sub₀ r (ne_of_gt hr0) hle, hx, div_pow, div_eq_mul_inv]
        ring
    _ ≤ C * D * r ^ n * (1 - x)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hgeo ?_
        positivity
    _ = C * D * (1 - x)⁻¹ * r ^ n := by ring

/-- The coefficients of a product of formal power series, as a `Finset.range` convolution. -/
theorem coeff_mul_range (F G : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (F * G)
      = ∑ m ∈ Finset.range (n + 1),
          PowerSeries.coeff m F * PowerSeries.coeff (n - m) G := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-! ## The subalgebra of subexponential power series -/

/-- The `ℂ`-subalgebra of `PowerSeries ℂ` consisting of the series with subexponential
coefficients. -/
def SubexpPS : Subalgebra ℂ (PowerSeries ℂ) where
  carrier := {F : PowerSeries ℂ | Subexponential fun n : ℕ => ‖PowerSeries.coeff n F‖}
  mul_mem' := fun {F G} hF hG => by
    refine Subexponential.of_le (fun n => ?_) (subexponential_cauchy hF hG)
    rw [coeff_mul_range]
  one_mem' := by
    refine Subexponential.of_le (b := fun _ : ℕ => (1 : ℝ)) (fun n => ?_) (subexponential_const 1)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [PowerSeries.coeff_one, if_neg hn, norm_zero]
      norm_num
  add_mem' := fun {F G} hF hG => by
    refine Subexponential.of_le (fun n => ?_) (hF.add hG)
    rw [map_add]
    exact norm_add_le _ _
  zero_mem' := by
    refine Subexponential.of_le (fun n => ?_) subexponential_zero
    simp
  algebraMap_mem' := fun c => by
    refine Subexponential.of_le (b := fun _ : ℕ => ‖c‖) (fun n => ?_) (subexponential_const ‖c‖)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [show (algebraMap ℂ (PowerSeries ℂ) c) = PowerSeries.C c from rfl,
        PowerSeries.coeff_C, if_neg hn, norm_zero]
      exact norm_nonneg c

@[simp] theorem mem_subexpPS {F : PowerSeries ℂ} :
    F ∈ SubexpPS ↔ Subexponential fun n : ℕ => ‖PowerSeries.coeff n F‖ := Iff.rfl

theorem mk_zhuG_mem_subexpPS (j : ℕ) : PowerSeries.mk (zhuG j) ∈ SubexpPS := by
  refine Subexponential.of_le (fun n => ?_) (subexponential_zhuG j)
  rw [PowerSeries.coeff_mk]

/-- `ℂ[G₂, G₄, G₆]` sits inside the subexponential series. -/
theorem GSeries_le_subexpPS : GSeries ≤ SubexpPS := by
  rw [GSeries, Algebra.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mk_zhuG_mem_subexpPS 1
  · exact mk_zhuG_mem_subexpPS 2
  · exact mk_zhuG_mem_subexpPS 3

/-- **Residual (c-iii)**: every element of the Noetherian ring `ℂ[G₂, G₄, G₆]` has
subexponential coefficients — exactly the growth hypothesis
`∀ i, Subexponential (fun k => ‖g i k‖)` of
`Modularity.FormalODE.onePointSubexp_of_formalODE`. -/
theorem subexponential_coeff_of_mem_GSeries {F : PowerSeries ℂ} (hF : F ∈ GSeries) :
    Subexponential fun n : ℕ => ‖PowerSeries.coeff n F‖ :=
  GSeries_le_subexpPS hF

/-! ## The packaged consumer: an ODE over `ℂ[G₂, G₄, G₆]` gives the growth datum -/

section VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **Residual (c), fully packaged.**  Once the one-point functions satisfy a *monic* linear
`qDeriv`-equation whose coefficients lie in the Noetherian ring `ℂ[G₂, G₄, G₆]`, the growth datum
`OnePointSubexp` follows: `(c-iii)` supplies the subexponential bound on those coefficients, and
`Modularity.FormalODE.onePointSubexp_of_formalODE` does the rest.

This is the exact residual shape left by `(c-i)`–`(c-iii)`: nothing about growth, convolution or
Eisenstein coefficients remains — only the production of the equation itself. -/
theorem onePointSubexp_of_GSeriesODE (N : OrdVModule W M) (hbase : ℂ)
    (hsupp : OnePointSupported N hbase)
    (hODE : ∀ v : 𝒱, ∃ (s : ℕ) (G : ℕ → PowerSeries ℂ), 1 ≤ s ∧
      (∀ i, G i ∈ GSeries) ∧
      ∀ e : ℂ, (qDeriv^[s] (torusOnePoint N v)) e
        + ∑ i ∈ Finset.range s,
            qConv (fun k => PowerSeries.coeff k (G i)) (qDeriv^[i] (torusOnePoint N v)) e = 0) :
    OnePointSubexp N hbase := by
  refine onePointSubexp_of_formalODE N hbase hsupp (fun v => ?_)
  obtain ⟨s, G, hs, hmem, hode⟩ := hODE v
  exact ⟨s, fun i k => PowerSeries.coeff k (G i), hs,
    fun i => subexponential_coeff_of_mem_GSeries (hmem i), hode⟩

end VOA

end VOA
