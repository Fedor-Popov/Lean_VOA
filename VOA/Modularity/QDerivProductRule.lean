/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.FormalBlockFinite
import VOA.Modularity.SubexpSeriesRing

/-!
# The `qDeriv` product rule, and why Zhu Lemma 4.4.4 needs **no Ramanujan identities**

`qDeriv` is `ℂ`-linear but **not** `PowerSeries ℂ`-linear: for a supported `q`-series `χ`,

  `qDeriv (F ⋆ χ) = F ⋆ qDeriv χ + (θF) ⋆ χ`,   `θF := q dF/dq`.

This is exactly why Zhu's ODE (4.4.14) has coefficients in the **quasi**-modular ring
`ℂ[G₂,G₄,G₆]` rather than in `ℂ[G₄,G₆]`, and it is the one place where a naive reading of Zhu's
Lemma 4.4.4 appears to need **Ramanujan's identities** `θE₂ = (E₂²−E₄)/12` etc. — the statement that
`ℂ[G₂,G₄,G₆]` is `θ`-stable.

**The repo does not need them.**  The downstream consumer
`Modularity.FormalODE.onePointSubexp_of_formalODE` asks only that the ODE coefficients be
**subexponential**, and the subexponential series form a ring which is `θ`-stable *for free*
(`theta_mem_subexpPS`, off the banked `Subexponential.mul_pow`).  Monicity — the property Ramanujan
would have been invoked to preserve — comes from a different place entirely: Noetherian
stabilisation over `GSeries` in `Modularity.FormalBlockFinite.exists_monic_Lsq_relation`.

## Main results

* `theta`, `theta_coeff`, `theta_mul` — `q d/dq` on `PowerSeries ℂ`, a derivation;
* `qDeriv_psSMul` — the product rule;
* `theta_mem_subexpPS` — the subexponential series are `θ`-stable.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

/-! ## `q d/dq` on formal power series -/

/-- The Euler operator `θF = q·dF/dq` on formal power series. -/
noncomputable def theta (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n : ℂ) * PowerSeries.coeff n F

@[simp] theorem theta_coeff (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (theta F) = (n : ℂ) * PowerSeries.coeff n F := by
  rw [theta, PowerSeries.coeff_mk]

/-- `θ` is a derivation of `PowerSeries ℂ`. -/
theorem theta_mul (F G : PowerSeries ℂ) :
    theta (F * G) = theta F * G + F * theta G := by
  refine PowerSeries.ext fun n => ?_
  rw [theta_coeff, map_add, coeff_mul_range, coeff_mul_range, coeff_mul_range,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  have hcast : (m : ℂ) + ((n - m : ℕ) : ℂ) = (n : ℂ) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [theta_coeff, theta_coeff]
  linear_combination (PowerSeries.coeff m F * PowerSeries.coeff (n - m) G) * hcast.symm

/-! ## The product rule -/

theorem qDeriv_mem_QSeriesAt {h : ℂ} {χ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) :
    qDeriv χ ∈ QSeriesAt h := by
  intro e he
  change e * χ e = 0
  rw [hχ e he, mul_zero]

/-- **The `qDeriv` product rule.**  `qDeriv` is a derivation over the `qConv`-action of
`PowerSeries ℂ`, with the correction term given by `θ`. -/
theorem qDeriv_psSMul (F : PowerSeries ℂ) {h : ℂ} {χ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) :
    qDeriv (psSMul F χ) = psSMul F (qDeriv χ) + psSMul (theta F) χ := by
  refine QSeriesAt.ext (qDeriv_mem_QSeriesAt (psSMul_mem F hχ))
    (Submodule.add_mem _ (psSMul_mem F (qDeriv_mem_QSeriesAt hχ)) (psSMul_mem _ hχ)) (fun N => ?_)
  change (h + (N : ℂ)) * psSMul F χ (h + (N : ℂ))
    = psSMul F (qDeriv χ) (h + (N : ℂ)) + psSMul (theta F) χ (h + (N : ℂ))
  rw [psSMul_apply_coset F hχ N, psSMul_apply_coset F (qDeriv_mem_QSeriesAt hχ) N,
    psSMul_apply_coset _ hχ N, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_range] at hn
  have hcast : ((N - n : ℕ) : ℂ) + (n : ℂ) = (N : ℂ) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  change (h + (N : ℂ)) * (PowerSeries.coeff n F * χ (h + ((N - n : ℕ) : ℂ)))
    = PowerSeries.coeff n F * ((h + ((N - n : ℕ) : ℂ)) * χ (h + ((N - n : ℕ) : ℂ)))
      + PowerSeries.coeff n (theta F) * χ (h + ((N - n : ℕ) : ℂ))
  rw [theta_coeff]
  linear_combination (PowerSeries.coeff n F * χ (h + ((N - n : ℕ) : ℂ))) * hcast.symm

/-! ## The subexponential series are `θ`-stable -/

/-- **`θ` preserves subexponential growth.**  Multiplying the `n`-th coefficient by `n` is a
polynomial factor, which `Subexponential.mul_pow` absorbs.  Hence the ODE coefficients produced by
Zhu Lemma 4.4.4 stay subexponential **without** `ℂ[G₂,G₄,G₆]` being `θ`-stable — that is, without
Ramanujan's identities. -/
theorem theta_mem_subexpPS {F : PowerSeries ℂ} (hF : F ∈ SubexpPS) : theta F ∈ SubexpPS := by
  have hpow := (Subexponential.mul_pow hF (fun n => norm_nonneg _) 1)
  refine Subexponential.of_le (fun n => ?_) hpow
  rw [theta_coeff, norm_mul, Complex.norm_natCast, pow_one]

theorem theta_mem_subexpPS_of_mem_GSeries {F : PowerSeries ℂ} (hF : F ∈ GSeries) :
    theta F ∈ SubexpPS :=
  theta_mem_subexpPS (GSeries_le_subexpPS hF)

end VOA
