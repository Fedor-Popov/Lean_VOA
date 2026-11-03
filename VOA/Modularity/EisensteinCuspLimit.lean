/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.EisensteinAnalytic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# The cusp limit of Zhu's Eisenstein family

`Modularity.FormalSpecialization` records that a purely formal `ℂ⟦q⟧` argument cannot reach a
point of `ℍ`, and names the single analytic input the polynomial-ring route needs:

  `G_{2j}(z) → G_{2j}(∞) = zhuG j 0` as `Im z → ∞`.

That is proved here, off Mathlib's `q`-expansion machinery: `zhuGC_eq_mul_E` writes
`G_{2j} = (zhuG j 0)·E_{2j}` for `j ≥ 2`, `ModularFormClass.exp_decay_sub_atImInfty'` gives
exponential decay of `E_{2j} − E_{2j}(∞)` along `atImInfty`, and
`EisensteinSeries.E_qExpansion_coeff_zero` identifies `E_{2j}(∞) = 1`.

## Main results

* `tendsto_modularForm_atImInfty` — every level-one modular form tends to its value at `∞`;
* `valueAtInfty_E` — `E_k(∞) = 1`;
* `tendsto_zhuGC_atImInfty` — `G_{2j}(z) → zhuG j 0`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Filter UpperHalfPlane Complex
open scoped Topology Real MatrixGroups

/-- Along `atImInfty` the exponential `e^{−c·Im τ}` tends to `0` for `c > 0`. -/
theorem tendsto_exp_neg_im_atImInfty {c : ℝ} (hc : 0 < c) :
    Tendsto (fun τ : UpperHalfPlane => Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
  have him : Tendsto (fun τ : UpperHalfPlane => τ.im) atImInfty atTop := tendsto_comap
  have hneg : Tendsto (fun τ : UpperHalfPlane => -c * τ.im) atImInfty atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -c < 0)).mpr him
  exact Real.tendsto_exp_atBot.comp hneg

/-- **A level-one modular form tends to its value at the cusp.** -/
theorem tendsto_modularForm_atImInfty {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [FunLike F UpperHalfPlane ℂ] [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] [Fact (IsCusp OnePoint.infty Γ)] (f : F) :
    Tendsto (fun τ : UpperHalfPlane => f τ) atImInfty (𝓝 (valueAtInfty (fun τ => f τ))) := by
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_sub_atImInfty' (F := F) (Γ := Γ) (k := k) (f := f)
  have hz : Tendsto (fun τ : UpperHalfPlane => f τ - valueAtInfty (fun τ => f τ)) atImInfty (𝓝 0) :=
    hO.trans_tendsto (tendsto_exp_neg_im_atImInfty hc)
  rwa [tendsto_sub_nhds_zero_iff] at hz

/-- `E_k(∞) = 1`. -/
theorem valueAtInfty_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    valueAtInfty (fun τ : UpperHalfPlane => ModularForm.E hk τ) = 1 := by
  have hq := EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  rw [qExpansion_coeff_zero (h := 1) one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero (F := ModularForm _ k)
      (f := ModularForm.E hk) one_pos one_mem_strictPeriods_SL)
    (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk)
      one_mem_strictPeriods_SL)] at hq
  exact hq

/-- **The cusp limit of Zhu's Eisenstein family**: `G_{2j}(z) → −B_{2j}/(2j)!`. -/
theorem tendsto_zhuGC_atImInfty {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun τ : UpperHalfPlane => zhuGC j (τ : ℂ)) atImInfty (𝓝 (zhuG j 0)) := by
  have hk : 3 ≤ 2 * j := by omega
  have hk2 : Even (2 * j) := ⟨j, by ring⟩
  have hrw : (fun τ : UpperHalfPlane => zhuGC j (τ : ℂ))
      = fun τ : UpperHalfPlane => zhuG j 0 * ModularForm.E hk τ := by
    funext τ
    rw [zhuGC_eq_mul_E hj (coe_mem_imGT_zero τ)]
  rw [hrw]
  have hE := tendsto_modularForm_atImInfty (ModularForm.E hk)
  rw [valueAtInfty_E hk hk2] at hE
  simpa using hE.const_mul (zhuG j 0)

end VOA
