/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TwistedPlusConj
import VOA.Moonshine.TwistedPlusModule
import VOA.Moonshine.Character

/-!
# `(V_Λ^T)^+` as an ordinary `V_Λ^+`-module  (Moonshine step M8a)

On the Leech twisted module `V_Λ^T = S[θ] ⊗ T_Λ` (`leechTwistedModule`, `FockT 24 ⊗ T`):

* `thetaTwLeech = twTheta 24 T_Λ = thetaT ⊗ (−1)` — FLM's lift of `θ` (`θ = −1` on `T`, DGM
  (5.38) with `d = 24`).  It is an involution, preserves the `L₀`-grading, and
  `Y^T(θu) = θ_tw Y^T(u) θ_tw` (`leechTwistedModule_YM_theta`); bundled as `leechThetaLift`.
* `TP := ker(θ_tw − 1)`, *definitionally* `TwistedSector.twFixed 24 T_Λ` (`TP_eq_twFixed`).
* `plusModule : OrdVModule leechVOAPlus TP` with `u₍ₙ₎ = Y^T(u)₍2n/2₎` (`mode_plusModule`); the
  odd fractional modes of `u ∈ V_Λ^+` vanish (`YM_odd_eq_zero_of_plus`).
* The grading: `(plusModule.weight q).map TP.subtype = twFixed 24 T ⊓ twWeight 24 T q`
  (`map_plusModule_weight`), hence `finrank_plusModule_weight` — the module grading *is* the
  M7c/M7d grading.  Consequences: integer weights `≥ 2` only (`plusModule_weight_ne_bot`),
  `dim TP₂ = 98304` (`finrank_plusModule_weight_two`), and
  `finrank_plusModule_eq_coeff_JShift : dim (V_Λ^+)_n + dim TP_n = [qⁿ](q·J)` for all `n`.

## Sign bookkeeping (checked)
Conjugation is insensitive to the sign on `T` (it is central), so both lifts `thetaT ⊗ (±1)`
satisfy the compatibility; `−1` is singled out by integrality: `θ_tw = (−1)^{d+1}` on doubled
oscillator weight `d` (`twTheta_of_mem_twGrading`), so `TP` = odd `d` = integer `L₀ = (d+3)/2`,
lowest weight `2` (`h(−½) ⊗ t`).  With `+1` the fixed part would be `3/2 + ℤ`.  This agrees
with `twFixed_eq_iSup_int`.

## Status
All declarations `sorry`-free; unconditional.  Not done in this file: the `V_Λ^+`-module is not shown
irreducible, and the `ℤ`-indexed grading needed for `V♮` is only the restriction of the
`ℂ`-indexed one (`plusModule_weight_ne_bot`).
-/

namespace VOA.Moonshine

open LatticeTwisted TwistedSector TwistedPlus TwistedHeisenberg Module
open scoped TensorProduct

/-- The Leech twisted sector `S[θ] ⊗ T_Λ`. -/
abbrev Tw : Type := FockT 24 ⊗[ℂ] leechT

/-- **FLM's `θ` on the Leech twisted sector**, `thetaT ⊗ (−1)`. -/
noncomputable abbrev thetaTwLeech : End ℂ Tw := twTheta 24 leechT

theorem weightLT_ratCast {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm] (q : ℚ) :
    weightLT r Tm (q : ℂ) = twWeight r Tm q := by
  unfold weightLT twWeight
  refine iSup_congr fun d => ?_
  simp only [Rat.cast_inj]
  rfl

theorem twTheta_mem_weightLT {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm] {α : ℂ}
    {x : FockT r ⊗[ℂ] Tm} (hx : x ∈ weightLT r Tm α) : twTheta r Tm x ∈ weightLT r Tm α := by
  have hle : weightLT r Tm α ≤ (weightLT r Tm α).comap (twTheta r Tm) := by
    refine iSup₂_le fun d hd y hy => ?_
    rw [Submodule.mem_comap, twTheta_of_mem_twGrading (d := d) hy]
    exact Submodule.smul_mem _ _
      ((le_iSup₂_of_le (f := fun (e : ℕ) (_ : ((levelT r e : ℚ) : ℂ) = α) => GT r Tm e)
        d hd le_rfl) hy)
  exact hle hx

/-- The lift `θ_tw` of `leechTheta` to the Leech twisted module. -/
noncomputable def leechThetaLift : ThetaLift leechTwistedModule where
  op := thetaTwLeech
  op_op := twTheta_twTheta 24 leechT
  conj := leechTwistedModule_YM_theta
  map_weight α x hx := by
    rw [leechTwistedModule_weight] at hx ⊢
    exact twTheta_mem_weightLT hx

/-- **`(V_Λ^T)^+ = ker(θ_tw − 1)`.** -/
noncomputable abbrev TP : Submodule ℂ Tw := plusSub leechThetaLift

theorem TP_eq_twFixed : TP = twFixed 24 leechT := rfl

/-- **`(V_Λ^T)^+` is an ordinary `V_Λ^+`-module.** -/
noncomputable def plusModule : OrdVModule leechVOAPlus TP :=
  TwistedPlus.plusModule leechThetaLift

/-- The modes: `u₍ₙ₎ x = Y^T(u)₍2n/2₎ x` for `u ∈ V_Λ^+`, `x ∈ TP`. -/
theorem mode_plusModule (u : (orbifold (Subgroup.zpowers leechTheta)).carrier) (n : ℤ) (x : TP) :
    ((mode (plusModule.YM u) n x : TP) : Tw) = leechTwistedModule.YM u.1 (2 * n) x :=
  TwistedPlus.mode_plusModule leechThetaLift u n x

/-- The odd fractional modes of `u ∈ V_Λ^+` vanish on the whole twisted sector. -/
theorem YM_odd_eq_zero_of_plus (u : (orbifold (Subgroup.zpowers leechTheta)).carrier) (n : ℤ) :
    leechTwistedModule.YM u.1 (2 * n + 1) = 0 :=
  YM_odd_eq_zero (fixed_of_mem u.2) n

/-- **The module grading is the M7 grading**: `TP_q = twFixed ⊓ twWeight q`. -/
theorem map_plusModule_weight (q : ℚ) :
    (plusModule.weight (q : ℂ)).map TP.subtype = twFixed 24 leechT ⊓ twWeight 24 leechT q := by
  change (plusWeight leechThetaLift (q : ℂ)).map TP.subtype = _
  rw [map_plusWeight, leechTwistedModule_weight, weightLT_ratCast]
  rfl

theorem finrank_plusModule_weight (q : ℚ) :
    finrank ℂ (plusModule.weight (q : ℂ))
      = finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT q : Submodule ℂ Tw) := by
  rw [← map_plusModule_weight, LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective TP.subtype (Submodule.injective_subtype _) _)]

/-- **Integer weights `≥ 2` only**: a nonzero weight space of `TP` sits at `α = n ∈ ℤ`,
`n ≥ 2`. -/
theorem plusModule_weight_ne_bot {α : ℂ} (h : plusModule.weight α ≠ ⊥) :
    ∃ n : ℤ, α = n ∧ 2 ≤ n := by
  have hmap : twFixed 24 leechT ⊓ weightLT 24 leechT α ≠ ⊥ := by
    intro h0
    apply h
    have hm : (plusWeight leechThetaLift α).map TP.subtype = ⊥ := by
      rw [map_plusWeight, leechTwistedModule_weight]; exact h0
    exact Submodule.map_injective_of_injective (Submodule.injective_subtype _)
      (by change Submodule.map TP.subtype (plusWeight leechThetaLift α) = _
          rw [hm, Submodule.map_bot])
  by_cases hα : ∃ d : ℕ, ((levelT 24 d : ℚ) : ℂ) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [weightLT_level] at hmap
    rcases Nat.even_or_odd d with hd | ⟨k, rfl⟩
    · exact absurd (by rw [inf_comm]; exact twGrading_inf_twFixed hd) hmap
    · refine ⟨(k : ℤ) + 2, ?_, by omega⟩
      rw [levelT_24_odd]
      push_cast
      ring
  · push Not at hα
    exact absurd (by rw [weightLT_eq_bot 24 leechT hα, inf_bot_eq]) hmap

theorem plusModule_weight_eq_bot_of_re_lt_two {α : ℂ} (hα : α.re < 2) :
    plusModule.weight α = ⊥ := by
  by_contra h
  obtain ⟨n, rfl, hn⟩ := plusModule_weight_ne_bot h
  simp only [Complex.intCast_re] at hα
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **`dim TP₂ = 24 · 4096 = 98304`.** -/
theorem finrank_plusModule_weight_two : finrank ℂ (plusModule.weight 2) = 98304 := by
  have h := finrank_plusModule_weight 2
  rw [show ((2 : ℚ) : ℂ) = (2 : ℂ) by norm_num] at h
  rw [h, leechTwisted_finrank_fixed_two]

/-- **The graded dimension of `V_Λ^+ ⊕ TP` is `J`**: for every `n`,
`dim (V_Λ^+)_n + dim TP_n = [qⁿ](q·J)`, with `TP` the `V_Λ^+`-module `plusModule`. -/
theorem finrank_plusModule_eq_coeff_JShift (n : ℕ) :
    ((finrank ℂ (leechVOAPlus.grading (n : ℤ))
      + finrank ℂ (plusModule.weight ((n : ℤ) : ℂ)) : ℕ) : ℂ)
      = PowerSeries.coeff n JShift := by
  have h := finrank_plusModule_weight (((n : ℤ) : ℚ))
  rw [Rat.cast_intCast] at h
  rw [h]
  exact finrank_sectors_eq_coeff_JShift n

end VOA.Moonshine
