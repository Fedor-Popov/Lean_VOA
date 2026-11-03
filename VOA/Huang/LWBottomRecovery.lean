/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.BottomRecovery
import VOA.Modules.ZhuVermaAnArchAModScope
import VOA.Modules.ZhuAlgebra

/-!
# `AllBottomRecovers` holds for every VOA

`Modules/ZhuVermaAnArchLeaf3.lean` isolates `BottomRecovers P` ("a mode word returning a bottom
vector to the bottom acts through the Zhu algebra") as a key hypothesis, with `AllBottomRecovers`
its
universal form. Here it is proved for every
lowest-weight module, by viewing `P` as an admissible module with levels `P(k) = P_{h+k}`
(`lwAdmissible`) and applying the general bottom recovery of `Huang/BottomRecovery.lean`.

## Main results

* `lwAdmissible P` — the admissible structure of a lowest-weight module;
* `bottomRecovers P` and `allBottomRecovers W` — unconditional;
* `isSimpleAMod_toAMod_of_irreducible` — the bottom of an irreducible lowest-weight module is a
  simple `A(V)`-module, with no semisimplicity and no PBW datum.

`#print axioms`: Lean's three.
-/

namespace VOA.Huang.LWBottomRecovery

open VOA VOA.Huang.BottomRecovery

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section LW

variable (P : LWModule W)

/-- The levels of a lowest-weight module: `P(k) = P_{h+k}` for `k ≥ 0`. -/
noncomputable def lwLev (k : ℤ) : Submodule ℂ P.carrier :=
  if 0 ≤ k then P.isMod.weight (P.h + (k : ℂ)) else ⊥

theorem lwLev_zero : lwLev P 0 = P.isMod.weight P.h := by simp [lwLev]

/-- A weight `h + m` with `m < 0` carries nothing. -/
theorem weight_neg_eq_bot {m : ℤ} (hm : m < 0) : P.isMod.weight (P.h + (m : ℂ)) = ⊥ := by
  by_contra hne
  obtain ⟨n, hn⟩ := P.isLow _ hne
  have : (m : ℂ) = (n : ℂ) := by linear_combination hn
  have : m = (n : ℤ) := by exact_mod_cast this
  omega

theorem lwLev_eq_weight (k : ℤ) : lwLev P k = P.isMod.weight (P.h + (k : ℂ)) := by
  unfold lwLev
  split_ifs with hk
  · rfl
  · exact (weight_neg_eq_bot P (by omega)).symm

theorem lwLev_isInternal : DirectSum.IsInternal (lwLev P) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hw := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 P.isMod.isInternal
  constructor
  · refine iSupIndep_def.mpr (fun k => ?_)
    rw [lwLev_eq_weight]
    have hle : (⨆ (j : ℤ) (_ : j ≠ k), lwLev P j)
        ≤ ⨆ (α : ℂ) (_ : α ≠ P.h + (k : ℂ)), P.isMod.weight α := by
      refine iSup₂_le (fun j hj => ?_)
      rw [lwLev_eq_weight]
      refine le_iSup₂_of_le (P.h + (j : ℂ)) (fun h => hj ?_) le_rfl
      have : (j : ℂ) = (k : ℂ) := by linear_combination h
      exact_mod_cast this
    exact (iSupIndep_def.mp hw.1 _).mono_right hle
  · rw [eq_top_iff, ← hw.2]
    refine iSup_le (fun α => ?_)
    by_cases hα : P.isMod.weight α = ⊥
    · rw [hα]; exact bot_le
    · obtain ⟨n, rfl⟩ := P.isLow α hα
      have : P.isMod.weight (P.h + (n : ℂ)) = lwLev P (n : ℤ) := by
        rw [lwLev_eq_weight]; push_cast; rfl
      rw [this]
      exact le_iSup (lwLev P) (n : ℤ)

/-- **A lowest-weight module is admissible**, with level `0` its bottom `P_h`. -/
noncomputable def lwAdmissible : AdmissibleModule W P.carrier where
  toWeakModule := P.isMod.toWeakModule
  lev := lwLev P
  lev_eq_bot_of_neg k hk := by unfold lwLev; rw [if_neg (by omega)]
  isInternal := lwLev_isInternal P
  act_lev := by
    intro w p k a ha x hx
    rw [lwLev_eq_weight] at hx ⊢
    have := mode_mem_weight P.isMod ha hx p
    convert this using 2
    push_cast; ring

@[simp] theorem lwAdmissible_lev : (lwAdmissible P).lev = lwLev P := rfl

/-- **Bottom recovery for every lowest-weight module.** -/
theorem bottomRecovers : BottomRecovers P := by
  intro S
  let N := lwAdmissible P
  let S' : Submodule ℂ P.carrier := S.toBottomImage
  have hS0 : S' ≤ N.lev 0 := by
    rintro _ ⟨y, _, rfl⟩
    rw [lwAdmissible_lev, lwLev_zero]; exact y.2
  have hSo : ∀ ⦃a : 𝒱⦄ ⦃w : ℤ⦄, a ∈ W.grading w → ∀ ⦃x : P.carrier⦄, x ∈ S' →
      N.toWeakModule.act a (w - 1) x ∈ S' := by
    rintro a w ha _ ⟨y, hy, rfl⟩
    refine ⟨P.toAMod.ρ (VOA.mk W a) y, S.ρ_mem _ hy, ?_⟩
    change ((actA P.isMod P.isLow (VOA.mk W a) y : P.isMod.weight P.h) : P.carrier) = _
    rw [actA_mk_apply_coe, oMod_homogeneous P.isMod ha]
    rfl
  intro x hx
  let x' : P.isMod.weight P.h := x
  -- `x` lies in the generated submodule, which sits inside `genSub S'`.
  have hgen : S.genVSubmodule.carrier ≤ (genSub (N := N) S').carrier := by
    intro z hz
    simp only [AModSubmodule.genVSubmodule, Submodule.mem_iInf] at hz
    exact hz ⟨genSub (N := N) S', le_genSub S'⟩
  have hx' : (x' : P.carrier) ∈ (genSub (N := N) S').carrier := hgen hx
  have hx0 : (x' : P.carrier) ∈ N.lev 0 := by
    rw [lwAdmissible_lev, lwLev_zero]; exact x'.2
  obtain ⟨y, hy, hyx⟩ := genSub_le_bottom S' hS0 hSo hx' hx0
  have : y = x' := Subtype.ext hyx
  rw [this] at hy
  exact hy

/-- `AllBottomRecovers` holds for every vertex operator algebra. -/
theorem allBottomRecovers (W : VertexOperatorAlgebra 𝒱) : AllBottomRecovers W :=
  fun P => bottomRecovers P

/-- **The bottom of an irreducible lowest-weight module is a simple `A(V)`-module**, with no
semisimplicity hypothesis and no PBW datum (compare `isSimpleAMod_of_irreducible_of_semisimple`). -/
theorem isSimpleAMod_toAMod_of_irreducible (hP : P.IsIrreducibleLW) : IsSimpleAMod P.toAMod :=
  isSimpleAMod_of_bottomRecovers P hP (bottomRecovers P)

end LW

end VOA.Huang.LWBottomRecovery
