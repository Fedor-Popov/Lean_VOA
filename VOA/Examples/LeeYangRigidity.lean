/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LeeYangSingular
import VOA.Examples.VirasoroInstance
import VOA.Core.RigidityBridge

/-!
# The Lee–Yang model instantiates the rigidity bridge

`Core.RigidityBridge` builds, for a general VOA `W`, the triple `(𝒱ₖ, shapForm, shapForm₁)` that
`Core.DeformedForm` consumes, and proves two criteria putting a singular vector into
`radBil (shapForm)`.  This file discharges every hypothesis of the *second* criterion
(`RigidBridge.mem_radBil_of_descendantSpanned`) for `V(-22/5, 0) = virasoroVOA leeYangC`, using
the singular vector derived in `Examples/LeeYangSingular`.

## The general Virasoro facts proved here (§1)

* `virasoroVOA_L_eq_Lop` — `Lₙ` of the VOA instance is the abstract Virasoro mode `Lop c n`.
  (`(virasoroVOA c).L n = mode (Y ω) (n+1) = mode (YomegaVir c) (n+1) = Lop c n`.)
* `gradingVir_one` — `𝒱₁ = 0` for `V(c,0)`: the energy of a creation monomial is `0` (empty word)
  or `≥ 2`, never `1`.
* `virasoroVOA_qp` — hence the `L₁𝒱₁ = 0` hypothesis of `canonicalInvariantForm` is free.
* `descendantSpanned_virasoroVOA` — every weight space of `V(c,0)` is spanned by the vacuum
  and Virasoro descendants, immediately from `negSpanVir_eq_top`: a creation monomial is either
  `|0⟩` or `L₋ₙ₋₂(…)` with `n + 2 ≥ 1`.

All four hold for **arbitrary** central charge `c`.

## The Lee–Yang results (§2)

* `leeYangSingular_isSingular : IsSingularOfWeight (virasoroVOA leeYangC) 4 leeYangSingular` —
  the singular vector of `Examples/LeeYangSingular` packaged in the `Core.SingularVector`
  interface.
* `leeYangSingular_mem_radBil` — **the Lee–Yang singular vector lies in the radical of the
  level-4 Shapovalov form of `V(-22/5,0)`**, unconditionally.
* `shapForm_leeYang_degenerate` — hence that form is degenerate.  This is the Kac-determinant
  statement `det M₄(-22/5) = 0`, obtained without computing a determinant: the singular vector
  *is* the null direction.
* `leeYangSingular_not_liftable` — the bridge, instantiated: for any graded first-order
  deformation `D` of `V(-22/5,0)` whose deformed level-4 self-pairing of the singular vector is
  nonzero, the singular vector admits **no** first-order correction.

## ⚠ Scope, stated loudly

`leeYangSingular_not_liftable` is an **obstruction** statement, not `Deform.IsRigid`.  It says the
relation `s` of the undeformed Shapovalov form does not survive to first order — equivalently the
family is not flat at level 4.  It does **not** say that `D` is a coboundary, and nothing here
claims that.  See the `Core.RigidityBridge` docstring.

Its hypothesis `hself` is a genuine condition on `D` and is *not* discharged here: computing
`s¹₍₇₎s` requires an explicit `Y₁`, which this repository does not yet have for any nonzero
deformation of `V(c,0)`.  The theorem is stated with `hself` as an explicit named hypothesis
precisely so that this is visible.

## Status
No `sorry`, no `admit`, no `native_decide`, no new axiom;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on every declaration (in particular
`VOA.pbw` is *not* used — `negSpanVir_eq_top` and `vacVec_ne_zero` are both `pbw`-free).
-/

namespace VOA

open SingVec RigidBridge Deform

namespace VirModule

variable (c : ℂ)

/-! ## §1  General facts about `V(c,0)` as a VOA -/

/-- **The VOA's Virasoro modes are the abstract ones**: `Lₙ = Lop c n`.

`(virasoroVOA c).L n = mode (Y ω) (n+1)`, and `Y ω = YomegaVir c` (`virYA_omega`) whose `m`-th
mode is `Lop c (m-1)` (`mode_YomegaVir`). -/
theorem virasoroVOA_L_eq_Lop (n : ℤ) : (virasoroVOA c).L n = Lop c n := by
  change mode (virYA c (omegaVir c)) (n + 1) = Lop c n
  rw [virYA_omega, mode_YomegaVir, show (n + 1 - 1 : ℤ) = n from by ring]

/-- **`V(c,0)` has no weight-one states**: `𝒱₁ = 0`.

`gradingVir c 1` is spanned by the creation monomials of energy `1`, and there are none — the
empty word has energy `0` and every nonempty word has energy `≥ 2` (each mode is `L₋ᵢ₋₂`). -/
theorem gradingVir_one : gradingVir c 1 = ⊥ := by
  rw [gradingVir, Submodule.span_eq_bot]
  rintro x ⟨ws, hen, rfl⟩
  exfalso
  cases ws with
  | nil => simp at hen
  | cons i rest => rw [energyVir_cons] at hen; omega

/-- The quasi-primary hypothesis `L₁𝒱₁ = 0` of `canonicalInvariantForm` holds vacuously for
`V(c,0)`, since `𝒱₁ = 0`. -/
theorem virasoroVOA_qp :
    ∀ v, v ∈ (virasoroVOA c).grading 1 → (virasoroVOA c).L 1 v = 0 := by
  intro v hv
  have hv' : v ∈ gradingVir c 1 := hv
  rw [gradingVir_one c, Submodule.mem_bot] at hv'
  rw [hv', map_zero]

/-- **Every weight space of `V(c,0)` is spanned by the vacuum and Virasoro descendants.**

`negSpanVir_eq_top` says the creation monomials `L₋ₙ₁₋₂⋯L₋ₙᵣ₋₂|0⟩` span everything; each of them
is either `|0⟩` (the empty word) or of the form `L₋ₘ z` with `m = n₁ + 2 ≥ 1`. -/
theorem descendantSpanned_virasoroVOA (k : ℤ) : DescendantSpanned (virasoroVOA c) k := by
  refine descendantSpanned_of_span_eq_top _ _ (le_antisymm le_top ?_)
  rw [← negSpanVir_eq_top c, negSpanVir]
  refine Submodule.span_mono ?_
  rintro x ⟨ws, rfl⟩
  cases ws with
  | nil => exact Set.mem_insert _ _
  | cons n rest =>
      refine Set.mem_insert_of_mem _ ⟨(n : ℤ) + 2, negWordVir c rest, by omega, ?_⟩
      rw [negWordVir_cons, virasoroVOA_L_eq_Lop,
        show (-((n : ℤ) + 2)) = -(n : ℤ) - 2 from by ring]

end VirModule

namespace LeeYang

open VOA.VirModule

/-! ## §2  The Lee–Yang instantiation -/

/-- The vacuum of `V(-22/5,0)` is nonzero (`vacVec_ne_zero`, which is `pbw`-free). -/
theorem leeYang_vacuum_ne_zero : (virasoroVOA leeYangC).vacuum ≠ 0 := vacVec_ne_zero leeYangC

/-- The Lee–Yang vector, packaged in the `Core.SingularVector` interface: it is a **Virasoro**
singular vector of weight `4` for the VOA `V(-22/5,0)`.

(Strong singularity — `u₍ₙ₎s = 0` for every field `u` — is *not* claimed; it is exactly what
`Core.SingularVector` records as missing.  The descendant-spanning criterion of
`Core.RigidityBridge` is designed to avoid needing it.) -/
theorem leeYangSingular_isSingular :
    IsSingularOfWeight (virasoroVOA leeYangC) 4 leeYangSingular where
  ne_zero := leeYangSingular_ne_zero
  weight_pos := by norm_num
  homogeneous := leeYangSingular_mem_grading
  annihilated := fun n hn => by
    rw [virasoroVOA_L_eq_Lop]
    exact leeYangSingular_annihilated (by omega)

/-- The Lee–Yang singular vector viewed inside the weight-4 space of `V(-22/5,0)`. -/
noncomputable def leeYangSing4 : (virasoroVOA leeYangC).grading 4 :=
  ⟨leeYangSingular, leeYangSingular_isSingular.homogeneous⟩

@[simp] theorem leeYangSing4_coe :
    (leeYangSing4 : VirUniv leeYangC) = leeYangSingular := rfl

/-- **The Lee–Yang singular vector lies in the radical of the level-4 Shapovalov form of
`V(-22/5,0)`** — unconditionally.

Every hypothesis of `RigidBridge.mem_radBil_of_descendantSpanned` is discharged: the vacuum is
nonzero, `𝒱₁ = 0` supplies the quasi-primary condition, `s` is Virasoro-singular of weight `4`,
and `𝒱₄` is spanned by the vacuum and Virasoro descendants. -/
theorem leeYangSingular_mem_radBil :
    leeYangSing4 ∈ DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) :=
  mem_radBil_of_descendantSpanned leeYang_vacuum_ne_zero (virasoroVOA_qp leeYangC)
    leeYangSingular_isSingular (descendantSpanned_virasoroVOA leeYangC 4)

/-- Concretely: `s₍₇₎x = 0` for every weight-4 state `x` — the level-4 Shapovalov pairing against
the singular vector vanishes identically. -/
theorem leeYangSingular_shapovalov_zero (x : VirUniv leeYangC)
    (hx : x ∈ (virasoroVOA leeYangC).grading 4) :
    (virasoroVOA leeYangC).smul leeYangSingular 7 x = 0 := by
  have h := DefForm.mem_radBil.mp leeYangSingular_mem_radBil ⟨x, hx⟩
  rw [shapForm_eq_zero_iff] at h
  rw [show (7 : ℤ) = 2 * 4 - 1 from by norm_num]
  exact h

/-- **The level-4 Shapovalov form of `V(-22/5,0)` is degenerate.**

This is the Kac-determinant statement `det M₄(c = -22/5) = 0`, obtained with no determinant: the
singular vector exhibits the null direction. -/
theorem shapForm_leeYang_degenerate :
    ¬ LinearMap.Nondegenerate (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) := by
  intro hnd
  have hbot := DefForm.radBil_eq_bot_of_nondegenerate hnd
  have hmem := leeYangSingular_mem_radBil
  rw [hbot, Submodule.mem_bot] at hmem
  exact leeYangSingular_ne_zero (congrArg Subtype.val hmem)

/-- The radical of the level-4 Shapovalov form is nonzero. -/
theorem radBil_shapForm_leeYang_ne_bot :
    DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) ≠ ⊥ := by
  intro h
  have hmem := leeYangSingular_mem_radBil
  rw [h, Submodule.mem_bot] at hmem
  exact leeYangSingular_ne_zero (congrArg Subtype.val hmem)

/-- **The rigidity bridge, instantiated for Lee–Yang.**

For any graded first-order deformation `D` of `V(-22/5,0)` whose deformed level-4 self-pairing of
the singular vector is nonzero, the singular vector admits **no** first-order correction: the
relation `s` of the undeformed Shapovalov form does not survive to first order.

⚠ This is *not* `Deform.IsRigid (virasoroVOA leeYangC)`, and `hself` is an undischarged named
hypothesis — see the file docstring. -/
theorem leeYangSingular_not_liftable (D : FirstOrderDeformation (virasoroVOA leeYangC))
    (hD : D.IsGraded)
    (hself : shapForm₁ D hD leeYang_vacuum_ne_zero 4 leeYangSing4 leeYangSing4 ≠ 0) :
    ¬ ∃ s₁ : (virasoroVOA leeYangC).grading 4,
        ∀ w : (virasoroVOA leeYangC).grading 4,
          shapForm₁ D hD leeYang_vacuum_ne_zero 4 leeYangSing4 w
            + shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4 s₁ w = 0 :=
  not_liftable_of_self_pairing_ne_zero leeYang_vacuum_ne_zero D hD
    leeYangSingular_mem_radBil hself

/-- The Jantzen-layer restatement: the singular vector is in `F₁` but not in `F₂`, so
`F₂ ⊊ F₁` for the deformed level-4 form. -/
theorem leeYang_F2_lt_F1 (D : FirstOrderDeformation (virasoroVOA leeYangC)) (hD : D.IsGraded)
    (hself : shapForm₁ D hD leeYang_vacuum_ne_zero 4 leeYangSing4 leeYangSing4 ≠ 0) :
    DefForm.F2 (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4)
        (shapForm₁ D hD leeYang_vacuum_ne_zero 4)
      < DefForm.F1 (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) :=
  F2_lt_F1_of_self_pairing_ne_zero leeYang_vacuum_ne_zero D hD leeYangSingular_mem_radBil hself

end LeeYang

end VOA
