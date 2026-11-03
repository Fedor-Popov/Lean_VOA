/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationGraded
import VOA.Examples.VirasoroInstance
import VOA.Examples.LeeYangSingular
import Mathlib.Algebra.DirectSum.Module

/-!
# The first-order deformation space of `V(c,0)` at low tridegrees

`Core.DeformationGraded` reduces first-order deformation theory to finite linear algebra: at each
tridegree `(a,b,d)` the mode is *determined*, `n = a+b−d−1` (`Deform.gradedMode`), the cochain
space `Deform.GradedCochain W a b d = Hom(𝒱ₐ, Hom(𝒱_b, 𝒱_d))` is finite-dimensional, and

    `Deform.DeformationSpaceAt W a b d  =  gradedCocyclesAt W a b d ⧸ gradedCoboundariesAt W a b d`.

This file **runs that computation** for `W = virasoroVOA c`, at the family of tridegrees
`(2,2,d)` — the smallest ones where anything can happen — and reports the outcome.

## Why `(2,2,·)` is where the computation starts, and not lower

`V(c,0)` has `𝒱₀ = ℂ·𝟙`, `𝒱₁ = 0`, `𝒱₂ = ℂ·ω`, `𝒱₃ = ℂ·L₋₃𝟙`, `𝒱₄ = span{L₋₂²𝟙, L₋₄𝟙}`
(`gradingVir_zero`, `gradingVir_one_eq_bot`, `gradingVir_two`, `gradingVir_three`,
`LeeYang.gradingVir_four`).  Every tridegree below `(2,2,·)` is **vacuous, and for a trivial
reason** — this is important information and it is proved, not assumed:

* source grade `0`: the order-`t` vacuum axiom `Y₁(𝟙,z) = 0` forces
  `gradedCocyclesAt W 0 b d = ⊥` (`gradedCocyclesAt_source_zero`, for *every* VOA);
* any tridegree touching grade `1`: `𝒱₁ = 0`, so the cochain space itself is `0`
  (`gradedCoboundariesAt_eq_top_of_target_bot`, `deformationSpaceAt_two_two_one_trivial`).

So `(2,2,d)` really is the first place a first-order deformation of `V(c,0)` can show up, and
there the cochain space is `𝒱_d` itself (`gradedCochain_two_two_ext`,
`finrank_gradedCochain_two_two`), because `dim 𝒱₂ = 1`.

## Method (the repo's `Examples/LeeYangSingular` template, one degree up)

The cocycle side is *not* computed by solving the Jacobi system; it does not have to be.  The
whole quotient is killed as soon as the **coboundary** side already fills the cochain space, and
the coboundary side is a finite, explicit image.  Two families of *global* grade-preserving field
redefinitions `φ` (`φ𝟙 = 0`) are constructed and their `(2,2,d)` components computed in closed
form:

1. the **scaling** redefinition `φ = L₀` (`scalGraded`).  On homogeneous vectors
   `δL₀(u,n,v) = (n+1)·u₍ₙ₎v`, so at `(a,b,d)` it is the scalar `a+b−d` times the undeformed
   product (`gradedComponent_scal_apply`).  At `(2,2,d)` this is `(4−d)·L_{2−d}ω`.
2. the **single-block** redefinition `φ = ψ` on `𝒱ₖ` and `0` elsewhere (`blockMap`, built from
   the structure field `W.isInternal`), legal for `k ≠ 0`.  When the *source* grades both differ
   from `k` it contributes `δφ(u,n,v) = −ψ(u₍ₙ₎v)` (`gradedComponent_block_apply`), so at
   `(2,2,k)` with `k ∉ {0,2}` it sweeps out **all** of `𝒱ₖ` as soon as `ω₍₃₋ₖ₎ω = L_{2−k}ω ≠ 0`.

Every structure constant needed is a concrete function of `c`, from `Lop_bracket`:
`L₂ω = (c/2)𝟙`, `L₀ω = 2ω`, `L₋₁ω = L₋₃𝟙`, `L₋₂ω = L₋₂²𝟙`
(`Lop_two_omega`, `Lop_zero_omega`, `Lop_negOne_omega`, `Lop_negTwo_omega`).

## The outcome, tridegree by tridegree

| tridegree | mode `n` | `dim` cochains | coboundaries | deformation space |
|---|---|---|---|---|
| `(0,b,d)` | any | `dim 𝒱_b · dim 𝒱_d` | — (cocycles are `⊥`) | `0`, trivially |
| `(2,2,0)` | `3` | `1` | `⊤` iff `c ≠ 0` | `0` if `c ≠ 0`; `= cocycles` at `c = 0` |
| `(2,2,1)` | `2` | `0` | `⊤` | `0`, trivially (`𝒱₁ = 0`) |
| `(2,2,2)` | `1` | `1` | `⊤`, every `c` | `0` |
| `(2,2,3)` | `0` | `1` | `⊤`, every `c` | `0` |
| `(2,2,4)` | `−1` | `2` | `⊤`, every `c` | `0` |

## The `c`-dependence: the rank drops exactly at `c = 0`

The only place `c` enters the `(2,2,·)` computation is the central term `ω₍₃₎ω = (c/2)𝟙` at
`(2,2,0)`.  There the coboundary map is the `1×1` matrix `λ ↦ λc`, and:

* `c ≠ 0`: `gradedCoboundariesAt (virasoroVOA c) 2 2 0 = ⊤` — the *central-charge* direction is
  itself a field redefinition at this tridegree (rescaling `ω`), so the quotient vanishes;
* `c = 0`: `gradedCoboundariesAt (virasoroVOA 0) 2 2 0 = ⊥` — **the rank drops to `0`**, proved,
  and the deformation space there *is* the cocycle space
  (`gradedCoboundariesIn_two_two_zero_eq_bot`).

This makes `(2,2,0)` at `c = 0` an obstruction detector:
`deformationSpaceAt_two_two_zero_ne_zero_of_witness` says any graded first-order deformation of
`V(0,0)` with `ω¹₍₃₎ω ≠ 0` has a **nonzero** class, which by
`Deform.gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid` would disprove
`Deform.IsRigid (virasoroVOA 0)`.

⚠ This is `c = 0`, **not** a minimal model.  Nothing here detects `c = 1 − 6(p−q)²/(pq)`: at the
`(2,2,·)` tridegrees the only `c`-dependent structure constant is the central term, so the only
special value visible is its zero.  Minimal-model values would first have to show up where a
*singular vector* enters, i.e. at tridegrees whose target is a degenerate weight space — the
`(4,4,·)` block for Lee–Yang, matching `Examples/LeeYangSingular` and `Examples/LeeYangRigidity`.
That is the next computation, not this one.

## ⚠ A concrete instance of the `Deform.GradedToGlobalRigidity` obstruction

The `(2,2,·)` family also makes the gap recorded in `Deform.GradedToGlobalRigidity` *visible*,
which is worth stating because it is easy to over-read the vanishing results above.

Spell out the coboundary at `(2,2,d)` for a general grade-preserving `φ` with `φ𝟙 = 0`.  On
`𝒱₂ = ℂ·ω` such a `φ` is a single scalar, `φω = λω`, and `φ` kills `𝒱₀ = ℂ·𝟙`.  Hence

* at `(2,2,0)` (mode `3`):  `δφ(ω,3,ω) = 2λ·ω₍₃₎ω = λc·𝟙`;
* at `(2,2,2)` (mode `1`):  `δφ(ω,1,ω) = 2λω − 2λω + 2λω = 2λ·ω`.

Now consider the *candidate* deformation `∂_c Y` — differentiating the structure constants of
`V(c,0)` in `c` on the (`c`-independent) underlying graded space.  Its `(2,2,0)` component is
`½·𝟙` and its `(2,2,2)` component is `0` (because `ω₍₁₎ω = 2ω` carries no `c`).  Trivialising it
at `(2,2,0)` forces `λ = 1/(2c)`; trivialising it at `(2,2,2)` forces `λ = 0`.  **Both tridegrees
have vanishing deformation space, yet no single `φ` trivialises the deformation at both.**

That is exactly the failure mode described in `Deform.GradedToGlobalRigidity`: per-tridegree
cokernel vanishing produces one `φ` per tridegree and they need not patch.  So the theorems below
must be read as what they say — `DeformationSpaceAt … = 0` at named tridegrees — and *not* as
evidence for `Deform.IsRigid`.

(⚠ `∂_c Y` is **not** constructed in this file, so the paragraph above is an orientation remark
here, not a theorem.  What *is* proved here is the coboundary computation it is built from.
`∂_c Y` is constructed downstream as `VOA.VirPoly.cDeformation` (`Examples/VirasoroCDefJacobi.lean`),
and `Examples/VirasoroCDefFinal.lean` proves `VOA.VirPoly.not_isRigidGraded_virasoroVOA`.  That
proof goes through the global gauge-line argument of `Examples/VirasoroCDeformation.lean`, not
through the per-tridegree quotients below, so it is consistent with this paragraph.)

## ⚠ Scope, stated honestly

* **What is proved.**  The *coboundary* side is computed exactly at `(2,2,d)` for `d ∈ {0,1,2,3,4}`
  and, conditionally on `L_{2−d}ω ≠ 0`, for every `d ∉ {0,2}`
  (`gradedCoboundariesAt_two_two_eq_top_of_block`).  Wherever it fills the cochain space the
  quotient vanishes — a genuine, fully-proved *partial rigidity* statement.
* **What is not proved.**  The *cocycle* side is never computed: no first-order Jacobi system is
  solved here.  That is not needed for the vanishing statements (a full coboundary space kills the
  quotient whatever the cocycles are), but it means the `c = 0` slot is left as
  `DeformationSpaceAt ≅ gradedCocyclesAt`, with the existence of a witness open.
* **No claim about `Deform.IsRigid (virasoroVOA c)`.**  Vanishing at finitely many tridegrees is
  not rigidity; and even vanishing at *all* tridegrees would not give it — see the obstruction
  recorded in `Deform.GradedToGlobalRigidity`.  The statements below are exactly
  `DeformationSpaceAt … = 0` at the named tridegrees, and nothing more.
* **What the next tridegree needs.**  `(2,2,d)` for `d ≥ 5` needs only `L_{2−d}ω ≠ 0` (the block
  criterion is already general).  `(3,3,·)`, `(2,4,·)`, `(4,4,·)` need a `gradedCochain_two_two_ext`
  analogue for a source space of dimension `> 1` — i.e. the bilinearity bookkeeping over a basis
  of `𝒱₄` — plus the corresponding structure constants `L_n L₋₂²𝟙`.

## Main results

* `gradedCocyclesAt_source_zero` — every source-grade-`0` tridegree is vacuous (any VOA).
* `coboCochain`, `isCoboundary_coboCochain` — `δφ` as an honest element of `Deform.Cochain`.
* `scalGraded`, `gradedComponent_scal_apply` — the scaling redefinition in closed form.
* `blockMap`, `blockMap_gradePreserving`, `gradedComponent_block_apply` — the single-block
  redefinition and its closed form.
* `gradedCochain_two_two_ext` — a `(2,2,d)` cochain is its single value on `(ω,ω)`.
* `gradedCoboundariesAt_two_two_eq_top_of_scal`, `…_of_block` — the two criteria.
* `gradedCoboundariesAt_two_two_zero_eq_top` (`c ≠ 0`) and
  `gradedCoboundariesAt_two_two_zero_eq_bot` (`c = 0`) — the rank drop.
* `deformationSpaceAt_two_two_zero_trivial` (`c ≠ 0`),
  `deformationSpaceAt_two_two_one_trivial`, `deformationSpaceAt_two_two_two_trivial`,
  `deformationSpaceAt_two_two_three_trivial`, `deformationSpaceAt_two_two_four_trivial`.
* `deformationSpaceAt_two_two_zero_ne_zero_of_witness` — the `c = 0` obstruction detector.
* `finrank_gradingVir_zero/one/two/three/four`, `finrank_gradedCochain_two_two` — the
  dimensions (`1, 0, 1, 1, 2`).

## Status
No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axioms;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on all 30 main declarations
(in particular `VOA.pbw` is *not* used).  Imported by the umbrella `VOA/Examples.lean`.

## Dependencies
`Core.DeformationGraded` (the graded cochain/cocycle/coboundary machinery and
`DeformationSpaceAt`), `Examples.VirasoroInstance` (`virasoroVOA c`),
`Examples.LeeYangSingular` (`L2vac_ne_zero`, `L3vac_ne_zero`, `level4_indep`, `gradingVir_four`).
-/

set_option linter.style.longLine false
-- `DeformationSpaceAt` is a quotient of a submodule *of a submodule*, so the instance search
-- for `AddCommGroup ↥(gradedCocyclesAt …)` needs one extra level of pending synthesis.
set_option maxSynthPendingDepth 3

namespace VOA

namespace VirDefLow

open Module (End)
open Deform
open VOA.VirModule

universe u

/-! ## §0  Pointwise access to `FormalDist`, and the coboundary cochain `δφ` -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `FormalDist 𝒲` is an opaque synonym for `ℤ → 𝒲`, so `Pi.add_apply` does not fire; this
records that its addition is pointwise. -/
@[simp] theorem fdist_add_apply {𝒲 : Type*} [AddCommGroup 𝒲] (f g : FormalDist 𝒲) (k : ℤ) :
    (f + g) k = f k + g k := rfl

/-- Scalar multiplication on `FormalDist` is pointwise. -/
@[simp] theorem fdist_smul_apply {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] (r : ℂ)
    (f : FormalDist 𝒲) (k : ℤ) : (r • f) k = r • f k := rfl

/-- The **coboundary cochain** `δφ` attached to a linear map `φ : 𝒱 →ₗ[ℂ] 𝒱`:
`(δφ)(u,z) := Y(φu,z) − φ∘Y(u,z) + Y(u,z)∘φ`, coefficient by coefficient.  This is the
"image of the field redefinitions" side of the deformation complex, packaged as an honest
element of `Deform.Cochain 𝒱`. -/
def coboCochain (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) : Deform.Cochain 𝒱 where
  toFun u := fun k => W.Y (φ u) k - φ * (W.Y u k) + (W.Y u k) * φ
  map_add' u₁ u₂ := by
    refine FormalDist.ext fun k => ?_
    change W.Y (φ (u₁ + u₂)) k - φ * (W.Y (u₁ + u₂) k) + (W.Y (u₁ + u₂) k) * φ
      = (fun k => W.Y (φ u₁) k - φ * (W.Y u₁ k) + (W.Y u₁ k) * φ) k
        + (fun k => W.Y (φ u₂) k - φ * (W.Y u₂ k) + (W.Y u₂ k) * φ) k
    simp only [map_add, fdist_add_apply, mul_add, add_mul]
    abel
  map_smul' r u := by
    refine FormalDist.ext fun k => ?_
    change W.Y (φ (r • u)) k - φ * (W.Y (r • u) k) + (W.Y (r • u) k) * φ
      = r • (W.Y (φ u) k - φ * (W.Y u k) + (W.Y u k) * φ)
    simp only [map_smul, fdist_smul_apply, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub]

/-- The modes of `δφ` are the coboundary formula `(φu)₍ₙ₎v − φ(u₍ₙ₎v) + u₍ₙ₎(φv)`. -/
theorem cmode_coboCochain (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) (u : 𝒱) (n : ℤ)
    (v : 𝒱) :
    Deform.cmode (coboCochain W φ) u n v
      = W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v) := rfl

/-- `δφ` **is** a coboundary, for any grading-preserving `φ` killing the vacuum. -/
theorem isCoboundary_coboCochain (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) :
    Deform.IsCoboundary W (coboCochain W φ) :=
  ⟨φ, hφ0, hφg, fun u n v => cmode_coboCochain W φ u n v⟩

/-- `δφ` is a graded cochain (a grade-preserving `φ` produces a grade-preserving `δφ`). -/
theorem coboCochain_mem_gradedCochains (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) :
    coboCochain W φ ∈ Deform.gradedCochains W :=
  Deform.coboundaries_le_gradedCochains W (isCoboundary_coboCochain W hφ0 hφg)

/-- `δφ`, packaged as an element of the graded cochains. -/
def coboGraded (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) :
    ↥(Deform.gradedCochains W) :=
  ⟨coboCochain W φ, coboCochain_mem_gradedCochains W hφ0 hφg⟩

/-- `δφ` lies in the graded coboundaries. -/
theorem coboGraded_mem (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) :
    coboGraded W hφ0 hφg ∈ Deform.gradedCoboundaries W :=
  isCoboundary_coboCochain W hφ0 hφg

/-- The `(a,b,d)`-component of `δφ` lies in the coboundary space at that tridegree.  This is
the workhorse: every explicit field redefinition produces an explicit element of
`gradedCoboundariesAt`. -/
theorem gradedComponent_coboGraded_mem (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) (a b d : ℤ) :
    Deform.gradedComponent W a b d (coboGraded W hφ0 hφg)
      ∈ Deform.gradedCoboundariesAt W a b d :=
  Submodule.mem_map_of_mem (coboGraded_mem W hφ0 hφg)

/-- The component of `δφ`, evaluated: `(u,v) ↦ (φu)₍ₙ₎v − φ(u₍ₙ₎v) + u₍ₙ₎(φv)` with
`n = a + b − d − 1`. -/
@[simp] theorem gradedComponent_coboGraded_apply (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) (a b d : ℤ)
    (u : ↥(W.grading a)) (v : ↥(W.grading b)) :
    ((Deform.gradedComponent W a b d (coboGraded W hφ0 hφg) u v : ↥(W.grading d)) : 𝒱)
      = W.smul (φ (u : 𝒱)) (Deform.gradedMode a b d) (v : 𝒱)
        - φ (W.smul (u : 𝒱) (Deform.gradedMode a b d) (v : 𝒱))
        + W.smul (u : 𝒱) (Deform.gradedMode a b d) (φ (v : 𝒱)) := rfl

/-! ## §1  A vanishing quotient from a full coboundary space -/

/-- If the coboundary space fills the whole cochain space at a tridegree, the deformation space
there vanishes. -/
theorem deformationSpaceAt_subsingleton_of_coboundariesAt_top (W : VertexOperatorAlgebra 𝒱)
    {a b d : ℤ} (h : Deform.gradedCoboundariesAt W a b d = ⊤) :
    ∀ z : Deform.DeformationSpaceAt W a b d, z = 0 := by
  intro z
  refine Quotient.inductionOn' z fun f => ?_
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  change (f : Deform.GradedCochain W a b d) ∈ Deform.gradedCoboundariesAt W a b d
  rw [h]
  exact Submodule.mem_top

/-- If the cocycle space at a tridegree is zero, the deformation space there vanishes. -/
theorem deformationSpaceAt_subsingleton_of_cocyclesAt_bot (W : VertexOperatorAlgebra 𝒱)
    {a b d : ℤ} (h : Deform.gradedCocyclesAt W a b d = ⊥) :
    ∀ z : Deform.DeformationSpaceAt W a b d, z = 0 := by
  intro z
  refine Quotient.inductionOn' z fun f => ?_
  have hf : (f : Deform.GradedCochain W a b d) = 0 :=
    (Submodule.eq_bot_iff _).mp h _ f.2
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  change (f : Deform.GradedCochain W a b d) ∈ Deform.gradedCoboundariesAt W a b d
  rw [hf]
  exact Submodule.zero_mem _


/-! ## §2  The low graded pieces of `V(c,0)` and the products `ω₍ₙ₎ω` -/

variable (c : ℂ)

/-- The only creation word of energy `2` is `[0]` (each entry contributes `≥ 2`). -/
theorem energyVir_eq_two {ws : List ℕ} (h : energyVir ws = 2) : ws = [0] := by
  match ws with
  | [] => exact absurd h (by decide)
  | [i] =>
      rw [energyVir_cons, energyVir_nil] at h
      have hi : i = 0 := by omega
      rw [hi]
  | (i :: j :: rest) =>
      exfalso
      rw [energyVir_cons, energyVir_cons] at h
      omega

/-- The one-letter creation word indexed by zero is the conformal vector L at index −2 applied to
the vacuum. This identifies the abstract word notation with the generating state. -/
theorem negWordVir_zero_word : negWordVir c [0] = omegaVir c := by
  have h : (-((0 : ℕ) : ℤ) - 2) = -2 := by norm_num
  rw [negWordVir_cons, negWordVir_nil, h, omegaVir]

/-- **The level-2 subspace is the line spanned by `ω`**: `𝒱₂ = ℂ·L₋₂|0⟩`. -/
theorem gradingVir_two : gradingVir c 2 = ℂ ∙ omegaVir c := by
  apply le_antisymm
  · rw [gradingVir, Submodule.span_le]
    rintro x ⟨ws, hen, rfl⟩
    have h2 : energyVir ws = 2 := by exact_mod_cast hen
    rw [energyVir_eq_two h2, negWordVir_zero_word]
    exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_singleton_le_iff_mem]
    exact omegaVir_mem_gradingVir_two c

/-- **`ω ≠ 0` for every central charge** — `ω = L₋₂|0⟩ = L2vac c`, and `L2vac_ne_zero` is
unconditional (proved `pbw`-free through the linear-dilaton free-boson realization). -/
theorem omegaVir_ne_zero_all : omegaVir c ≠ 0 := LeeYang.L2vac_ne_zero c

/-- The modes of `ω` in the VOA `V(c,0)` are the abstract Virasoro modes: `ω₍ₙ₎ = L_{n−1}`. -/
theorem smulVir_omega (n : ℤ) (v : VirUniv c) :
    (virasoroVOA c).smul (omegaVir c) n v = Lop c (n - 1) v := by
  rw [PreVertexAlgebra.smul_def]
  change mode (virYA c (omegaVir c)) n v = _
  rw [virYA_omega, mode_YomegaVir]

/-- `L₂ω = (c/2)|0⟩` — the central term.  This is the single structure constant carrying `c`. -/
theorem Lop_two_omega : Lop c 2 (omegaVir c) = (c / 2) • vacVec c := by
  have key := congrArg (fun (T : End ℂ (VirUniv c)) => T (vacVec c)) (Lop_bracket c 2 (-2))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at key
  rw [Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 2), map_zero, sub_zero,
    show ((2 : ℤ) + -2) = 0 from by norm_num, Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 0),
    smul_zero, zero_add, if_pos rfl,
    show ((2 : ℤ) : ℂ) ^ 3 - ((2 : ℤ) : ℂ) = 6 from by norm_num] at key
  rw [omegaVir, key]
  congr 1
  ring

/-- `L₀ω = 2ω` — `ω` has conformal weight `2`. -/
theorem Lop_zero_omega : Lop c 0 (omegaVir c) = (2 : ℂ) • omegaVir c := by
  have h := L0_grading_gen c (omegaVir c) (omegaVir_mem_gradingVir_two c)
  rw [h]
  norm_num

/-- `L₋₁ω = L₋₃|0⟩`. -/
theorem Lop_negOne_omega : Lop c (-1) (omegaVir c) = LeeYang.L3vac c := by
  have key := congrArg (fun (T : End ℂ (VirUniv c)) => T (vacVec c)) (Lop_bracket c (-1) (-2))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at key
  rw [Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ -1), map_zero, sub_zero,
    if_neg (by norm_num : ¬((-1 : ℤ) + -2 = 0)), zero_smul, add_zero,
    show ((-1 : ℤ) + -2) = -3 from by norm_num] at key
  rw [omegaVir, key, LeeYang.L3vac]
  norm_num

/-- `L₋₂ω = L₋₂L₋₂|0⟩`. -/
theorem Lop_negTwo_omega : Lop c (-2) (omegaVir c) = LeeYang.L2L2vac c := rfl

/-- `L₋₂L₋₂|0⟩ ≠ 0`, from the proved level-4 independence. -/
theorem L2L2vac_ne_zero : LeeYang.L2L2vac c ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) • LeeYang.L2L2vac c + (0 : ℂ) • LeeYang.L4vac c = 0 := by
    rw [h]; simp
  exact one_ne_zero (LeeYang.level4_indep c h1).1


/-! ## §3  Two families of explicit field redefinitions

Both are *global* grade-preserving `φ` with `φ𝟙 = 0`, so both produce honest elements of
`Deform.gradedCoboundariesAt`.  Together they compute the coboundary side of the quotient at the
tridegrees reached below.

* the **scaling** redefinition `φ = L₀` (`scalGraded`), which acts on every graded piece at once;
* the **single-block** redefinition `φ = ψ` on `𝒱ₖ` and `0` elsewhere (`blockMap`), available for
  `k ≠ 0` (the vacuum condition forces the grade-`0` block to vanish).
-/

section General

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- The *undeformed* graded product `𝒱ₐ × 𝒱_b → 𝒱_d`: the `(a,b,d)` component of `Y` itself,
at the mode `gradedMode a b d = a + b − d − 1` determined by the tridegree. -/
def gradedProd (W : VertexOperatorAlgebra 𝒲) (a b d : ℤ) (u : ↥(W.grading a))
    (v : ↥(W.grading b)) : ↥(W.grading d) :=
  ⟨W.smul (u : 𝒲) (Deform.gradedMode a b d) (v : 𝒲), by
    have h := W.toPreVertexAlgebra.smul_mem_grading u.2 v.2 (Deform.gradedMode a b d)
    rwa [Deform.grading_of_gradedMode] at h⟩

/-- Forgetting the output-weight certificate gives back the ordinary VOA product at the mode
determined by the three weights. The graded product packages a familiar operation with its
correct target space. -/
@[simp] theorem gradedProd_coe (W : VertexOperatorAlgebra 𝒲) (a b d : ℤ) (u : ↥(W.grading a))
    (v : ↥(W.grading b)) :
    ((gradedProd W a b d u v : ↥(W.grading d)) : 𝒲)
      = W.smul (u : 𝒲) (Deform.gradedMode a b d) (v : 𝒲) := rfl

/-! ### §3.1  The scaling redefinition `φ = L₀` -/

/-- `L₀𝟙 = 0`: the vacuum has weight `0`. -/
theorem L_zero_vacuum_eq (W : VertexOperatorAlgebra 𝒲) : W.L 0 W.vacuum = 0 := by
  rw [W.L_zero_grading W.vacuum W.vacuum_mem]
  simp

/-- `L₀` preserves the grading (on `𝒱ₖ` it is multiplication by `k`). -/
theorem gradePreserving_L_zero (W : VertexOperatorAlgebra 𝒲) :
    Deform.GradePreserving W (W.L 0) := by
  intro k u hu
  rw [W.L_zero_grading u hu]
  exact Submodule.smul_mem _ _ hu

/-- The **scaling coboundary** `δL₀`, as a graded cochain. -/
noncomputable def scalGraded (W : VertexOperatorAlgebra 𝒲) : ↥(Deform.gradedCochains W) :=
  coboGraded W (L_zero_vacuum_eq W) (gradePreserving_L_zero W)

/-- **The closed form of `δL₀` at a tridegree**: it is the *scalar* `a + b − d` times the
undeformed product.  (Equivalently `u¹₍ₙ₎v = (n+1)u₍ₙ₎v`.) -/
theorem gradedComponent_scal_apply (W : VertexOperatorAlgebra 𝒲) (a b d : ℤ)
    (u : ↥(W.grading a)) (v : ↥(W.grading b)) :
    Deform.gradedComponent W a b d (scalGraded W) u v
      = ((a : ℂ) + b - d) • gradedProd W a b d u v := by
  refine Subtype.ext ?_
  rw [show scalGraded W = coboGraded W (L_zero_vacuum_eq W) (gradePreserving_L_zero W) from rfl,
    gradedComponent_coboGraded_apply]
  rw [W.L_zero_grading (u : 𝒲) u.2, W.L_zero_grading (v : 𝒲) v.2,
    W.L_zero_grading (W.smul (u : 𝒲) (Deform.gradedMode a b d) (v : 𝒲))
      (W.toPreVertexAlgebra.smul_mem_grading u.2 v.2 (Deform.gradedMode a b d)),
    Deform.grading_of_gradedMode, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right]
  change _ = ((a : ℂ) + b - d) • (W.smul (u : 𝒲) (Deform.gradedMode a b d) (v : 𝒲))
  module

/-- The scaling coboundary really is a coboundary at every tridegree. -/
theorem gradedComponent_scal_mem (W : VertexOperatorAlgebra 𝒲) (a b d : ℤ) :
    Deform.gradedComponent W a b d (scalGraded W) ∈ Deform.gradedCoboundariesAt W a b d :=
  gradedComponent_coboGraded_mem W (L_zero_vacuum_eq W) (gradePreserving_L_zero W) a b d

/-! ### §3.2  The single-block redefinition -/

/-- The internal-decomposition equivalence supplied by the structure field `W.isInternal`. -/
noncomputable def gradeEquiv (W : VertexOperatorAlgebra 𝒲) :
    DirectSum ℤ (fun k : ℤ => ↥(W.grading k)) ≃ₗ[ℂ] 𝒲 :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap W.grading) W.isInternal

/-- The **grade-`k` block** of a linear map: `ψ` on `𝒱ₖ`, zero on every other graded piece. -/
noncomputable def blockMap (W : VertexOperatorAlgebra 𝒲) (k : ℤ)
    (ψ : ↥(W.grading k) →ₗ[ℂ] ↥(W.grading k)) : 𝒲 →ₗ[ℂ] 𝒲 :=
  (W.grading k).subtype.comp (ψ.comp
    ((DirectSum.component ℂ ℤ (fun j => ↥(W.grading j)) k).comp
      (gradeEquiv W).symm.toLinearMap))

/-- A coordinate change supported on grade k acts there by the prescribed linear map. Projection to
the grade and inclusion back into the full state space do not alter a state already in that
grade. -/
theorem blockMap_apply_mem (W : VertexOperatorAlgebra 𝒲) (k : ℤ)
    (ψ : ↥(W.grading k) →ₗ[ℂ] ↥(W.grading k)) {x : 𝒲} (hx : x ∈ W.grading k) :
    blockMap W k ψ x = (ψ ⟨x, hx⟩ : 𝒲) := by
  have h : ((gradeEquiv W).symm x) k = ⟨x, hx⟩ :=
    DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem W.isInternal hx
  rw [blockMap]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← DirectSum.apply_eq_component, h]
  rfl

/-- The same coordinate change annihilates every other homogeneous grade. This makes it possible to
adjust one weight at a time without changing weights already fixed. -/
theorem blockMap_apply_of_ne (W : VertexOperatorAlgebra 𝒲) (k : ℤ)
    (ψ : ↥(W.grading k) →ₗ[ℂ] ↥(W.grading k)) {j : ℤ} (hjk : j ≠ k) {x : 𝒲}
    (hx : x ∈ W.grading j) : blockMap W k ψ x = 0 := by
  have h : ((gradeEquiv W).symm x) k = 0 :=
    DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne W.isInternal hjk hx
  rw [blockMap]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← DirectSum.apply_eq_component, h,
    map_zero]

/-- For `k ≠ 0` the block redefinition kills the vacuum (which sits in grade `0`). -/
theorem blockMap_vacuum (W : VertexOperatorAlgebra 𝒲) {k : ℤ} (hk : k ≠ 0)
    (ψ : ↥(W.grading k) →ₗ[ℂ] ↥(W.grading k)) : blockMap W k ψ W.vacuum = 0 :=
  blockMap_apply_of_ne W k ψ (Ne.symm hk) W.vacuum_mem

/-- The block redefinition preserves the grading. -/
theorem blockMap_gradePreserving (W : VertexOperatorAlgebra 𝒲) (k : ℤ)
    (ψ : ↥(W.grading k) →ₗ[ℂ] ↥(W.grading k)) :
    Deform.GradePreserving W (blockMap W k ψ) := by
  intro j u hu
  by_cases h : j = k
  · rw [h] at hu ⊢
    rw [blockMap_apply_mem W k ψ hu]
    exact (ψ ⟨u, hu⟩).2
  · rw [blockMap_apply_of_ne W k ψ h hu]
    exact Submodule.zero_mem _

/-- **The closed form of the block coboundary.**  At a tridegree `(a,b,k)` whose *source*
grades `a`, `b` both differ from `k`, the block redefinition sees only the target, and
`δφ(u,n,v) = −ψ(u₍ₙ₎v)`. -/
theorem gradedComponent_block_apply (W : VertexOperatorAlgebra 𝒲) {k : ℤ} (hk : k ≠ 0)
    (ψ : ↥(W.grading k) →ₗ[ℂ] ↥(W.grading k)) {a b : ℤ} (ha : a ≠ k) (hb : b ≠ k)
    (u : ↥(W.grading a)) (v : ↥(W.grading b)) :
    Deform.gradedComponent W a b k
        (coboGraded W (blockMap_vacuum W hk ψ) (blockMap_gradePreserving W k ψ)) u v
      = - ψ (gradedProd W a b k u v) := by
  refine Subtype.ext ?_
  rw [gradedComponent_coboGraded_apply,
    blockMap_apply_of_ne W k ψ ha u.2, blockMap_apply_of_ne W k ψ hb v.2,
    blockMap_apply_mem W k ψ
      (by
        have h := W.toPreVertexAlgebra.smul_mem_grading u.2 v.2 (Deform.gradedMode a b k)
        rwa [Deform.grading_of_gradedMode] at h)]
  simp only [PreVertexAlgebra.smul_zero_left, PreVertexAlgebra.smul_zero_right, Submodule.coe_neg]
  rw [zero_sub, add_zero]
  rfl

/-- The block coboundary lies in the coboundary space at its tridegree. -/
theorem gradedComponent_block_mem (W : VertexOperatorAlgebra 𝒲) {k : ℤ} (hk : k ≠ 0)
    (ψ : ↥(W.grading k) →ₗ[ℂ] ↥(W.grading k)) (a b : ℤ) :
    Deform.gradedComponent W a b k
        (coboGraded W (blockMap_vacuum W hk ψ) (blockMap_gradePreserving W k ψ))
      ∈ Deform.gradedCoboundariesAt W a b k :=
  gradedComponent_coboGraded_mem W (blockMap_vacuum W hk ψ) (blockMap_gradePreserving W k ψ) a b k

/-! ### §3.3  Two elementary linear-algebra facts -/

/-- In a `ℂ`-vector space, a nonzero vector can be sent anywhere by a linear endomorphism. -/
theorem exists_linear_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V] {w : V} (hw : w ≠ 0)
    (t : V) : ∃ ψ : V →ₗ[ℂ] V, ψ w = t := by
  have hmem : w ∈ (ℂ ∙ w) := Submodule.mem_span_singleton_self w
  obtain ⟨f, hf⟩ :=
    LinearMap.exists_extend (LinearEquiv.toSpanNonzeroSingleton ℂ V w hw).symm.toLinearMap
  have hfw : f w = 1 := by
    have := congrArg (fun g : (ℂ ∙ w) →ₗ[ℂ] ℂ => g ⟨w, hmem⟩) hf
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact (LinearEquiv.symm_apply_eq _).mpr
      (LinearEquiv.toSpanNonzeroSingleton_one ℂ V w hw).symm
  refine ⟨(LinearMap.toSpanSingleton ℂ V t).comp f, ?_⟩
  rw [LinearMap.comp_apply, hfw, LinearMap.toSpanSingleton_apply, one_smul]

/-- If the whole cochain space at a tridegree is the line through a single coboundary, the
coboundary space is everything. -/
theorem gradedCoboundariesAt_eq_top_of_generator (W : VertexOperatorAlgebra 𝒲) {a b d : ℤ}
    {S : Deform.GradedCochain W a b d} (hS : S ∈ Deform.gradedCoboundariesAt W a b d)
    (hspan : ∀ T : Deform.GradedCochain W a b d, ∃ r : ℂ, T = r • S) :
    Deform.gradedCoboundariesAt W a b d = ⊤ := by
  refine eq_top_iff.mpr fun T _ => ?_
  obtain ⟨r, rfl⟩ := hspan T
  exact Submodule.smul_mem _ r hS

/-- Every element of a line `ℂ·g` is a multiple of any *nonzero* multiple `w = γ·g` of `g`. -/
theorem exists_smul_of_line {V : Type*} [AddCommGroup V] [Module ℂ V] {g w x : V} {γ : ℂ}
    (hγ : γ ≠ 0) (hw : w = γ • g) (hx : x ∈ ℂ ∙ g) : ∃ r : ℂ, x = r • w := by
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨s / γ, ?_⟩
  rw [hw, smul_smul, div_mul_cancel₀ s hγ, hs]

end General


/-! ## §4  The computation at the tridegrees `(2,2,d)` of `V(c,0)` -/

section Virasoro

variable (c : ℂ)

/-- `ω`, as an element of the weight-`2` space of `V(c,0)`. -/
noncomputable def omega2 : ↥((virasoroVOA c).grading 2) :=
  ⟨omegaVir c, omegaVir_mem_gradingVir_two c⟩

/-- The conformal vector regarded as an element of the weight-two subspace is still the same state
after forgetting its membership proof. -/
@[simp] theorem omega2_coe : ((omega2 c : ↥((virasoroVOA c).grading 2)) : VirUniv c) = omegaVir c :=
  rfl

/-- Every weight-`2` state of `V(c,0)` is a multiple of `ω` (the space is the line `ℂ·ω`). -/
theorem exists_smul_omega2 (x : ↥((virasoroVOA c).grading 2)) : ∃ s : ℂ, x = s • omega2 c := by
  have hx : (x : VirUniv c) ∈ ℂ ∙ omegaVir c := by
    rw [← gradingVir_two c]; exact x.2
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨s, Subtype.ext hs.symm⟩

/-- **A cochain at tridegree `(2,2,d)` is determined by its single value on `(ω,ω)`** — this is
what makes the whole computation finite: the `(2,2,·)` cochain space is `𝒱_d` itself. -/
theorem gradedCochain_two_two_ext {d : ℤ}
    {T T' : Deform.GradedCochain (virasoroVOA c) 2 2 d}
    (h : T (omega2 c) (omega2 c) = T' (omega2 c) (omega2 c)) : T = T' := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  obtain ⟨s, rfl⟩ := exists_smul_omega2 c x
  obtain ⟨t, rfl⟩ := exists_smul_omega2 c y
  simp only [map_smul, LinearMap.smul_apply, h]

/-- The undeformed structure constant at tridegree `(2,2,d)`: `ω₍₃₋d₎ω = L_{2−d}ω`. -/
theorem gradedProd_omega_coe (d : ℤ) :
    ((gradedProd (virasoroVOA c) 2 2 d (omega2 c) (omega2 c) :
        ↥((virasoroVOA c).grading d)) : VirUniv c)
      = Lop c (2 - d) (omegaVir c) := by
  rw [gradedProd_coe, omega2_coe, smulVir_omega,
    show Deform.gradedMode 2 2 d - 1 = 2 - d from by simp only [Deform.gradedMode]; omega]

/-- The value of the scaling coboundary `δL₀` at tridegree `(2,2,d)`, on `(ω,ω)`. -/
theorem scal_two_two_value (d : ℤ) :
    ((Deform.gradedComponent (virasoroVOA c) 2 2 d (scalGraded (virasoroVOA c))
        (omega2 c) (omega2 c) : ↥((virasoroVOA c).grading d)) : VirUniv c)
      = (4 - (d : ℂ)) • Lop c (2 - d) (omegaVir c) := by
  rw [gradedComponent_scal_apply]
  change (((2 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) - (d : ℂ))
      • ((gradedProd (virasoroVOA c) 2 2 d (omega2 c) (omega2 c) :
          ↥((virasoroVOA c).grading d)) : VirUniv c) = _
  rw [gradedProd_omega_coe]
  norm_num

/-- **The scaling criterion.**  If the target space at `(2,2,d)` is a line `ℂ·g` and the
scaling coboundary `δL₀` hits a *nonzero* multiple of `g`, the coboundary space at that tridegree
is the whole cochain space. -/
theorem gradedCoboundariesAt_two_two_eq_top_of_scal {d : ℤ} {g : VirUniv c} {γ : ℂ} (hγ : γ ≠ 0)
    (hline : (virasoroVOA c).grading d = ℂ ∙ g)
    (hval : (4 - (d : ℂ)) • Lop c (2 - d) (omegaVir c) = γ • g) :
    Deform.gradedCoboundariesAt (virasoroVOA c) 2 2 d = ⊤ := by
  refine gradedCoboundariesAt_eq_top_of_generator (virasoroVOA c)
    (gradedComponent_scal_mem (virasoroVOA c) 2 2 d) ?_
  intro T
  have hS := (scal_two_two_value c d).trans hval
  have hx : ((T (omega2 c) (omega2 c) : ↥((virasoroVOA c).grading d)) : VirUniv c) ∈ ℂ ∙ g := by
    rw [← hline]; exact (T (omega2 c) (omega2 c)).2
  obtain ⟨r, hr⟩ := exists_smul_of_line hγ hS hx
  exact ⟨r, gradedCochain_two_two_ext c (Subtype.ext hr)⟩

/-- **The block criterion.**  For a target grade `k ∉ {0,2}` at which the undeformed structure
constant `L_{2−k}ω` is nonzero, the single-block redefinition already fills the whole cochain
space at `(2,2,k)`. -/
theorem gradedCoboundariesAt_two_two_eq_top_of_block {k : ℤ} (hk0 : k ≠ 0) (hk2 : k ≠ 2)
    (hne : Lop c (2 - k) (omegaVir c) ≠ 0) :
    Deform.gradedCoboundariesAt (virasoroVOA c) 2 2 k = ⊤ := by
  refine eq_top_iff.mpr fun T _ => ?_
  have hprod : gradedProd (virasoroVOA c) 2 2 k (omega2 c) (omega2 c) ≠ 0 := by
    intro h
    exact hne (by rw [← gradedProd_omega_coe c k, h, Submodule.coe_zero])
  obtain ⟨ψ, hψ⟩ := exists_linear_apply_eq hprod (- T (omega2 c) (omega2 c))
  have hmem := gradedComponent_block_mem (virasoroVOA c) hk0 ψ 2 2
  have heq : Deform.gradedComponent (virasoroVOA c) 2 2 k
      (coboGraded (virasoroVOA c) (blockMap_vacuum (virasoroVOA c) hk0 ψ)
        (blockMap_gradePreserving (virasoroVOA c) k ψ)) = T := by
    refine gradedCochain_two_two_ext c ?_
    rw [gradedComponent_block_apply (virasoroVOA c) hk0 ψ (Ne.symm hk2) (Ne.symm hk2), hψ,
      neg_neg]
  rwa [heq] at hmem

/-! ### §4.1  `(2,2,0)`: the central-charge slot — the one place `c` enters -/

/-- **`(2,2,0)`, `c ≠ 0`: the coboundary space is everything.**  The mode is `n = 3`, the
cochain space is the line `𝒱₀ = ℂ·𝟙`, and the scaling redefinition `δL₀` produces `2c·𝟙` there.
The rank of the coboundary map therefore drops exactly at `c = 0`. -/
theorem gradedCoboundariesAt_two_two_zero_eq_top (hc : c ≠ 0) :
    Deform.gradedCoboundariesAt (virasoroVOA c) 2 2 0 = ⊤ := by
  refine gradedCoboundariesAt_two_two_eq_top_of_scal c (γ := 2 * c) (g := vacVec c)
    (by simpa using hc) (gradingVir_zero c) ?_
  rw [show (2 : ℤ) - 0 = 2 from by norm_num, Lop_two_omega, smul_smul]
  congr 1
  push_cast
  ring

set_option synthInstance.maxHeartbeats 1000000 in
-- The carrier `virasoroVOA c` is a 19-field structure and `DeformationSpaceAt` is a quotient
-- of a submodule of a submodule; the default instance-search budget is not enough to build
-- the quotient's `Zero`.
/-- **`(2,2,0)`, `c ≠ 0`: the deformation space vanishes.**  A genuine, fully-proved partial
rigidity statement at the lowest tridegree where anything can happen. -/
theorem deformationSpaceAt_two_two_zero_trivial (hc : c ≠ 0) :
    ∀ z : Deform.DeformationSpaceAt (virasoroVOA c) 2 2 0, z = 0 :=
  deformationSpaceAt_subsingleton_of_coboundariesAt_top (virasoroVOA c)
    (gradedCoboundariesAt_two_two_zero_eq_top c hc)

/-- **`(2,2,0)` at `c = 0`: the coboundary space collapses to `0`.**  Every grade-preserving
`φ` acts on `𝒱₂ = ℂ·ω` by a scalar and kills `𝒱₀ = ℂ·𝟙`, so `δφ(ω,3,ω) = 2λ·ω₍₃₎ω = λc·𝟙`,
which vanishes identically when `c = 0`.  This is the rank drop, proved. -/
theorem gradedCoboundariesAt_two_two_zero_eq_bot :
    Deform.gradedCoboundariesAt (virasoroVOA 0) 2 2 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro T ⟨f, hf, rfl⟩
  obtain ⟨φ, -, hφg, hφ⟩ := hf
  refine gradedCochain_two_two_ext 0 ?_
  refine Subtype.ext ?_
  have hω : φ (omegaVir 0) ∈ ℂ ∙ omegaVir 0 := by
    rw [← gradingVir_two 0]
    exact hφg 2 (omegaVir 0) (omegaVir_mem_gradingVir_two 0)
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hω
  have hzero : (virasoroVOA 0).smul (omegaVir 0) 3 (omegaVir 0) = 0 := by
    rw [smulVir_omega, show (3 : ℤ) - 1 = 2 from by norm_num, Lop_two_omega]
    simp
  have hn : Deform.gradedMode 2 2 0 = 3 := by simp only [Deform.gradedMode]; norm_num
  simp only [Submodule.subtype_apply] at hφ
  rw [Deform.gradedComponent_apply, hn, Deform.cmode_def, hφ, omega2_coe, ← hlam,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, hzero, smul_zero, map_zero,
    sub_zero, add_zero]
  simp

/-! ### §4.2  `(2,2,2)` and the block tridegrees `(2,2,3)`, `(2,2,4)` -/

/-- **`(2,2,2)`: the coboundary space is everything, for every `c`.**  The mode is `n = 1`,
`ω₍₁₎ω = L₀ω = 2ω`, and `δL₀` produces `4ω`. -/
theorem gradedCoboundariesAt_two_two_two_eq_top :
    Deform.gradedCoboundariesAt (virasoroVOA c) 2 2 2 = ⊤ := by
  refine gradedCoboundariesAt_two_two_eq_top_of_scal c (γ := 4) (g := omegaVir c)
    (by norm_num) (gradingVir_two c) ?_
  rw [show (2 : ℤ) - 2 = 0 from by norm_num, Lop_zero_omega, smul_smul]
  congr 1
  push_cast
  ring

set_option synthInstance.maxHeartbeats 1000000 in
-- The carrier `virasoroVOA c` is a 19-field structure and `DeformationSpaceAt` is a quotient
-- of a submodule of a submodule; the default instance-search budget is not enough to build
-- the quotient's `Zero`.
/-- **`(2,2,2)`: the deformation space vanishes, for every `c`.** -/
theorem deformationSpaceAt_two_two_two_trivial :
    ∀ z : Deform.DeformationSpaceAt (virasoroVOA c) 2 2 2, z = 0 :=
  deformationSpaceAt_subsingleton_of_coboundariesAt_top (virasoroVOA c)
    (gradedCoboundariesAt_two_two_two_eq_top c)

/-- **`(2,2,3)`: the coboundary space is everything, for every `c`.**  The mode is `n = 0`,
`ω₍₀₎ω = L₋₁ω = L₋₃|0⟩ ≠ 0`. -/
theorem gradedCoboundariesAt_two_two_three_eq_top :
    Deform.gradedCoboundariesAt (virasoroVOA c) 2 2 3 = ⊤ := by
  refine gradedCoboundariesAt_two_two_eq_top_of_block c (by norm_num) (by norm_num) ?_
  rw [show (2 : ℤ) - 3 = -1 from by norm_num, Lop_negOne_omega]
  exact LeeYang.L3vac_ne_zero c

set_option synthInstance.maxHeartbeats 1000000 in
-- The carrier `virasoroVOA c` is a 19-field structure and `DeformationSpaceAt` is a quotient
-- of a submodule of a submodule; the default instance-search budget is not enough to build
-- the quotient's `Zero`.
/-- **`(2,2,3)`: the deformation space vanishes, for every `c`.** -/
theorem deformationSpaceAt_two_two_three_trivial :
    ∀ z : Deform.DeformationSpaceAt (virasoroVOA c) 2 2 3, z = 0 :=
  deformationSpaceAt_subsingleton_of_coboundariesAt_top (virasoroVOA c)
    (gradedCoboundariesAt_two_two_three_eq_top c)

/-- **`(2,2,4)`: the coboundary space is everything, for every `c`** — and here the cochain
space is genuinely **two**-dimensional (`𝒱₄ = span{L₋₂²|0⟩, L₋₄|0⟩}`, `level4_indep`).  The mode
is `n = −1`, `ω₍₋₁₎ω = L₋₂ω = L₋₂L₋₂|0⟩ ≠ 0`, and the grade-4 block redefinition sweeps out all
of `𝒱₄`. -/
theorem gradedCoboundariesAt_two_two_four_eq_top :
    Deform.gradedCoboundariesAt (virasoroVOA c) 2 2 4 = ⊤ := by
  refine gradedCoboundariesAt_two_two_eq_top_of_block c (by norm_num) (by norm_num) ?_
  rw [show (2 : ℤ) - 4 = -2 from by norm_num, Lop_negTwo_omega]
  exact L2L2vac_ne_zero c

set_option synthInstance.maxHeartbeats 1000000 in
-- The carrier `virasoroVOA c` is a 19-field structure and `DeformationSpaceAt` is a quotient
-- of a submodule of a submodule; the default instance-search budget is not enough to build
-- the quotient's `Zero`.
/-- **`(2,2,4)`: the deformation space vanishes, for every `c`.** -/
theorem deformationSpaceAt_two_two_four_trivial :
    ∀ z : Deform.DeformationSpaceAt (virasoroVOA c) 2 2 4, z = 0 :=
  deformationSpaceAt_subsingleton_of_coboundariesAt_top (virasoroVOA c)
    (gradedCoboundariesAt_two_two_four_eq_top c)

end Virasoro



/-! ### §4.3  What the `c = 0` collapse buys: an obstruction detector

At `c = 0` the coboundary space at `(2,2,0)` is `0`, so *nothing* at that tridegree can be
trivialised by a field redefinition and the deformation space there **is** the cocycle space.
That turns the slot into a detector: any graded first-order deformation of `V(0,0)` with
`ω¹₍₃₎ω ≠ 0` produces a nonzero class, and hence disproves `Deform.IsRigid (virasoroVOA 0)`.
(Whether such a deformation exists is *not* settled here — see the `## Scope` section.) -/

/-- At `c = 0`, the coboundaries inside the cocycles at `(2,2,0)` are zero. -/
theorem gradedCoboundariesIn_two_two_zero_eq_bot :
    Deform.gradedCoboundariesIn (virasoroVOA 0) 2 2 0 = ⊥ := by
  change (Deform.gradedCoboundariesAt (virasoroVOA 0) 2 2 0).comap
      (Deform.gradedCocyclesAt (virasoroVOA 0) 2 2 0).subtype = ⊥
  rw [gradedCoboundariesAt_two_two_zero_eq_bot, Submodule.comap_bot, Submodule.ker_subtype]

set_option synthInstance.maxHeartbeats 1000000 in
-- `DeformationSpaceAt` is a quotient of a submodule of a submodule; building the quotient's
-- `Zero` exceeds the default instance-search budget.
/-- **The obstruction detector at `c = 0`.**  A graded first-order deformation `D` of
`V(0,0)` with `ω¹₍₃₎ω ≠ 0` has a **nonzero** class in `DeformationSpaceAt (virasoroVOA 0) 2 2 0`.
By `Deform.gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid` such a `D` would disprove
`Deform.IsRigid (virasoroVOA 0)`. -/
theorem deformationSpaceAt_two_two_zero_ne_zero_of_witness
    (D : Deform.FirstOrderDeformation (virasoroVOA 0)) (hD : D.IsGraded)
    (hne : D.smul₁ (omegaVir 0) 3 (omegaVir 0) ≠ 0) :
    ∃ z : Deform.DeformationSpaceAt (virasoroVOA 0) 2 2 0, z ≠ 0 := by
  have hTmem : Deform.gradedComponent (virasoroVOA 0) 2 2 0 ⟨D.Y1, hD⟩
      ∈ Deform.gradedCocyclesAt (virasoroVOA 0) 2 2 0 :=
    Submodule.mem_map_of_mem (Deform.Y1_mem_cocycles D)
  have hTne : Deform.gradedComponent (virasoroVOA 0) 2 2 0 ⟨D.Y1, hD⟩ ≠ 0 := by
    intro h
    apply hne
    have h2 : Deform.cmode D.Y1 (omegaVir 0) (Deform.gradedMode 2 2 0) (omegaVir 0) = 0 := by
      have hc := congrArg
        (fun S : Deform.GradedCochain (virasoroVOA 0) 2 2 0 =>
          ((S (omega2 0) (omega2 0) : ↥((virasoroVOA 0).grading 0)) : VirUniv 0)) h
      simpa using hc
    rw [show Deform.gradedMode 2 2 0 = 3 from by simp only [Deform.gradedMode]; norm_num] at h2
    rw [← Deform.cmode_Y1]
    exact h2
  refine ⟨Submodule.Quotient.mk ⟨_, hTmem⟩, ?_⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero, gradedCoboundariesIn_two_two_zero_eq_bot,
    Submodule.mem_bot] at h
  exact hTne (congrArg Subtype.val h)

/-! ## §5  Where the computation cannot start: the trivially-zero tridegrees -/

section Trivial

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- **Every tridegree with source grade `0` is vacuous.**  A cocycle satisfies the order-`t`
vacuum axiom `Y₁(𝟙,z) = 0`, and `𝒱₀ = ℂ·𝟙`, so its `(0,b,d)`-component vanishes identically.
The deformation space there is zero for a *trivial* reason, and no information about rigidity
can be extracted from those tridegrees. -/
theorem gradedCocyclesAt_source_zero (W : VertexOperatorAlgebra 𝒲) (b d : ℤ) :
    Deform.gradedCocyclesAt W 0 b d = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro T ⟨f, hf, rfl⟩
  refine LinearMap.ext fun u => LinearMap.ext fun v => Subtype.ext ?_
  have hvac : ((f : ↥(Deform.gradedCochains W)) : Deform.Cochain 𝒲) W.vacuum = 0 := hf.2.1
  have hu : (u : 𝒲) ∈ ℂ ∙ W.vacuum := by rw [← W.vacuum_grade]; exact u.2
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hu
  rw [Deform.gradedComponent_apply, ← hs, Deform.cmode_smul_left, Deform.cmode_def, hvac]
  simp

set_option synthInstance.maxHeartbeats 1000000 in
-- `DeformationSpaceAt` is a quotient of a submodule of a submodule; building the quotient's
-- `Zero` exceeds the default instance-search budget.
/-- The deformation space at a source-grade-`0` tridegree vanishes (trivially). -/
theorem deformationSpaceAt_source_zero_trivial (W : VertexOperatorAlgebra 𝒲) (b d : ℤ) :
    ∀ z : Deform.DeformationSpaceAt W 0 b d, z = 0 :=
  deformationSpaceAt_subsingleton_of_cocyclesAt_bot W (gradedCocyclesAt_source_zero W b d)

/-- If the *target* graded piece vanishes, the cochain space at that tridegree is `0`, so the
coboundary space is (vacuously) everything. -/
theorem gradedCoboundariesAt_eq_top_of_target_bot (W : VertexOperatorAlgebra 𝒲) {a b d : ℤ}
    (h : W.grading d = ⊥) : Deform.gradedCoboundariesAt W a b d = ⊤ := by
  refine eq_top_iff.mpr fun T _ => ?_
  have hT : T = 0 := by
    refine LinearMap.ext fun u => LinearMap.ext fun v => Subtype.ext ?_
    have hmem : ((T u v : ↥(W.grading d)) : 𝒲) = 0 :=
      (Submodule.eq_bot_iff _).mp h _ (T u v).2
    simpa using hmem
  rw [hT]
  exact Submodule.zero_mem _

end Trivial

section VirasoroTrivial

variable (c : ℂ)

/-- **`V(c,0)` has no weight-one states**: `𝒱₁ = 0` (energies are `0` or `≥ 2`). -/
theorem gradingVir_one_eq_bot : gradingVir c 1 = ⊥ := by
  rw [gradingVir, Submodule.span_eq_bot]
  rintro x ⟨ws, hen, rfl⟩
  exfalso
  cases ws with
  | nil => simp at hen
  | cons i rest => rw [energyVir_cons] at hen; omega

set_option synthInstance.maxHeartbeats 1000000 in
-- `DeformationSpaceAt` is a quotient of a submodule of a submodule; building the quotient's
-- `Zero` exceeds the default instance-search budget.
/-- **`(2,2,1)` is empty**: `𝒱₁ = 0`, so the cochain space itself is zero.  The first tridegree
`(2,2,d)` with `d = 1` carries no information. -/
theorem deformationSpaceAt_two_two_one_trivial :
    ∀ z : Deform.DeformationSpaceAt (virasoroVOA c) 2 2 1, z = 0 :=
  deformationSpaceAt_subsingleton_of_coboundariesAt_top (virasoroVOA c)
    (gradedCoboundariesAt_eq_top_of_target_bot (virasoroVOA c) (gradingVir_one_eq_bot c))

/-! ## §6  The dimensions -/

/-- `dim 𝒱₀ = 1`. -/
theorem finrank_gradingVir_zero : Module.finrank ℂ ↥(gradingVir c 0) = 1 := by
  rw [gradingVir_zero c]
  exact finrank_span_singleton (vacVec_ne_zero c)

/-- `dim 𝒱₁ = 0`. -/
theorem finrank_gradingVir_one : Module.finrank ℂ ↥(gradingVir c 1) = 0 := by
  rw [gradingVir_one_eq_bot c]
  simp

/-- `dim 𝒱₂ = 1` (the line `ℂ·ω`). -/
theorem finrank_gradingVir_two : Module.finrank ℂ ↥(gradingVir c 2) = 1 := by
  rw [gradingVir_two c]
  exact finrank_span_singleton (omegaVir_ne_zero_all c)

/-- The only creation word of energy `3` is `[1]`. -/
theorem energyVir_eq_three {ws : List ℕ} (h : energyVir ws = 3) : ws = [1] := by
  match ws with
  | [] => exact absurd h (by decide)
  | [i] =>
      rw [energyVir_cons, energyVir_nil] at h
      have hi : i = 1 := by omega
      rw [hi]
  | (i :: j :: rest) =>
      exfalso
      rw [energyVir_cons, energyVir_cons] at h
      omega

/-- The one-letter creation word indexed by one is L at index −3 applied to the vacuum. It is the
state used to describe weight three and the translation descendant of the conformal generator. -/
theorem negWordVir_one_word : negWordVir c [1] = LeeYang.L3vac c := by
  have h : (-((1 : ℕ) : ℤ) - 2) = -3 := by norm_num
  rw [negWordVir_cons, negWordVir_nil, h, LeeYang.L3vac]

/-- `𝒱₃ = ℂ·L₋₃|0⟩`, hence `dim 𝒱₃ = 1`. -/
theorem gradingVir_three : gradingVir c 3 = ℂ ∙ LeeYang.L3vac c := by
  apply le_antisymm
  · rw [gradingVir, Submodule.span_le]
    rintro x ⟨ws, hen, rfl⟩
    have h3 : energyVir ws = 3 := by exact_mod_cast hen
    rw [energyVir_eq_three h3, negWordVir_one_word]
    exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_singleton_le_iff_mem]
    have h := negWord_mem_gradingVir c [1]
    rw [show (energyVir [1] : ℤ) = 3 from rfl, negWordVir_one_word] at h
    exact h

/-- `dim 𝒱₃ = 1`. -/
theorem finrank_gradingVir_three : Module.finrank ℂ ↥(gradingVir c 3) = 1 := by
  rw [gradingVir_three c]
  exact finrank_span_singleton (LeeYang.L3vac_ne_zero c)

/-- `dim 𝒱₄ = 2` — the first graded piece that is not a line (`L₋₂²|0⟩` and `L₋₄|0⟩`). -/
theorem finrank_gradingVir_four : Module.finrank ℂ ↥(gradingVir c 4) = 2 := by
  have hli : LinearIndependent ℂ ![LeeYang.L2L2vac c, LeeYang.L4vac c] :=
    LinearIndependent.pair_iff.mpr fun s t h => LeeYang.level4_indep c h
  have hrange : ({LeeYang.L2L2vac c, LeeYang.L4vac c} : Set (VirUniv c))
      = Set.range ![LeeYang.L2L2vac c, LeeYang.L4vac c] := by
    ext x
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [LeeYang.gradingVir_four c, hrange, finrank_span_eq_card hli]
  simp

/-- **The cochain space at `(2,2,d)` is `𝒱_d`**: since `dim 𝒱₂ = 1`, the finite-dimensional
cochain space at tridegree `(2,2,d)` has dimension `dim 𝒱_d`.  Concretely: `1` at `d = 0`, `0` at
`d = 1`, `1` at `d = 2`, `1` at `d = 3`, `2` at `d = 4`. -/
theorem finrank_gradedCochain_two_two (d : ℤ) :
    Module.finrank ℂ (Deform.GradedCochain (virasoroVOA c) 2 2 d)
      = Module.finrank ℂ ↥((virasoroVOA c).grading d) := by
  haveI := (virasoroVOA c).toPreVertexAlgebra.finrank 2
  haveI := (virasoroVOA c).toPreVertexAlgebra.finrank d
  rw [Module.finrank_linearMap, Module.finrank_linearMap,
    show Module.finrank ℂ ↥((virasoroVOA c).grading 2) = 1 from finrank_gradingVir_two c,
    one_mul, one_mul]

end VirasoroTrivial

end VirDefLow

end VOA
