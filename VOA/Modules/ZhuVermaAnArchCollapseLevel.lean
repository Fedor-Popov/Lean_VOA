/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ25
import VOA.Modules.ZhuVermaAnArchHingeCollapse

/-!
# Dong–Jiang **Lemma 2.7 into `O'`** — the `hLevel` collapse generator family (`O''' ⊆ O'` at `m = 0`)

This file delivers the **`hLevel`** generator family of the hinge collapse
`onmFull_le_Onm_of_gens` (`ZhuVermaAnArchHingeCollapse`).  Recall that the entire faithful Phase-4
Zhu bijection reduces (via `anmCrossClosure_of_collapse` + `anmRightModule_of_collapse`) to the
single collapse predicate

  `OnmCollapses W n  :=  OnmFull W n 0 ≤ Onm W n 0`,

and `onmFull_le_Onm_of_gens W n 0` reduces *that* to **exactly two** into-`O'` generator memberships:

* `hAssoc` (DJ Lemma 2.6, `O'' ⊆ O'`) — the associator-defect generators, handled in a sibling file;
* `hLevel` (DJ Lemma 2.7, `O''' ⊆ O'`) — the level-mixing generators, the subject **here**:

  `hLevel : ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W n 0 p a g v ∈ Onm W n 0`.

`levelMix W n 0 p a g v = anmGen W n 0 p (anmGen W n p p a g) v` is the seed of the `O'''_{n,0}`
summand: the level-`p` Zhu ideal `O_p(𝒱) = Onm W p p` carried up to level `n` by the Dong–Jiang
products `(a *^n_{p,p} g) *^n_{0,p} v`.

## What is established here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`LevelMixCollapse W n p`** — the precise residual `Prop`: the DJ Lemma 2.7 *into-`O'`* content of
  the level-mixing summand, stated as its two `Onm W p p`-generator slices directly into `Onm W n 0`
  (the circle-generator slice and the diagonal grading-generator slice).  It is NOT an axiom and NOT
  `sorry`'d — it is the genuine remaining combinatorial identity, isolated by the `span_le` reduction.

* **`hLevel_of_levelMixCollapse`** — the FULLY-PROVEN `span_le` reduction: given `LevelMixCollapse`,
  the headline `levelMix W n 0 p a g v ∈ Onm W n 0` holds for *every* `g ∈ Onm W p p` (and arbitrary
  `a, v`).  This is pure `comap`/`Submodule.span_le` bookkeeping: the level-mixing map
  `g ↦ anmGen W n 0 p (anmGen W n p p a g) v` is ℂ-linear in `g`, so the headline on all of
  `Onm W p p` follows from its action on the two `O'_{p,p}` generator families.

* **`levelMix_mem_OnmFull_unconditional`** — the unconditional bridge into the FULL ideal:
  `levelMix W n 0 p a g v ∈ OnmFull W n 0` for every `g ∈ Onm W p p`, with NO open residual.  This is
  exactly the proven Vandermonde-free DJ Lemma 2.7 chain `levelMixGen_mem_OnmFull_unconditional`
  (`ZhuVermaAnArchDJ25`, `(p₁, p₂) = (p, p)`, `m = 0`), which discharges the reassociation
  (`bareAssoc_mem_OnmFull`), the `span_le` split, the off-diagonal grading absorption
  (`anmGen_offdiag_Lgen_eq_general`), and the `DJ27ChainTail`/DJ 2.5 circle cross term
  (`dj27ChainTail_holds`).  Its output lands in `OnmFull` because each reassociation step legitimately
  produces an `O''_{n,0}` (associator-defect) element.

* **`hLevel_of_collapse`** — the architecture-consistent route: `OnmCollapses W n` ⟹ `hLevel` (at this
  `n`, for every `p`), by composing the unconditional `OnmFull` bridge with the collapse
  `OnmFull W n 0 ≤ Onm W n 0`.

## Status of the residual

The level-mixing membership into the *full* ideal `OnmFull W n 0` is **unconditionally true** and
discharged here (`levelMix_mem_OnmFull_unconditional`).  The genuine open content of `hLevel` is
**solely** the `OnmFull → Onm` collapse on this output shape: the DJ Lemma 2.7 chain inserts an
`O''_{n,0}` associator defect at each reassociation, and re-expressing that defect inside `O'_{n,0}`
is the SAME *into-`O'`* combinatorics that DJ Lemma 2.6 (`assocBar_mem_Onm`, modulo `AssocBarExpand`)
isolates — the `Y(Y(a,z₁−z₂)b,z₂)c` iterate reassociation whose `D_{n,m}`-coefficient weights vanish
by Prop 5.2.  We isolate that content precisely as the two-slice `LevelMixCollapse` residual and prove
the headline FROM it; we do not fake-close it.  Engine status (rank-1 free boson,
`certificates/mathematica/hinge_o2o3.wl`): both level-mixing slices lie in `Onm W n 0` for every tested
homogeneous input within the basis-grade guard.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 Lemma 2.7 (the `O'''_{n,m}` inclusion),
Lemma 2.6, Prop 5.2; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The level-mixing map as a ℂ-linear map in the inner factor `g` (for the `span_le` reduction). -/

/-- The level-mixing action `g ↦ levelMix W n 0 p a g v = anmGen W n 0 p (anmGen W n p p a g) v`
as a ℂ-linear map in `g` (composition of the inner right-slot map `anmGen W n p p a ·` and the outer
left-slot map `· ∗ⁿ_{0,p} v`). -/
noncomputable def levelMixMap (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) (a v : 𝒱) :
    𝒱 →ₗ[ℂ] 𝒱 where
  toFun g := anmGen W n 0 p (anmGen W n p p a g) v
  map_add' g₁ g₂ := by
    simp only [anmGen_add_right, anmGen_add_left]
  map_smul' c g := by
    simp only [anmGen_smul_right, anmGen_smul_left, RingHom.id_apply]

@[simp] theorem levelMixMap_apply (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) (a v g : 𝒱) :
    levelMixMap W n p a v g = anmGen W n 0 p (anmGen W n p p a g) v := rfl

theorem levelMixMap_eq_levelMix (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) (a v g : 𝒱) :
    levelMixMap W n p a v g = levelMix W n 0 p a g v := rfl

/-! ## The precise DJ Lemma 2.7 *into-`O'`* residual (the two `O'_{p,p}` generator slices). -/

/-- **`LevelMixCollapse W n p`** — the Dong–Jiang Lemma 2.7 *into-`O'`* content of the level-mixing
summand at `m = 0`, isolated to its two `O'_{p,p}` generator families directly into `Onm W n 0`:

* `circ`  — the circle-generator slice: `levelMix W n 0 p a (anmCirc W p p c d) v ∈ Onm W n 0`;
* `grad`  — the diagonal grading-generator slice: `levelMix W n 0 p a (anmLgen W p p c) v ∈ Onm W n 0`.

This is the genuine remaining combinatorial identity (the `OnmFull → Onm` collapse on the level-mixing
output shape — equivalently the DJ 2.6 `Y(Y(a,z₁−z₂)b,z₂)c` iterate reassociation that re-expresses
each `O''_{n,0}` reassociation defect inside `O'_{n,0}` with `D_{n,0}`-coefficient weights that vanish
by Prop 5.2).  It is carried as a hypothesis — NOT an axiom, NOT `sorry`'d.  The level-mixing
membership into the *full* ideal is unconditional (`levelMix_mem_OnmFull_unconditional`); only this
into-`O'` slice is open. -/
structure LevelMixCollapse (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) : Prop where
  /-- The circle-generator slice of the level-mixing summand, into `O'_{n,0}`. -/
  circ : ∀ a v c d : 𝒱, levelMix W n 0 p a (anmCirc W p p c d) v ∈ Onm W n 0
  /-- The diagonal grading-generator slice of the level-mixing summand, into `O'_{n,0}`. -/
  grad : ∀ a v c : 𝒱, levelMix W n 0 p a (anmLgen W p p c) v ∈ Onm W n 0

/-! ## The `span_le` reduction: `LevelMixCollapse ⟹ hLevel` (FULLY PROVEN). -/

/-- **The level-mixing map carries `Onm W p p` into `Onm W n 0` given the two generator slices.**
Pure `comap`/`Submodule.span_le`: `Onm W p p = span{circle gens} ⊔ OnmL`, and `levelMixMap` is
ℂ-linear, so the membership on all of `Onm W p p` follows from its action on the two `O'_{p,p}`
generator families (`circ`, `grad`). -/
theorem levelMix_mem_Onm_of_collapse (W : VertexOperatorAlgebra 𝒱) (n p : ℕ)
    (hLM : LevelMixCollapse W n p) (a v : 𝒱) :
    ∀ g ∈ Onm W p p, levelMix W n 0 p a g v ∈ Onm W n 0 := by
  intro g hg
  have hle : Onm W p p ≤ (Onm W n 0).comap (levelMixMap W n p a v) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, levelMixMap_apply] using
        hLM.circ a v c d
    · rw [OnmL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, levelMixMap_apply] using
        hLM.grad a v c
  have hx : g ∈ (Onm W n 0).comap (levelMixMap W n p a v) := hle hg
  rwa [Submodule.mem_comap, levelMixMap_apply] at hx

/-- **`hLevel` from the per-`p` collapse residual.**  Given `LevelMixCollapse W n p` for every `p`,
the `hLevel` family of `onmFull_le_Onm_of_gens W n 0` holds:
`∀ p a v g, g ∈ Onm W p p → levelMix W n 0 p a g v ∈ Onm W n 0`. -/
theorem hLevel_of_levelMixCollapse (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hLM : ∀ p : ℕ, LevelMixCollapse W n p) :
    ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W n 0 p a g v ∈ Onm W n 0 :=
  fun p a v g hg => levelMix_mem_Onm_of_collapse W n p (hLM p) a v g hg

/-! ## The unconditional bridge into the FULL ideal (NO residual). -/

/-- **The level-mixing summand lands in the FULL ideal, unconditionally.**
`levelMix W n 0 p a g v ∈ OnmFull W n 0` for every `g ∈ Onm W p p`, with NO open residual.

`levelMix W n 0 p a g v = anmGen W n 0 p (anmGen W n p p a g) v`, which is exactly the LHS of the
proven Vandermonde-free DJ Lemma 2.7 chain `levelMixGen_mem_OnmFull_unconditional`
(`ZhuVermaAnArchDJ25`) at `(p₁, p₂) = (p, p)`, `m = 0` (`anmGen W n m p₁ (anmGen W n p₁ p₂ a g) v`
with `p₁ = p₂ = p`).  That chain discharges the first reassociation (`bareAssoc_mem_OnmFull`), the
`span_le` split into the two `O'_{p,p}` generator families, the off-diagonal grading absorption
(`anmGen_offdiag_Lgen_eq_general`), and the DJ 2.5 circle cross term (`dj27ChainTail_holds`).  It
lands in `OnmFull` (not `Onm`) precisely because each reassociation legitimately inserts an
`O''_{n,0}` associator-defect element. -/
theorem levelMix_mem_OnmFull_unconditional (W : VertexOperatorAlgebra 𝒱) (n p : ℕ)
    (a v g : 𝒱) (hg : g ∈ Onm W p p) :
    levelMix W n 0 p a g v ∈ OnmFull W n 0 :=
  levelMixGen_mem_OnmFull_unconditional W n 0 p p a v g hg

/-! ## `hLevel` from the architecture-level collapse `OnmCollapses`. -/

/-- **`hLevel` from the collapse `OnmCollapses W n`.**  Composing the unconditional `OnmFull` bridge
(`levelMix_mem_OnmFull_unconditional`) with the collapse `OnmFull W n 0 ≤ Onm W n 0` gives the
`hLevel` family directly.  This is the architecture-consistent route: the level-mixing into-`O'`
membership is exactly the `OnmFull → Onm` collapse on the level-mixing output shape, which the
`OnmCollapses W n` hypothesis encodes (and which `onmFull_le_Onm_of_gens` in turn reduces to this very
`hLevel` family together with `hAssoc`). -/
theorem hLevel_of_collapse (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcol : OnmCollapses W n) :
    ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W n 0 p a g v ∈ Onm W n 0 :=
  fun p a v g hg => hcol (levelMix_mem_OnmFull_unconditional W n p a v g hg)

/-- **The collapse `OnmCollapses W n` implies the per-`p` `LevelMixCollapse` residual.**  Bridges the
architecture-level collapse to the finer two-slice residual: each generator slice lands in `OnmFull`
unconditionally and is collapsed into `Onm` by `hcol`.  (Shows the two formulations agree: closing
`OnmCollapses` is equivalent, on the level-mixing summand, to closing `LevelMixCollapse W n p` for all
`p`.) -/
theorem levelMixCollapse_of_collapse (W : VertexOperatorAlgebra 𝒱) (n p : ℕ)
    (hcol : OnmCollapses W n) :
    LevelMixCollapse W n p where
  circ a v c d :=
    hcol (levelMix_mem_OnmFull_unconditional W n p a v (anmCirc W p p c d)
      (anmCirc_mem_Onm W p p c d))
  grad a v c :=
    hcol (levelMix_mem_OnmFull_unconditional W n p a v (anmLgen W p p c)
      (anmLgen_mem_Onm W p p c))

end VOA
