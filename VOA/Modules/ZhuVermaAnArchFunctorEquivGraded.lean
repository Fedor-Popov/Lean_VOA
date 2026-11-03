/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchHoleMuEquiv
import VOA.Modules.ZhuVermaAnArchMULW

/-!
# The genuine map `M(φ)=1⊗φ` is a **graded** iso preserving the bottom — the `MUJNatural` crux

`Modules.ZhuVermaAnArchHoleMuEquiv` built the genuine Dong–Jiang functor map
`M(φ) = MU.functorEquiv φ = ⊕ₙ (id ⊗ φ)` and reduced `hiso` to `MUActionNatural` (DJ Prop 3.4,
proved in `ZhuVermaAnArchActionNaturalLevelShift` for the level-shift construction) and `MUJNatural`
(DJ Prop 3.5 — canonicity of `J` under `M(φ)`).

This file proves the **reusable crux** of `MUJNatural`: the genuine map `M(φ)` is a **graded** linear
isomorphism — it carries each level-`n` layer `MU.deg W U₁ n` *onto* the level-`n` layer
`MU.deg W U₂ n` (`functorEquiv` acts layer-by-layer as `functorPiece φ n`, a `LinearEquiv`), and in
particular carries the **bottom** `MU.deg W U 0` (`= M(U)_h = cweight h`) onto the bottom.  This is
exactly the structural fact DJ Prop 3.5 rests on: `M(φ)` induces a *bijection* of graded submodules
preserving the bottom, hence carries the canonical maximal bottom-trivial graded submodule `J₁` onto
`J₂`.

## What is built (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`MU.functorEquiv_comp_incl`** — `M(φ) ∘ incl_{U₁} n = incl_{U₂} n ∘ functorPiece φ n`
  (map level).
* **`MU.functorEquiv_map_deg`** — `M(φ)` maps the level-`n` layer onto the level-`n` layer:
  `(MU.deg W U₁ n).map M(φ) = MU.deg W U₂ n`.  (The genuine map is a *graded* iso.)
* **`MU.functorEquiv_map_bottom`** — the bottom `MU.deg W U 0` is carried onto the bottom.
* **`MUModuleData.functorEquiv_map_cweight_bottom`** — the ℂ-graded bottom
  `M(U)_{h} = cweight h = MU.deg 0` is carried onto the corresponding bottom layer (the `n = 0`
  specialization, stated on `cweight`).

## What `MUJNatural` still needs (honest)

The genuine `MUJNatural F : map M(φ) J₁ = J₂` becomes a theorem once `J` is the **canonical**
maximal bottom-trivial graded submodule `⨆ {Q graded | Q ⊓ M(U)_bottom = ⊥}`: `M(φ)` (a graded iso
preserving the bottom, this file) permutes the indexing set of bottom-trivial graded submodules and
commutes with `⨆` (`Submodule.map_iSup`), so it carries the sup onto the sup.  The remaining content
is the *canonical* construction of `J` (its bottom-triviality and graded-simplicity — the deep
DLM/Dong–Jiang maximal-`J` theory, currently carried in `LUMaxData`).  This file supplies the
graded-iso half.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.5, Thm 4.13; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchHoleMuEquiv` (`MU.functorEquiv`, `functorEquiv_incl`, `functorPiece`),
`ZhuVermaAnArchMU` (`MU.deg`, `MU.incl`), `ZhuVermaAnArchMULW` (`cweight`, `cweight_add_nat`).
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace MU

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`M(φ) ∘ incl_{U₁} n = incl_{U₂} n ∘ functorPiece φ n`** (map level) — the genuine functor map
acts layer-by-layer as the `LinearEquiv` `functorPiece φ n = id ⊗ φ`. -/
theorem functorEquiv_comp_incl {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) (n : ℕ) :
    (MU.functorEquiv φ).toLinearMap ∘ₗ MU.incl W U₁ n
      = (MU.incl W U₂ n).comp (MU.functorPiece φ n).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MU.functorEquiv_incl]

/-- **`M(φ)` is a graded iso — it carries each level-`n` layer onto the level-`n` layer.**
`MU.deg W U n = range (incl … n)`; `M(φ)` maps it to `range (M(φ) ∘ incl_{U₁} n) =
range (incl_{U₂} n ∘ functorPiece φ n)`, and `functorPiece φ n` is a `LinearEquiv` (range `⊤`), so
this is `range (incl_{U₂} n) = MU.deg W U₂ n`. -/
theorem functorEquiv_map_deg {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) (n : ℕ) :
    (MU.deg W U₁ n).map (MU.functorEquiv φ).toLinearMap = MU.deg W U₂ n := by
  rw [MU.deg, ← LinearMap.range_comp, functorEquiv_comp_incl, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (MU.functorPiece φ n).surjective, Submodule.map_top, MU.deg]

/-- **`M(φ)` carries the bottom `MU.deg W U 0` onto the bottom** — the `n = 0` case of
`functorEquiv_map_deg`; the graded-iso property at the bottom layer. -/
theorem functorEquiv_map_bottom {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) :
    (MU.deg W U₁ 0).map (MU.functorEquiv φ).toLinearMap = MU.deg W U₂ 0 :=
  functorEquiv_map_deg φ 0

end MU

namespace MUModuleData

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`M(φ)` carries the ℂ-graded bottom `M(U)_h = cweight h = MU.deg 0` onto the corresponding
bottom.**  Stated on `cweight` (the ℂ-grading) via `cweight_add_nat` (`cweight (h+0) = MU.deg 0`);
this is the form `J`'s bottom-triviality `J ⊓ M(U)_h = ⊥` is phrased against. -/
theorem functorEquiv_map_cweight_bottom {U₁ U₂ : AMod W} {h₁ h₂ : ℂ}
    (D₁ : MUModuleData W U₁ h₁) (D₂ : MUModuleData W U₂ h₂) (φ : AModEquiv W U₁ U₂) :
    (D₁.cweight h₁).map (MU.functorEquiv φ).toLinearMap = D₂.cweight h₂ := by
  have e₁ : D₁.cweight h₁ = MU.deg W U₁ 0 := by
    have := D₁.cweight_cast 0
    simpa using this
  have e₂ : D₂.cweight h₂ = MU.deg W U₂ 0 := by
    have := D₂.cweight_cast 0
    simpa using this
  rw [e₁, e₂, MU.functorEquiv_map_bottom]

end MUModuleData

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
