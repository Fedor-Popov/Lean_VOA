/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAGenuineRho
import VOA.Modules.ZhuVermaAnArchActionNaturalLevelShift

/-!
# `hact` as an unconditional TERM — the U-INDEPENDENT-σ Construction-A datum

`Modules.ZhuVermaAnArchActionNaturalLevelShift` proved DJ Prop 3.4 (`MUActionNatural F`) for any
family whose per-`U` `𝒱`-action is the **bottom-independent-σ** level-shift action, carrying that
form as the hypothesis `hact`.  For the genuine Construction-A family
(`InducedAssignment.BimodGenuineConstructionA`, `ZhuVermaAnArchAGenuineRho`) the action *is* the
level-shift action (`BimodGenuineConstructionA.mudata_act`) — but with a **per-`U`** shift `σ U`, so
`hact` (which needs one bottom-independent `σ`) was not yet a term.

This file closes that: the level-shift assignment `σ` and its descents `hL`/`hR` genuinely depend
only on the VOA grading, **not** on the bottom `U` (that bottom-independence *is* the content of
Construction A — the first-factor bimodule composition never touches `U`).  We package that
structurally as `BimodGenuineConstructionAUniform`, a variant of `BimodGenuineConstructionA` whose
`σ`/`hL`/`hR` are U-independent, and show `hact` is a **term** for the resulting family.
Consequently `isoInvariant` (functoriality of `L(·)` on bottoms) rests, on this datum, on
**exactly** `MUJNatural F` (DJ Prop 3.5, canonicity of `J`) — DJ Prop 3.4 is fully discharged.

## What is built (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`InducedAssignment.BimodGenuineConstructionAUniform`** — the U-independent-σ Construction-A
  datum: identical to `BimodGenuineConstructionA` except `σ : ℤ → ℕ → ℕ` (and `hL`/`hR : ∀ m n`) are
  bottom-independent.  All the per-`U` analytic residues (`hderiv`/`hbracket`/`hvac`/`htr`/`hmi`/…)
  are carried exactly as before (the module `M(U)` still genuinely depends on `U`).
* **`…Uniform.toBimodGenuineConstructionA`** — the constant embedding into
  `BimodGenuineConstructionA` (`σ U := σ`, etc.), so all of `AGenuineRho`'s downstream machinery
  (`mudata`, `toLUFamily`,
  `mudata_act`) applies verbatim.
* **`…Uniform.hact`** — **`hact` as a TERM**: the per-`U` action of `F = G.toLUFamily ludata` is the
  bottom-independent-σ level-shift action `levelShiftAct W U σ …`, on the nose (via `mudata_act`,
  `σ` constant).
* **`…Uniform.isoInvariant`** — `isoInvariant` for the uniform datum from **only** `MUJNatural F`
  (DJ Prop 3.4 supplied by the term `hact`), via `isoInvariant_of_levelShift`.
* **`phase4_of_dj28_uniform`** — the faithful (`hall`-free) `Function.Bijective (forwardMapIrr W)`
  threaded through the Hinge, with the `hiso` clause resting on the single residual `MUJNatural F`.

## The exact remaining `hiso` residual (honest)

After this file the functoriality clause `hiso` of Zhu Theorem 5.3.4 rests, for the genuine
uniform Construction-A family, on **exactly one** carried DJ residual: `MUJNatural F` — DJ Prop 3.5,
the canonicity of the maximal proper graded submodule `J` under the functor map `M(φ) = 1 ⊗ φ`.
DJ Prop 3.4 (`MUActionNatural`) is an unconditional theorem.  (The other structural residues —
the maximal-`J` datum `lumax` inside `F`, the generation-from-bottom `G`, and the keystone
`MUGradedAction` — are unchanged.)

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; Frenkel–Zhu;
Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchAGenuineRho` (`BimodGenuineConstructionA`, `mudata_act`,
`toLUFamily`), `ZhuVermaAnArchActionNaturalLevelShift` (`MUActionNatural_of_levelShift`,
`isoInvariant_of_levelShift`, `phase4_of_dj28_levelShiftNatural`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

open VHat VHat.VHatRep MUModuleData

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The U-independent-σ Construction-A datum -/

/-- **The U-INDEPENDENT-σ genuine Construction-A datum.**  Identical to `BimodGenuineConstructionA`
except the level-shift assignment `σ : ℤ → ℕ → ℕ` and its descents `hL`/`hR : ∀ m n` are
**bottom-independent** — the physically correct statement of Construction A, where the loop mode
acts by the first-factor bimodule composition `anmComposeBilin` that never touches the bottom `U`.
The
per-`U` analytic residues (`hderiv`/`hbracket`/`hvac`/`htr`/`hmi`/`hL0`/`hfin`/`hbot`) are carried
exactly as in `BimodGenuineConstructionA` (the module `M(U)` still depends on `U`). -/
structure BimodGenuineConstructionAUniform (W : VertexOperatorAlgebra 𝒱) where
  /-- The **bottom-independent** level-shift assignment `σ m n`. -/
  σ : ℤ → ℕ → ℕ
  /-- The **bottom-independent** DJ Prop 3.4 left level-shift descents. -/
  hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0
  /-- The **bottom-independent** DJ Prop 3.4 right level-shift descents. -/
  hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0
  /-- The Borcherds derivative relation of the level-shift action (per `U`). -/
  hderiv : ∀ (U : AMod W) (a : 𝒱) (m : ℤ),
    levelShiftActGen W U σ hL hR m (W.L (-1) a)
      + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0
  /-- The Borcherds bracket relation of the level-shift action (per `U`). -/
  hbracket : ∀ (U : AMod W) (a b : 𝒱) (m k : ℤ),
    assembleAct (levelShiftActGen W U σ hL hR)
        (vloopBracket W (single m a) (single k b))
      = ⁅levelShiftActGen W U σ hL hR m a, levelShiftActGen W U σ hL hR k b⁆
  /-- Carried explicitly: `MUGradedAction W`, the DJ §3 action well-definedness. -/
  graded : MUGradedAction W
  /-- The lowest weight `h` of `M(U)`. -/
  hU : AMod W → ℂ
  /-- Vacuum creation of the level-shift representation (per `U`). -/
  hvac : ∀ U : AMod W, VacuumCreation (levelShiftRho W U σ hL hR (hderiv U) (hbracket U))
  /-- Truncation/field of the level-shift representation (per `U`). -/
  htr : ∀ U : AMod W,
    VHat.VHatRep.ActModeTruncated (levelShiftRho W U σ hL hR (hderiv U) (hbracket U))
  /-- The module-iterate residual of the level-shift representation (per `U`). -/
  hmi : ∀ U : AMod W,
    VHat.VHatRep.ModuleIterate (levelShiftRho W U σ hL hR (hderiv U) (hbracket U))
  /-- The grading scalar `L₀ = h + n` (per `U`). -/
  hL0 : ∀ (U : AMod W) (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
    (levelShiftRho W U σ hL hR (hderiv U) (hbracket U)).actMode W.conformalVector 1 x
      = ((hU U : ℂ) + n) • x
  /-- Finiteness of each graded piece (per `U`). -/
  hfin : ∀ (U : AMod W) (n : ℕ), FiniteDimensional ℂ (MU.deg W U n)
  /-- Bottom nonvanishing of each `M(U)`. -/
  hbot : ∀ U : AMod W, MU.deg W U 0 ≠ ⊥

namespace BimodGenuineConstructionAUniform

variable (G : BimodGenuineConstructionAUniform W)

/-- **The constant embedding into `BimodGenuineConstructionA`** (`σ U := σ`, etc.).  Definitionally
`(toBimodGenuineConstructionA G).σ U = G.σ` (constant), so every downstream construction of
`ZhuVermaAnArchAGenuineRho` (`mudata`, `toLUFamily`, `mudata_act`) applies verbatim. -/
noncomputable def toBimodGenuineConstructionA : BimodGenuineConstructionA W where
  σ := fun _ => G.σ
  hL := fun _ => G.hL
  hR := fun _ => G.hR
  hderiv := G.hderiv
  hbracket := G.hbracket
  graded := G.graded
  hU := G.hU
  hvac := G.hvac
  htr := G.htr
  hmi := G.hmi
  hL0 := G.hL0
  hfin := G.hfin
  hbot := G.hbot

@[simp] theorem toBimodGenuineConstructionA_σ (U : AMod W) :
    (G.toBimodGenuineConstructionA).σ U = G.σ := rfl

@[simp] theorem toBimodGenuineConstructionA_hU :
    (G.toBimodGenuineConstructionA).hU = G.hU := rfl

/-- The `LUFamily W` of the uniform Construction-A datum, given the per-`U` maximal-`J` datum. -/
noncomputable def toLUFamily
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U)) :
    LUFamily W :=
  (G.toBimodGenuineConstructionA).toLUFamily ludata

/-! ## `hact` as a TERM, and `isoInvariant` from only `MUJNatural` -/

/-- **`hact` as a TERM.**  The per-`U` `𝒱`-action of `F = G.toLUFamily ludata` **is** the
bottom-independent-σ level-shift action `levelShiftAct W U G.σ …` — on the nose, because the
underlying `BimodGenuineConstructionA` has the constant shift `σ U ≡ G.σ` (via
`BimodGenuineConstructionA.mudata_act`, then `LinearMap.ext`).  This is precisely the `hact`
hypothesis of `MUActionNatural_of_levelShift`, discharged. -/
theorem hact
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U))
    (U : AMod W) (u : 𝒱) (n : ℤ) :
    ((G.toLUFamily ludata).mudata U).weak.act u n
      = VHat.levelShiftAct W U G.σ n (fun k => G.hL n k) (fun k => G.hR n k) u := by
  -- `.weak.act u n` is a bare function `M → M`; check pointwise.
  -- `(G.toLUFamily ludata).mudata U = (toBimodGenuineConstructionA G).mudata U`, whose action is
  -- `levelShiftAct` with the constant shift `σ U = G.σ` (definitionally).
  refine funext fun x => ?_
  exact (G.toBimodGenuineConstructionA).mudata_act U u n x

/-- **`isoInvariant` for the uniform datum from ONLY `MUJNatural F`.**  DJ Prop 3.4 is supplied by
the term `hact`; only DJ Prop 3.5 (`MUJNatural`, canonicity of `J`) is carried.  So the
functoriality clause `hiso` of Zhu Theorem 5.3.4 rests, for the genuine uniform Construction-A
family, on exactly one residual. -/
theorem isoInvariant
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U))
    (hJ : MUJNatural (G.toLUFamily ludata)) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W ((G.toLUFamily ludata).K U₁) ((G.toLUFamily ludata).K U₂) :=
  isoInvariant_of_levelShift (G.toLUFamily ludata) G.σ G.hL G.hR (G.hact ludata) hJ

end BimodGenuineConstructionAUniform

end InducedAssignment

/-! ## The faithful hinge on the single `hiso` residual `MUJNatural` -/

/-- **`phase4_of_dj28_uniform` — the faithful, `hall`-free Zhu Theorem 5.3.4 bijection
`Φ(𝒱) ↔ Irr A(𝒱)` (`forwardMapIrr`) for the genuine uniform Construction-A family, with `hiso`
resting on the SINGLE residual `MUJNatural`.**

Threads the uniform datum through `phase4_of_dj28_neededSlice` (Hinge): the `𝒱`-action is the
bottom-independent-σ level-shift action (so DJ Prop 3.4 is the term `hact`), and the only carried
`hiso` residual is `MUJNatural G.toLUFamily` (DJ Prop 3.5).  The remaining structural inputs are the
maximal-`J` datum `ludata` (inside `F`), the generation-from-bottom family `G'`, the keystone
`NeededSliceMems`, and `A`/`hirr`. -/
theorem phase4_of_dj28_uniform {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U))
    (hJ : InducedAssignment.MUJNatural (G.toLUFamily ludata))
    (G' : InducedAssignment.GenFromBottomGFamily (G.toLUFamily ludata)) :
    Function.Bijective (forwardMapIrr W) :=
  phase4_of_dj28_neededSlice hslice A hirr (G.toLUFamily ludata)
    (G.isoInvariant ludata hJ) G'

end VOA
