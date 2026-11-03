/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchPhase4Bijection
import VOA.Modules.ZhuVermaAnArchDJ28Term1Capstone

/-!
# The Zhu-5.3.4 bijection on the SINGLE Half-A residual `CrossCircCore` (+ minimal Half-B fields).

This file proves the cleanest *conditional* Zhu Theorem 5.3.4 bijection: `Function.Bijective
(forwardMapIrr W)` from the single homogeneous cross-level-circle residue

  `CrossCircCore W n`  (`ZhuVermaAnArchMUcross`) :=
    `∀ K, ∀ a ∈ 𝒱_K, ∀ c d, resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`,

together with the genuine Frenkel–Zhu/DLM Construction-A / generalized-Verma data (Half B).

`(∀ n, CrossCircCore W n)` is the whole remaining A-direction content of the theorem: it
de-homogenizes (`anmRight_zero_crossCirc_mem_Onm_of_core`) to the general cross-circle membership
`hcross`, which (via `neededSliceMems_of_crossCirc`) is the keystone `hslice : NeededSliceMems W`,
AND (via `mUGradedAction_of_crossCircCore`, `ZhuVermaAnArchDJ28Term1Capstone`) is the construction
field `graded : MUGradedAction W` of the Construction-A bundle.  So the SAME Half-A residue discharges
*both* the keystone and the `graded` field of Half B.

Three statements are proved, from most-bundled to most-peeled:

* **`zhu534_of_crossCircCore`** — `(∀ n, CrossCircCore W n) → StructuralData W →
  Function.Bijective (forwardMapIrr W)`.  Half B carried whole as `sd : StructuralData W`.
* **`zhu534_of_crossCircCore_fields`** — Half B carried as its individual fields
  `A`/`hirr`/`G`/`bregen`/`G'` (each named explicitly).
* **`zhu534_of_crossCircCore_peelGraded`** — the same, but with `G`'s `graded : MUGradedAction W`
  field discharged (built from `CrossCircCore`), so the carried construction datum is the
  `graded`-free bundle `G0 : GAUniformNoGraded W` (all twelve non-`graded` Construction-A fields).

Every headline term is axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free; no `sorry`/
`admit`/`native_decide`/`axiom` (only this file added, plus its import to
`Modules.lean`).  The bijection row is **not** flipped — these are honest conditional statements
carrying the genuine deep Frenkel–Zhu/DLM residues as hypotheses.

## References
Dong–Jiang, Math. Z. 259 (2008) Lemma 2.8, Thm 4.13, Prop 3.4/3.5; Dong–Li–Mason J. Algebra 206
(1998); Frenkel–Zhu (generalized Verma); Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchPhase4Bijection` (`zhu534_bijection`), `ZhuVermaAnArchStructuralClose`
(`bijection_of_structural`, `StructuralData`, `BottomRegenData`), `ZhuVermaAnArchDJ28Term1Capstone`
(`mUGradedAction_of_crossCircCore`), `ZhuVermaAnArchMUcross`
(`CrossCircCore`, `anmRight_zero_crossCirc_mem_Onm_of_core`),
`ZhuVermaAnArchConstructionAUniform` (`BimodGenuineConstructionAUniform`).
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra
open Finsupp
open VHat VHat.VHatRep

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`hcross` from `(∀ n, CrossCircCore W n)`** — the general cross-level-circle membership family
`∀ n a c d, anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0`, de-homogenized from the homogeneous
core `CrossCircCore` via `anmRight_zero_crossCirc_mem_Onm_of_core`.  This is the single family through
which the whole A-direction of Zhu Thm 5.3.4 (`hslice`/`MUGradedAction`) is expressed. -/
theorem hcross_of_crossCircCore (W : VertexOperatorAlgebra 𝒱)
    (hcore : ∀ n : ℕ, CrossCircCore W n) :
    ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0 :=
  fun n a c d => anmRight_zero_crossCirc_mem_Onm_of_core W n (hcore n) a c d

/-- **`zhu534_of_crossCircCore` — the Zhu-5.3.4 bijection from the single Half-A residual
`CrossCircCore` plus the whole Half-B bundle `StructuralData W`.**

The keystone `hslice : NeededSliceMems W` is produced from `(∀ n, CrossCircCore W n)` alone (via
`hcross_of_crossCircCore` + `neededSliceMems_of_crossCirc`, inside `zhu534_bijection`); `sd` carries
the genuine Frenkel–Zhu/DLM generalized-Verma construction (`⟨A, hirr, G, bregen, G'⟩`).  So the whole
bijection rests on the SINGLE Half-A residue `CrossCircCore` and the Half-B construction bundle. -/
theorem zhu534_of_crossCircCore (W : VertexOperatorAlgebra 𝒱)
    (hcore : ∀ n : ℕ, CrossCircCore W n)
    (sd : InducedAssignment.StructuralData W) :
    Function.Bijective (forwardMapIrr W) :=
  zhu534_bijection W (hcross_of_crossCircCore W hcore) sd

/-- **`zhu534_of_crossCircCore_fields` — the Zhu-5.3.4 bijection with Half B carried as its individual
`StructuralData` fields, each named explicitly.**

Identical content to `zhu534_of_crossCircCore`, but the Half-B bundle is un-packed: the lifting datum
`A`/`hirr`, the genuine uniform Construction-A datum `G`, the generation-from-bottom residue `bregen`,
and the generation-from-bottom lift `G'`.  The single Half-A residue is `(∀ n, CrossCircCore W n)`. -/
theorem zhu534_of_crossCircCore_fields (W : VertexOperatorAlgebra 𝒱)
    (hcore : ∀ n : ℕ, CrossCircCore W n)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (bregen : InducedAssignment.BottomRegenData G)
    (G' : InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  zhu534_of_crossCircCore W hcore ⟨A, hirr, G, bregen, G'⟩

/-! ## Peeling the `graded : MUGradedAction W` field off the Construction-A bundle

The uniform Construction-A datum `BimodGenuineConstructionAUniform` carries a field
`graded : MUGradedAction W` (the DJ §3 action well-definedness).  This field is *literally*
`MUGradedAction W`, which `mUGradedAction_of_crossCircCore` produces from `(∀ n, CrossCircCore W n)`.
Since `mudata` (hence the types of `bregen`/`G'`) is built through `toGenuineRhoFamily`, which uses
only `σ`/`hL`/`hR`/`hderiv`/`hbracket`/`hU`/`hvac`/`htr`/`hmi`/`hL0`/`hfin`/`hbot` and **never**
`graded`, the `graded` field can be discharged from the same Half-A residue that gives the keystone —
leaving the `graded`-free bundle below as the carried construction datum. -/

/-- **The `graded`-free uniform Construction-A datum** — `BimodGenuineConstructionAUniform` minus its
`graded : MUGradedAction W` field.  All twelve genuine Frenkel–Zhu/DLM construction fields (the
bottom-independent level-shift assignment `σ`, its descents `hL`/`hR`, the Borcherds relations
`hderiv`/`hbracket`, the lowest weight `hU`, and the per-`U` analytic residues
`hvac`/`htr`/`hmi`/`hL0`/`hfin`/`hbot`).  The removed `graded` field is supplied downstream from
`CrossCircCore` via `mUGradedAction_of_crossCircCore`. -/
structure GAUniformNoGraded (W : VertexOperatorAlgebra 𝒱) where
  /-- The bottom-independent level-shift assignment `σ m n`. -/
  σ : ℤ → ℕ → ℕ
  /-- The bottom-independent DJ Prop 3.4 left level-shift descents. -/
  hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0
  /-- The bottom-independent DJ Prop 3.4 right level-shift descents. -/
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
  /-- The lowest weight `h` of `M(U)`. -/
  hU : AMod W → ℂ
  /-- Vacuum creation of the level-shift representation (per `U`). -/
  hvac : ∀ U : AMod W, VacuumCreation (levelShiftRho W U σ hL hR (hderiv U) (hbracket U))
  /-- Truncation/field of the level-shift representation (per `U`). -/
  htr : ∀ U : AMod W,
    ActModeTruncated (levelShiftRho W U σ hL hR (hderiv U) (hbracket U))
  /-- The module-iterate residual of the level-shift representation (per `U`). -/
  hmi : ∀ U : AMod W,
    ModuleIterate (levelShiftRho W U σ hL hR (hderiv U) (hbracket U))
  /-- The grading scalar `L₀ = h + n` (per `U`). -/
  hL0 : ∀ (U : AMod W) (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
    (levelShiftRho W U σ hL hR (hderiv U) (hbracket U)).actMode W.conformalVector 1 x
      = ((hU U : ℂ) + n) • x
  /-- Finiteness of each graded piece (per `U`). -/
  hfin : ∀ (U : AMod W) (n : ℕ), FiniteDimensional ℂ (MU.deg W U n)
  /-- Bottom nonvanishing of each `M(U)`. -/
  hbot : ∀ U : AMod W, MU.deg W U 0 ≠ ⊥

/-- **Re-attach the `graded` field from `CrossCircCore`.**  Builds the full uniform Construction-A
datum `BimodGenuineConstructionAUniform` from a `graded`-free bundle `G0` by supplying
`graded := mUGradedAction_of_crossCircCore W hcore`.  Every other field is `G0`'s verbatim, so the
induced `M(U)` (`mudata`, which never reads `graded`) is unchanged. -/
noncomputable def GAUniformNoGraded.toFull {W : VertexOperatorAlgebra 𝒱}
    (G0 : GAUniformNoGraded W) (hcore : ∀ n : ℕ, CrossCircCore W n) :
    InducedAssignment.BimodGenuineConstructionAUniform W where
  σ := G0.σ
  hL := G0.hL
  hR := G0.hR
  hderiv := G0.hderiv
  hbracket := G0.hbracket
  graded := mUGradedAction_of_crossCircCore W hcore
  hU := G0.hU
  hvac := G0.hvac
  htr := G0.htr
  hmi := G0.hmi
  hL0 := G0.hL0
  hfin := G0.hfin
  hbot := G0.hbot

/-- **`zhu534_of_crossCircCore_peelGraded` — the Zhu-5.3.4 bijection with the construction bundle's
`graded : MUGradedAction W` field discharged.**

The carried construction datum is the `graded`-free bundle `G0 : GAUniformNoGraded W`; the missing
`graded` field is supplied internally from the SAME Half-A residue `(∀ n, CrossCircCore W n)` via
`mUGradedAction_of_crossCircCore` (`GAUniformNoGraded.toFull`).  So one residue — `CrossCircCore` —
discharges *both* the keystone `hslice : NeededSliceMems W` and the construction field
`graded : MUGradedAction W`; the remaining carried Half-B fields are exactly `A`/`hirr`, the twelve
non-`graded` Construction-A fields (`G0`), `bregen`, and `G'`. -/
theorem zhu534_of_crossCircCore_peelGraded (W : VertexOperatorAlgebra 𝒱)
    (hcore : ∀ n : ℕ, CrossCircCore W n)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (G0 : GAUniformNoGraded W)
    (bregen : InducedAssignment.BottomRegenData (G0.toFull hcore))
    (G' : InducedAssignment.GenFromBottomGFamily
      ((G0.toFull hcore).toLUFamily
        (fun U => (InducedAssignment.lumaxOfRegen (G0.toFull hcore) bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  zhu534_of_crossCircCore W hcore ⟨A, hirr, G0.toFull hcore, bregen, G'⟩

end VOA

-- Integrity gate (axiom-clean: [propext, Classical.choice, Quot.sound]; NO sorryAx/pbw).
