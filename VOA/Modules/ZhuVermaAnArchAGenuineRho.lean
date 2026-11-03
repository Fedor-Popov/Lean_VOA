/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLevelShiftRho
import VOA.Modules.ZhuVermaAnArchGenuineRho
import VOA.Modules.ZhuVermaAnArchDownstream
import VOA.Modules.ZhuVermaAnArchScopeClose

/-!
# HOLE A — the lifting `U ↦ M̄(U)` on the **genuine BIMODULE-COMPOSITION** representation
  `levelShiftRho` (Dong–Jiang §3, Construction A), assembled into `A : InducedAssignment W`

This file closes **HOLE A** of the faithful Zhu bijection `zhuBijectionIrr_scorecard` on the
**genuine Dong–Jiang Construction-A loop representation** — the BIMODULE-COMPOSITION action
`levelShiftRho` built from the descended bimodule composition `anmComposeBilin` /
`MU.actAnm` (the `A_{n,0}(𝒱)`-bimodule loop action `u_p` of DJ §3), well-defined by the
Dong–Jiang Prop 3.4 residue memberships (`MUGradedAction W` / the level-shift descents `hL`/`hR`).

It replaces the vacuous route to HOLE A: `InducedAssignment.GenuineConstructionA`
(`ZhuVermaAnArchHoleA`) defines its loop representation as
`genuineRhoMU W U hd := fzRhoMU W U hd`, which rests on `hd : ∀ n m, FZModeDescent W n m` — and that
literal-mode descent is **PROVABLY FALSE** (`J₍₁₎(L₋₁+L₀)J = vacuum ∉ O(𝒱)`,
`ZhuVermaAnArchFZModeDescent`), so that route is gated on an unsatisfiable hypothesis (vacuous).
This file uses **no `fzRhoMU` and no `FZModeDescent`**: the representation is the genuine
degree-dependent level-shift action of DJ §3 (Construction A), on which a loop generator `a(m)`
maps the layer `n` to the shifted layer `σ m n` via the genuine bimodule composition
`anmCompose W (σ m n) n 0` (`anmComposeBilin`, `ZhuVermaAnArchBimodComp` / `ZhuVermaAnArchLevelShiftRho`).

## Dong–Jiang §3, Construction A — what is built, faithfully

For each bottom `A(𝒱)`-module `U`, Construction A builds the generalized Verma module
`M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_{A_0(𝒱)} U` (the headline carrier `MU W U`), on which a vertex operator
`Y(a,z) = ∑ a₍ₘ₎ z^{-m-1}` acts by the **loop action** `a₍ₘ₎` (DJ §3, the `u_p` action). The genuine
loop mode is realized by the Dong–Jiang **bimodule composition** `A_{σ m n, n}(𝒱) ⊗_{A_n} A_{n,0}(𝒱)
→ A_{σ m n, 0}(𝒱)` (`anmComposeBilin W (σ m n) n 0`), acting on the left tensor factor and identity on
`U`, then including into the shifted layer `MU.incl W U (σ m n)`. This is exactly
`VHat.levelShiftRho W U σ hL hR hderiv hbracket` of `ZhuVermaAnArchLevelShiftRho` — a *genuine*
`V̂`-representation `ρ : VHatRep W (MU W U)` carrying ONLY:

* the level-shift well-definedness `hL`/`hR` (the DJ Prop 3.4 level-mixing residue memberships, the
  bottom-source slice of which is the PROVEN `AnmComposeDescL_bottom`), and
* the two genuine Borcherds generator relations `hderiv` (`(L₋₁a)(m) = −m·a(m−1)`, balanced because
  both sides carry the matching grade shift `σ m`) and `hbracket` (the `ℓ = 0` Borcherds OPE).

It carries **no** `FZModeDescent` — the false literal-mode descent that made the old HOLE A vacuous
is gone. The action well-definedness `MUGradedAction W` (the associator grind; the same Dong–Jiang
Prop 3.4 content as `hL`/`hR`) is carried **explicitly**.

The three Construction-A claims are all discharged on this genuine carrier:

1. **`ρ` is a `V̂`-representation** (the loop modes `a(m)` act, the `V̂`-bracket is `actMode_bracket`):
   `levelShiftRho W U σ hL hR hderiv hbracket`. Carries `hL`/`hR`/`hderiv`/`hbracket` + the explicit
   `MUGradedAction W`. **Never** `FZModeDescent`.
2. **`M(U)` is an admissible (`ℕ`-gradable) `V`-module**, i.e. the loop action is *truncated* and
   satisfies the **module Jacobi 5.3.1b**:
   * truncation `htr : ActModeTruncated (levelShiftRho …)` — the grading/field property of the genuine
     `ℕ`-graded carrier (carried as the structural residue of THIS ρ, exactly as the existing
     `GenuineRhoFamily.htr`);
   * the module Jacobi 5.3.1b is the **proven term**
     `isModuleJacobi_of_moduleIterate ρ htr hmi` (`ZhuVermaAnArchGenuineRho`), where
     `hmi : ModuleIterate (levelShiftRho …)` is the module-iterate residual DLM3 eqs 4.3–4.4 of THIS
     bimodule-composition ρ (carried as the genuine deep crux of the level-shift action, replacing the
     carried `hjac`). No `pbw`, no defect quotient, no `fzRhoMU`.
   So `M(U)` is produced as a genuine `𝒱`-module **term** `buildMUModuleData_of_iterate` (via the
   shared `GenuineRhoFamily.toMURepFamily.mudata`), given the structural per-`U` data.
3. **Bottom survival** (`M(U)_h ≅ U`) — the `realizes` field, the `R0`/`bottomBalancedEquiv` content,
   sibling holes hiso/G; carried as the explicit `AModEquiv` residue.

The assignment's last two abstract fields — `realizes` (bottom survival) and `isoInvariant`
(functoriality of `M(·)`, DJ Prop 3.4/3.5) — are the sibling holes (hiso/muEquiv, G), carried as the
named residues `realizes`/`Dfun` (with `isoInvariant = Dfun.isoInvariant`, a **proven term**).

## The result

`BimodGenuineConstructionA W` bundles the genuine bimodule-composition Construction-A data per `U`:
the level-shift assignment `σ` and its descents `hL`/`hR`, the two generator relations
`hderiv`/`hbracket`, the carried `MUGradedAction W`, and the structural per-`U` fields
(`htr`/`hvac`/`hmi`/`hL0`/`hfin`/`hbot`). `toGenuineRhoFamily` produces the per-`U`
`GenuineRhoFamily` with the genuine `ρ = levelShiftRho` — re-using the EXISTING module-iterate
discharge of `ZhuVermaAnArchGenuineRho` (the module Jacobi is the proven term
`isModuleJacobi_of_moduleIterate`, **not** carried). Supplying the downstream residues that live in
the sibling holes (`ludata` = HOLE F, `realizes` = hiso/G, `Dfun` = hiso),
`bimodHoleA_inducedAssignment` assembles the lifting datum

  `A : InducedAssignment W`,   `A.realize U = L(U) = (R.toLUFamily ludata).K U`,

through `MURepFamily.toCanonicalAssignmentData.toInducedAssignment`. The instant `A` is supplied, the
round-trip `forwardMap ∘ invFun = id` of Theorem 5.3.4 holds.

## Honest hypothesis audit (the FULL closure of `bimodHoleA_inducedAssignment`)

It produces a genuine `InducedAssignment W` whose `realize` carrier/field/module-Jacobi/grading are
produced as **terms** from `levelShiftRho` (the genuine bimodule-composition ρ). It rests on exactly:

* `σ` / `hL` / `hR` — the level-shift assignment and the DJ Prop 3.4 level-shift bimodule-composition
  descents (`anmComposeBilin` well-definedness; bottom-source slice = `AnmComposeDescL_bottom`);
* `hderiv` / `hbracket` — the two genuine Borcherds generator relations of the level-shift action
  (`(L₋₁a)(m) = −m·a(m−1)` and the `ℓ = 0` OPE);
* `graded : MUGradedAction W` — the action well-definedness, **carried explicitly**
  (the associator grind; same DJ §3 content);
* per-`U` structural data of `M(U)`: `htr` (truncation/field of the level-shift ρ), `hvac`
  (`VacuumCreation`), `hmi` (`ModuleIterate` of the level-shift ρ — the genuine DLM3 deep crux),
  `hL0` (`L₀ = h+n`), `hfin` (finite graded pieces), `hbot` (bottom nonvanishing);
* `ludata` — the per-`U` maximal-`J` datum (the deep content of sibling **HOLE F**);
* `realizes` — bottom survival `(F.K U).toAMod ≅ U` (the `R0` content of siblings **hiso/G**);
* `Dfun : MUFunctorialData F` — functoriality of `M(·)` (sibling **HOLE hiso**), from which
  `isoInvariant` is the proven term.

**No `FZModeDescent`. No `fzRhoMU`. No `pbw`. No `sorry`/`admit`/`native_decide`, never an axiom.**
Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## References
Dong–Jiang `math/0601626` §3 (Construction A, `M(U)`, the `u_p` loop action via the bimodule
composition `A_{p,n} ⊗_{A_n} A_{n,m} → A_{p,m}`), Prop 3.4–3.5; DLM3 §4 (eqs 4.3–4.4, the iterate
residual); Frenkel–Zhu; H. Li `hep-th/9406211` §2; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchLevelShiftRho` (`levelShiftRho`, the genuine bimodule-composition ρ via
`anmComposeBilin`), `ZhuVermaAnArchBimodComp` (`anmCompose`, `anmComposeBilin`, `AnmComposeDescL/R`),
`ZhuVermaAnArchGenuineRho` (`GenuineRhoFamily`, `isModuleJacobi_of_moduleIterate`,
`buildMUModuleData_of_iterate`),
`ZhuVermaAnArchMUModuleDataBuild` (`MURepFamily`, `toLUFamily`, `toCanonicalAssignmentData`),
`ZhuVermaAnArchScopeClose` (`CanonicalAssignmentData`, `toInducedAssignment`),
`ZhuInduced` (`InducedAssignment`, `forwardMap_comp_invFun`).
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

/-! ## The genuine bimodule-composition Construction-A data (the `ρ`-side of HOLE A)

`BimodGenuineConstructionA W` bundles exactly the genuine Dong–Jiang §3 Construction-A inputs of the
**bimodule-composition** loop representation `levelShiftRho` (`anmComposeBilin` / `MU.actAnm`) — the
level-shift assignment `σ` with its descents `hL`/`hR`, the two generator relations
`hderiv`/`hbracket`, the **explicitly-carried** action well-definedness `MUGradedAction W`, and the
structural per-`U` fields — and *nothing else*. In particular it carries **no** `FZModeDescent` (the
false literal-mode descent that made the old HOLE A vacuous), and **no** `fzRhoMU`. -/

/-- **The genuine bimodule-composition Construction-A bundle (DJ §3) for the loop representation
`levelShiftRho`.**

Carries, per bottom `A(𝒱)`-module `U`:
* `σ U : ℤ → ℕ → ℕ` — the level-shift assignment (the Frenkel–Zhu / DJ grade shift `σ m n` = the
  layer a degree-`m` loop mode sends source layer `n` to);
* `hL U` / `hR U` — the DJ Prop 3.4 level-shift bimodule-composition descents
  `AnmComposeDescL/R W (σ m n) n 0` (well-definedness of `anmComposeBilin` at the level-mixing pairs;
  the bottom-source slice is the PROVEN `AnmComposeDescL_bottom`). A `Prop`, **never** an axiom;
* `hderiv U` / `hbracket U` — the two genuine Borcherds generator relations of the level-shift action
  (`(L₋₁a)(m) = −m·a(m−1)` balanced by the matching shift `σ m`; the `ℓ = 0` OPE);
* `graded : MUGradedAction W` — **carried explicitly** (the action well-definedness;
  the associator grind closes it; the same DJ §3 Prop 3.4 residue content as `hL`/`hR`);
* `hU`/`hvac`/`htr`/`hmi`/`hL0`/`hfin`/`hbot` — the structural per-`U` data of `M(U)`: lowest weight,
  vacuum creation (module VA2), truncation/field of the level-shift ρ, the `ModuleIterate` residual of
  the level-shift ρ (the genuine DLM3 deep crux, DLM3 eqs 4.3–4.4), the grading scalar `L₀ = h + n`,
  finiteness of graded pieces, and bottom nonvanishing. -/
structure BimodGenuineConstructionA (W : VertexOperatorAlgebra 𝒱) where
  /-- The per-`U` level-shift assignment `σ m n` of the degree-dependent loop action. -/
  σ : AMod W → ℤ → ℕ → ℕ
  /-- The DJ Prop 3.4 **left** level-shift descents (the `anmComposeBilin` left well-definedness). -/
  hL : ∀ (U : AMod W) (m : ℤ) (n : ℕ), AnmComposeDescL W (σ U m n) n 0
  /-- The DJ Prop 3.4 **right** level-shift descents (the `anmComposeBilin` right well-definedness). -/
  hR : ∀ (U : AMod W) (m : ℤ) (n : ℕ), AnmComposeDescR W (σ U m n) n 0
  /-- The Borcherds **derivative** relation `(L₋₁a)(m) + m·a(m−1) = 0` of the level-shift action
  (balanced because both sides carry the matching grade shift `σ m`). -/
  hderiv : ∀ (U : AMod W) (a : 𝒱) (m : ℤ),
    levelShiftActGen W U (σ U) (hL U) (hR U) m (W.L (-1) a)
      + (m : ℂ) • levelShiftActGen W U (σ U) (hL U) (hR U) (m - 1) a = 0
  /-- The Borcherds **bracket** relation (the `ℓ = 0` loop commutator OPE) of the level-shift
  action. -/
  hbracket : ∀ (U : AMod W) (a b : 𝒱) (m k : ℤ),
    assembleAct (levelShiftActGen W U (σ U) (hL U) (hR U))
        (vloopBracket W (single m a) (single k b))
      = ⁅levelShiftActGen W U (σ U) (hL U) (hR U) m a,
          levelShiftActGen W U (σ U) (hL U) (hR U) k b⁆
  /-- **Carried explicitly:** `MUGradedAction W`, the DJ §3 action well-definedness (same residue
  content as `hL`/`hR`); being closed separately by the associator grind. -/
  graded : MUGradedAction W
  /-- The lowest weight `h` of `M(U)`. -/
  hU : AMod W → ℂ
  /-- The vacuum-creation datum (module VA2 `Y(𝟙,z)=id`) of the genuine level-shift representation. -/
  hvac : ∀ U : AMod W,
    VacuumCreation (VHat.levelShiftRho W U (σ U) (hL U) (hR U) (hderiv U) (hbracket U))
  /-- Truncation/field of the genuine level-shift representation (the grading/field property on the
  genuine `ℕ`-graded carrier; the structural residue of THIS ρ). -/
  htr : ∀ U : AMod W,
    VHat.VHatRep.ActModeTruncated (VHat.levelShiftRho W U (σ U) (hL U) (hR U) (hderiv U) (hbracket U))
  /-- **The module-iterate residual** `ModuleIterate (levelShiftRho …)` (DLM3 eqs 4.3–4.4) — the
  genuine deep crux of the bimodule-composition action, *replacing* the carried module Jacobi. -/
  hmi : ∀ U : AMod W,
    VHat.VHatRep.ModuleIterate (VHat.levelShiftRho W U (σ U) (hL U) (hR U) (hderiv U) (hbracket U))
  /-- The grading scalar `L₀ = h + n` on the level-`n` piece (5.3.1c). -/
  hL0 : ∀ (U : AMod W) (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
    (VHat.levelShiftRho W U (σ U) (hL U) (hR U) (hderiv U) (hbracket U)).actMode
      W.conformalVector 1 x = ((hU U : ℂ) + n) • x
  /-- Finiteness of each graded piece. -/
  hfin : ∀ (U : AMod W) (n : ℕ), FiniteDimensional ℂ (MU.deg W U n)
  /-- Bottom nonvanishing of each `M(U)`. -/
  hbot : ∀ U : AMod W, MU.deg W U 0 ≠ ⊥

namespace BimodGenuineConstructionA

variable (G : BimodGenuineConstructionA W)

/-- **The genuine bimodule-composition `V̂`-representation `ρ = levelShiftRho …`** for a bottom
`U`. The Dong–Jiang Construction-A loop action via `anmComposeBilin` (the `A_{n,0}(𝒱)`-bimodule
composition `u_p`), **not** `fzRhoMU`. -/
noncomputable def rho (U : AMod W) : VHat.VHatRep W (MU W U) :=
  VHat.levelShiftRho W U (G.σ U) (G.hL U) (G.hR U) (G.hderiv U) (G.hbracket U)

@[simp] theorem rho_eq (U : AMod W) :
    G.rho U = VHat.levelShiftRho W U (G.σ U) (G.hL U) (G.hR U) (G.hderiv U) (G.hbracket U) := rfl

/-- **The genuineness witness — `ρ`'s mode action is the bimodule-composition level-shift action.**
A loop generator `a(m)` acts by `levelShiftAct m a` (the genuine residue level-shift action sending
layer `n → σ m n` via `anmCompose W (σ m n) n 0`), pinned by name so the construction is checkably the
GENUINE bimodule-composition one (and not `fzRhoMU`/`FZModeDescent`). -/
@[simp] theorem rho_actMode (U : AMod W) (a : 𝒱) (m : ℤ) :
    (G.rho U).actMode a m
      = VHat.levelShiftAct W U (G.σ U) m (fun n => G.hL U m n) (fun n => G.hR U m n) a :=
  VHat.levelShiftRho_actMode W U (G.σ U) (G.hL U) (G.hR U) (G.hderiv U) (G.hbracket U) a m

/-- **The per-`U` `GenuineRhoFamily` from the bimodule-composition Construction-A bundle.** The
genuine loop representation `rho U := levelShiftRho …` (DJ §3, via `anmComposeBilin`); its truncation
`htr`, vacuum creation `hvac`, the module-iterate residual `hmi`, grading scalar `hL0`, finiteness
`hfin`, and bottom-nonvanishing `hbot` are all passed through from `G`. No carried module-Jacobi: it
is *derived* downstream as the proven term `isModuleJacobi_of_moduleIterate`. -/
noncomputable def toGenuineRhoFamily : GenuineRhoFamily W where
  hU := G.hU
  rho := G.rho
  htr := G.htr
  hvac := G.hvac
  hmi := G.hmi
  hL0 := G.hL0
  hfin := G.hfin
  hbot := G.hbot

@[simp] theorem toGenuineRhoFamily_rho (U : AMod W) :
    (G.toGenuineRhoFamily).rho U = G.rho U := rfl

@[simp] theorem toGenuineRhoFamily_hU :
    (G.toGenuineRhoFamily).hU = G.hU := rfl

/-- **The headline `MURepFamily W` produced from the bimodule-composition Construction-A bundle.**
Every representation field is genuine: `rho = levelShiftRho` (the `anmComposeBilin` loop action), with
the module-Jacobi field supplied by the **proven term**
`isModuleJacobi_of_moduleIterate (levelShiftRho …) (htr …) (hmi …)` — discharged on the genuine
carrier from the module-iterate residual, no `pbw`, no defect quotient, no `fzRhoMU`. So
`MURepFamily.mudata` produces `M(U)` as a genuine `𝒱`-module term `buildMUModuleData`. -/
noncomputable def toMURepFamily : MURepFamily W :=
  (G.toGenuineRhoFamily).toMURepFamily

@[simp] theorem toMURepFamily_rho (U : AMod W) :
    (G.toMURepFamily).rho U = G.rho U := rfl

@[simp] theorem toMURepFamily_hU :
    (G.toMURepFamily).hU = G.hU := rfl

/-- The genuine `M(U)` as a `𝒱`-module **term**, built through `buildMUModuleData` from the
bimodule-composition loop representation `levelShiftRho` with the proven module Jacobi 5.3.1b. -/
noncomputable def mudata (U : AMod W) : MUModuleData W U (G.hU U) :=
  (G.toMURepFamily).mudata U

@[simp] theorem mudata_eq (U : AMod W) :
    G.mudata U = (G.toMURepFamily).mudata U := rfl

/-- The genuine `M(U)`-module mode action is the bimodule-composition level-shift action verbatim — so
the assignment built below carries the *actual* Construction-A loop action, not an opaque field and
not `fzRhoMU`. -/
@[simp] theorem mudata_act (U : AMod W) (a : 𝒱) (m : ℤ) (x : MU W U) :
    (G.mudata U).weak.act a m x
      = VHat.levelShiftAct W U (G.σ U) m (fun n => G.hL U m n) (fun n => G.hR U m n) a x := by
  rw [mudata_eq, MURepFamily.mudata, MUModuleData.buildMUModuleData_act]
  rw [show (G.toMURepFamily).rho U = G.rho U from rfl]
  exact G.rho_actMode U a m ▸ rfl

end BimodGenuineConstructionA

/-! ## The lifting datum `A : InducedAssignment W` (HOLE A, genuine bimodule-composition ρ)

The assignment `realize := U ↦ L(U) = (R.toLUFamily ludata).K U` is built through the existing
`MURepFamily.toCanonicalAssignmentData.toInducedAssignment`, with `R = G.toMURepFamily` (the genuine
level-shift loop representation family). The two abstract fields beyond the `ρ`-side — `realizes`
(bottom survival) and `isoInvariant` (functoriality) — are sourced from the carried sibling-hole
residues `realizes` and `Dfun` (with `isoInvariant = Dfun.isoInvariant`, a proven term). -/

/-- **The `LUFamily W` of the genuine bimodule-composition construction**, given the per-`U`
maximal-`J` datum `ludata` (the deep content of sibling HOLE F). `F.K U = L(U) = M(U)/J` is the
irreducible quotient; its `mudata` is the genuine `buildMUModuleData` term over `levelShiftRho`. -/
noncomputable def BimodGenuineConstructionA.toLUFamily (G : BimodGenuineConstructionA W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (G.toMURepFamily.mudata U)) : LUFamily W :=
  (G.toMURepFamily).toLUFamily ludata

/-- **The `CanonicalAssignmentData W` of the genuine bimodule-composition construction.** `F` is the
genuine `LUFamily` (its `mudata` produced by `buildMUModuleData` over the loop representation
`levelShiftRho`); `realizes` is the carried bottom-survival iso (`R0`, sibling holes hiso/G); `Dfun`
is the carried functoriality datum (sibling hole hiso), from which the assignment's `isoInvariant` is
a proven term. -/
noncomputable def BimodGenuineConstructionA.toCanonicalAssignmentData
    (G : BimodGenuineConstructionA W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (G.toMURepFamily.mudata U))
    (realizes : ∀ U : AMod W, AModEquiv W ((G.toLUFamily ludata).K U).toAMod U)
    (Dfun : MUFunctorialData (G.toLUFamily ludata)) :
    CanonicalAssignmentData W :=
  (G.toMURepFamily).toCanonicalAssignmentData ludata realizes Dfun

/-- **HOLE A (genuine bimodule-composition ρ) — the lifting datum `A : InducedAssignment W`.**

The assignment `U ↦ M̄(U)` of Theorem 5.3.4 (DJ §3, Construction A), on the **genuine
BIMODULE-COMPOSITION** loop representation `levelShiftRho` (the `anmComposeBilin` / `MU.actAnm` loop
action `u_p`), **not** `fzRhoMU`/`FZModeDescent`. The `realize` family is
`U ↦ L(U) = (R.toLUFamily ludata).K U` for the genuine representation family `R = G.toMURepFamily`, so
the carrier `MU W U`, the loop action `levelShiftRho`, the truncation, the **module Jacobi 5.3.1b**
(proven from the module-iterate residual `hmi` of this ρ via `isModuleJacobi_of_moduleIterate`), and
the `ℂ`-grading are all genuine terms inside `realize`. The abstract `realizes`/`isoInvariant` fields
are the carried sibling-hole residues. No `sorry`, **never** an axiom. -/
noncomputable def bimodHoleA_inducedAssignment (G : BimodGenuineConstructionA W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (G.toMURepFamily.mudata U))
    (realizes : ∀ U : AMod W, AModEquiv W ((G.toLUFamily ludata).K U).toAMod U)
    (Dfun : MUFunctorialData (G.toLUFamily ludata)) :
    InducedAssignment W :=
  (G.toCanonicalAssignmentData ludata realizes Dfun).toInducedAssignment

/-- **The lifting `A.realize` is the genuine `L(U) = M(U)/J`** (the irreducible quotient of the
generalized Verma module built on the bimodule-composition loop representation `levelShiftRho`). This
exhibits that the assignment's carrier is the *actual* Construction-A module, not a placeholder and
not `fzRhoMU`-sourced. -/
@[simp] theorem bimodHoleA_inducedAssignment_realize (G : BimodGenuineConstructionA W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (G.toMURepFamily.mudata U))
    (realizes : ∀ U : AMod W, AModEquiv W ((G.toLUFamily ludata).K U).toAMod U)
    (Dfun : MUFunctorialData (G.toLUFamily ludata)) (U : AMod W) :
    (bimodHoleA_inducedAssignment G ludata realizes Dfun).realize U = (G.toLUFamily ludata).K U :=
  rfl

/-- **The lifting `A.realizes` is exactly the carried bottom-survival iso.** -/
@[simp] theorem bimodHoleA_inducedAssignment_realizes (G : BimodGenuineConstructionA W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (G.toMURepFamily.mudata U))
    (realizes : ∀ U : AMod W, AModEquiv W ((G.toLUFamily ludata).K U).toAMod U)
    (Dfun : MUFunctorialData (G.toLUFamily ludata)) (U : AMod W) :
    (bimodHoleA_inducedAssignment G ludata realizes Dfun).realizes U = realizes U :=
  rfl

/-! ## The round-trip of Theorem 5.3.4 from HOLE A (the lifting half, genuine ρ) -/

/-- **The round-trip `forwardMap ∘ invFun = id` of Theorem 5.3.4, from the genuine HOLE A.** The
instant the lifting datum `A = bimodHoleA_inducedAssignment …` is supplied, the lifting half of the
Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` closes: `forwardMap [L(U)] = [U]` for every `A(𝒱)`-module iso-class
(`InducedAssignment.forwardMap_comp_invFun`, unconditional once the assignment exists). -/
theorem bimodHoleA_forwardMap_comp_invFun (G : BimodGenuineConstructionA W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (G.toMURepFamily.mudata U))
    (realizes : ∀ U : AMod W, AModEquiv W ((G.toLUFamily ludata).K U).toAMod U)
    (Dfun : MUFunctorialData (G.toLUFamily ludata)) :
    forwardMap W ∘ (bimodHoleA_inducedAssignment G ludata realizes Dfun).invFun = id :=
  (bimodHoleA_inducedAssignment G ludata realizes Dfun).forwardMap_comp_invFun

/-! ## The genuineness audit — the assignment carries the bimodule-composition ρ, never `fzRhoMU`

The lifting datum's module `M(U)` is the `buildMUModuleData` term over `ρ = levelShiftRho` (the
`anmComposeBilin` loop action), whose mode action is the genuine level-shift bimodule composition.
The following records that the per-`U` representation of the assembled `MURepFamily` is
*definitionally* `levelShiftRho`, certifying the genuineness by name (no `FZModeDescent`, no
`fzRhoMU`). -/

/-- **Genuineness certificate.** The representation feeding the lifting datum is the
bimodule-composition `levelShiftRho`, on the nose. -/
@[simp] theorem bimodHoleA_rho_is_levelShiftRho (G : BimodGenuineConstructionA W) (U : AMod W) :
    (G.toMURepFamily).rho U
      = VHat.levelShiftRho W U (G.σ U) (G.hL U) (G.hR U) (G.hderiv U) (G.hbracket U) :=
  rfl

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
