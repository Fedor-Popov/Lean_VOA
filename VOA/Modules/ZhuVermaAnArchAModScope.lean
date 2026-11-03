/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLeaf3
import VOA.Modules.ZhuVermaAnArchMUFullGrading

/-!
# The `AMod` scope repair — additive scoped predicates for the `∀ U : AMod W` statements

`AMod W` (`Modules.ZhuBijection`) is the bundled `A(𝒱)`-module type used as the *codomain* of the
Zhu correspondence.  Its fields are exactly `⟨carrier, ρ, ρ_one, ρ_mul⟩`: it carries **no**
nontriviality and **no** irreducibility.  That is deliberate (the descended action `actA` produces
precisely this data and nothing more), but it makes a family of statements in the
`M(U)`-construction files **false at the literal `∀ U : AMod W` scope**.  This file repairs the
scope *additively*:
nothing existing is edited, no existing theorem statement is changed, and the repair consists of new
scoped predicates, their transport API, the corrected scoped statements, and — crucially — explicit
**refutation certificates** for the unscoped versions.

## Why the unscoped statements fail (two genuinely different counterexamples)

**(A) The zero `A(𝒱)`-module.**  `zeroAMod W : AMod W` (carrier `PUnit`, `ρ = 0`; the unit law
`ρ [𝟙] = 1` holds because `End ℂ PUnit` is a subsingleton) is a perfectly legal `AMod W`.  It
refutes every statement of the shape "something built from `U` is nonzero":

* `not_nontrivial_zeroAMod` / `not_forall_nontrivial` — `∀ U : AMod W, Nontrivial U.carrier` is
  FALSE;
* `not_isSimpleAMod_zeroAMod` / `not_forall_isSimpleAMod` — `∀ U : AMod W, IsSimpleAMod U` is FALSE;
* `MUFull.deg_zero_eq_bot_zeroAMod` / `not_forall_muFull_bottom_ne_bot` — the `bottom_ne_bot` field
  `hbot : MUFull.deg W U 0 ≠ ⊥` of `MUFullModuleData` (`Modules.ZhuVermaAnArchMUFullLW`) is FALSE at
  `∀ U : AMod W` scope: at `U = zeroAMod W` the whole bottom `A_{0,0}(𝒱) ⊗_ℂ U` is the zero space.

**(B) A reducible `A(𝒱)`-module.**  `AMod.prod P Q` (diagonal action on `P.carrier × Q.carrier`) is
`AMod W` again, and for nontrivial `P`, `Q` the first summand `AMod.fstSub P Q` is a proper nonzero
`A(𝒱)`-submodule.  This refutes the *dichotomy*-flavoured statements — the abstract skeleton of the
`bottom_A0_irred` leaf (`InducedAssignment.BottomA0Irreducible`,
`Modules.ZhuVermaAnArchSdBottomIrred`) of `InducedAssignment.BottomRegenData`
(`Modules.ZhuVermaAnArchStructuralClose`), which asserts for **every** `U` that a graded submodule
of
`M(U)` meeting the bottom already contains the bottom, i.e. that the bottom `A(𝒱)`-module is
irreducible:

* `not_amodDichotomy_prod` / `not_forall_amodDichotomy`.

The two counterexamples are genuinely independent: `amodDichotomy_zeroAMod` shows the **zero**
module does *not* refute the dichotomy (it holds vacuously there), and
`not_scopedNontrivial_amodDichotomy`
shows that merely demanding `Nontrivial U.carrier` does *not* repair it either.  The dichotomy needs
the *simple/irreducible* scope; nontriviality is the weaker scope that repairs `hbot`.

**(C) The `hL0` scope.**  The `L0_on_deg` field of `MUFullModuleData W U h` pins **one** scalar `h`
as the `L₀`-eigenvalue on the whole bottom.  The bottom is `A_{0,0}(𝒱) ⊗ U`, on which `[ω]` acts
through `U.ρ [ω]` — motivation (NOT proved here) for demanding that `[ω]` act on `U` by a single
scalar `h`.  We name that requirement `AMod.OmegaScalar U h`; what is proved here is that it is
**necessary** for `U` to be a bottom at all (`omegaScalar_of_bottomEquiv`), that it **holds** on the
intended scope
(`lowestAMod_omegaScalar`, `LWModule.toAMod_omegaScalar`, `IrrAMod.omegaScalar`), prove it is
transported by `AModEquiv`, and refute it off the scope (`not_omegaScalar_prod`,
`not_forall_exists_omegaScalar`: a direct sum of two bottoms with distinct lowest weights admits
**no** `h`).

## What is built here

* **Scoped predicates.**  `AMod.OmegaScalar U h`; `AModDichotomy U` (the ideal-free skeleton of
  `bottom_A0_irred`); the existing `IsSimpleAMod` (`Modules.ZhuVermaAnArchLeaf3`) is *reused*, not
  duplicated, and so are `nontrivial_toAMod` and `IrrAMod`
  (`Modules.ZhuVermaAnArchFaithfulBijection`).
* **Transport along `AModEquiv`.**  `AModEquiv.comapSubmodule`, `AModEquiv.nontrivial_target`,
  `AModEquiv.isSimpleAMod_target`, `AModEquiv.amodDichotomy_target`,
  `AModEquiv.omegaScalar_target` — every scope predicate is an iso-invariant.
* **Simple ⟹ nontrivial ⟹ (nothing).**  `IsSimpleAMod.nontrivial`, `IsSimpleAMod.amodDichotomy`,
  and the exact split `isSimpleAMod_iff : IsSimpleAMod U ↔ Nontrivial U.carrier ∧ AModDichotomy U`.
* **`IrrAMod` coerces into the scope.**  `IrrAMod.nontrivial` and `IrrAMod.omegaScalar` are
  **unconditional**; `IrrAMod.isSimpleAMod`/`IrrAMod.amodDichotomy` are supplied on the explicitly
  named gate `AllBottomRecovers W` (`= ∀ P, BottomRecovers P`, the keystone-caliber residual
  isolated in `Modules.ZhuVermaAnArchLeaf3`; never an axiom, and **proved for every VOA** by
  `VOA.Huang.LWBottomRecovery.allBottomRecovers`), and on the strictly weaker
  `AllIrrBottomRecovers W` (`= ∀ P, P.IsIrreducibleLW → BottomRecovers P`) via
  `IrrAMod.isSimpleAMod_irr` / `IrrAMod.amodDichotomy_irr` — the sharpened gate is the honest one,
  since only irreducible realizers ever arise from `IsBottomOfIrr`.
* **Scoped quantifiers** `ScopedNontrivial` / `ScopedSimple` / `ScopedIrr` with their implications,
  plus `AModIsoInvariant` and `scopedIrr_of_bottoms` — the drop-in replacements for a bare
  `∀ U : AMod W, Φ U` in the `BottomRegenData`/`BottomA0Irreducible`-shaped statements.
* **The corrected `hbot` on the β-track.**  `MUFull.deg_ne_bot_of_nontrivial` and
  `MUFull.bottom_ne_bot_of_bottomMap`: once the balanced-bottom map
  `MUPieceFull W U 0 →ₗ[ℂ] U.carrier` is surjective (the pending balanced-bottom surgery over
  `AnmFull`), `hbot` follows **on the nontrivial scope** and only there — hence also on `IrrAMod`
  ungated (`scopedNontrivial_muFull_bottom_ne_bot`, `scopedIrr_muFull_bottom_ne_bot`).
* **The corrected `hL0` necessary condition.**  `omegaScalar_of_bottomEquiv` and
  `isEmpty_bottomEquiv_of_not_omegaScalar`.

## Status / residuals (stated exactly)

Everything below is proved outright except where a hypothesis is displayed in the statement.  The
only carried hypotheses are `AllBottomRecovers W` / `AllIrrBottomRecovers W` (for the *simple*-scope
conclusions about `IrrAMod`) and, in `MUFull.bottom_ne_bot_of_bottomMap`, the surjective bottom map
— neither is discharged here and neither is an axiom.  ⚠ **Update:** `AllBottomRecovers W` (hence
`AllIrrBottomRecovers W`, via `AllBottomRecovers.allIrr`) is proved for every VOA,
downstream, by `VOA.Huang.LWBottomRecovery.allBottomRecovers` (`Huang/LWBottomRecovery.lean`,
`#print axioms`: Lean's three), so the simple-scope conclusions hold unconditionally once that
is supplied.  Nothing here proves `bottom_A0_irred`,
`BottomRegenData`, `MUGradedAction`, or any `M(U)` keystone; it fixes **scopes** only.

`#print axioms` on every declaration below is exactly `[propext, Classical.choice, Quot.sound]`;
no `sorry`, no new axiom, no `pbw`.

## References
Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu; Dong–Jiang `math/0601626` §2, §4.
`Modules.ZhuBijection` (`AMod`, `AModEquiv`, `lowestAMod`, `LWModule.toAMod`),
`Modules.ZhuVermaAnArchLeaf3` (`AModSubmodule`, `IsSimpleAMod`, `nontrivial_toAMod`,
`BottomRecovers`, `isSimpleAMod_of_bottomRecovers`),
`Modules.ZhuVermaAnArchFaithfulBijection` (`IsBottomOfIrr`, `IrrAMod`),
`Modules.ZhuVermaAnArchSdBottomIrred` (`BottomA0Irreducible` — the statement being rescoped),
`Modules.ZhuVermaAnArchMUFullLW` (`MUFullModuleData.bottom_ne_bot`, `.L0_on_deg`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section AModScope

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## §1  The scoped predicates

`IsSimpleAMod` already exists (`Modules.ZhuVermaAnArchLeaf3`) and is reused verbatim.  Two further
predicates are needed: the *dichotomy* skeleton that the `bottom_A0_irred` leaf really asserts, and
the `[ω]`-scalarity that the `L0_on_deg` field really forces. -/

/-- **`AModDichotomy U`** — the ideal-free skeleton of the `bottom_A0_irred` leaf: every
`A(𝒱)`-submodule of `U` that is not `⊥` is already `⊤`.  Together with `Nontrivial U.carrier` this
is `IsSimpleAMod U`; separated out because it is the exact shape in which
`InducedAssignment.BottomA0Irreducible` (`Modules.ZhuVermaAnArchSdBottomIrred`) states its
conclusion — a graded submodule meeting the bottom nontrivially contains the whole bottom. -/
def AModDichotomy (U : AMod W) : Prop :=
  ∀ S : AModSubmodule U, S.carrier ≠ ⊥ → S.carrier = ⊤

/-- **`U.OmegaScalar h`** — the Zhu class `[ω]` of the conformal vector acts on `U` by the single
scalar `h`.  This is exactly what the `L0_on_deg` field of `MUFullModuleData W U h` forces on the
bottom `A_{0,0}(𝒱) ⊗ U` of `M(U)`: one complex number `h` is pinned as the `L₀`-eigenvalue of the
*entire* bottom layer, and `[ω]` acts on that layer through `U.ρ [ω]`. -/
def AMod.OmegaScalar (U : AMod W) (h : ℂ) : Prop :=
  U.ρ (_root_.VOA.mk W W.conformalVector) = h • (1 : Module.End ℂ U.carrier)

/-- Pointwise form of `AMod.OmegaScalar`: `[ω] · x = h • x` for every `x`. -/
theorem AMod.omegaScalar_apply {U : AMod W} {h : ℂ} (hU : U.OmegaScalar h) (x : U.carrier) :
    U.ρ (_root_.VOA.mk W W.conformalVector) x = h • x := by
  rw [hU]; simp

/-! ## §2  Transport along `AModEquiv`: every scope predicate is an iso-invariant -/

/-- **Pulling an `A(𝒱)`-submodule back along an `AModEquiv`.**  For `e : P ≃ Q` and an
`A(𝒱)`-submodule `S` of `Q`, its preimage is an `A(𝒱)`-submodule of `P` (closure is the
intertwining `e (P.ρ a x) = Q.ρ a (e x)`). -/
def AModEquiv.comapSubmodule {P Q : AMod W} (e : AModEquiv W P Q) (S : AModSubmodule Q) :
    AModSubmodule P where
  carrier := S.carrier.comap e.toLinearEquiv.toLinearMap
  ρ_mem a {x} hx := by
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [e.map_ρ a x]
    exact S.ρ_mem a hx

/-- The carrier of `AModEquiv.comapSubmodule` is the preimage submodule, definitionally. -/
theorem AModEquiv.comapSubmodule_carrier {P Q : AMod W} (e : AModEquiv W P Q)
    (S : AModSubmodule Q) :
    (e.comapSubmodule S).carrier = S.carrier.comap e.toLinearEquiv.toLinearMap := rfl

/-- **Nontriviality transports along an `AModEquiv`.** -/
theorem AModEquiv.nontrivial_target {P Q : AMod W} (e : AModEquiv W P Q)
    (hP : Nontrivial P.carrier) : Nontrivial Q.carrier := by
  obtain ⟨x, y, hxy⟩ := hP
  exact ⟨e.toLinearEquiv x, e.toLinearEquiv y, fun hh => hxy (e.toLinearEquiv.injective hh)⟩

/-- **Simplicity transports along an `AModEquiv`.**  A submodule of the target pulls back to a
submodule of the source; the source dichotomy is pushed forward using that `e` is a bijection. -/
theorem AModEquiv.isSimpleAMod_target {P Q : AMod W} (e : AModEquiv W P Q)
    (hP : IsSimpleAMod P) : IsSimpleAMod Q := by
  refine ⟨e.nontrivial_target hP.1, fun S => ?_⟩
  rcases hP.2 (e.comapSubmodule S) with hb | ht
  · left
    refine le_antisymm (fun y hy => ?_) bot_le
    have hmem : e.toLinearEquiv.symm y ∈ (e.comapSubmodule S).carrier := by
      change e.toLinearEquiv.toLinearMap (e.toLinearEquiv.symm y) ∈ S.carrier
      simpa using hy
    rw [hb, Submodule.mem_bot] at hmem
    have hy0 : y = 0 := by
      have hc := congrArg e.toLinearEquiv hmem
      simpa using hc
    simp [hy0]
  · right
    refine le_antisymm le_top (fun y _ => ?_)
    have hmem : e.toLinearEquiv.symm y ∈ (e.comapSubmodule S).carrier := by rw [ht]; trivial
    have hS : e.toLinearEquiv.toLinearMap (e.toLinearEquiv.symm y) ∈ S.carrier := hmem
    simpa using hS

/-- **The dichotomy transports along an `AModEquiv`.** -/
theorem AModEquiv.amodDichotomy_target {P Q : AMod W} (e : AModEquiv W P Q)
    (hP : AModDichotomy P) : AModDichotomy Q := by
  intro S hS
  refine le_antisymm le_top (fun y _ => ?_)
  have hne : (e.comapSubmodule S).carrier ≠ ⊥ := by
    intro hb
    refine hS (le_antisymm (fun y hy => ?_) bot_le)
    have hmem : e.toLinearEquiv.symm y ∈ (e.comapSubmodule S).carrier := by
      change e.toLinearEquiv.toLinearMap (e.toLinearEquiv.symm y) ∈ S.carrier
      simpa using hy
    rw [hb, Submodule.mem_bot] at hmem
    have hy0 : y = 0 := by
      have hc := congrArg e.toLinearEquiv hmem
      simpa using hc
    simp [hy0]
  have ht := hP _ hne
  have hmem : e.toLinearEquiv.symm y ∈ (e.comapSubmodule S).carrier := by rw [ht]; trivial
  have hS' : e.toLinearEquiv.toLinearMap (e.toLinearEquiv.symm y) ∈ S.carrier := hmem
  simpa using hS'

/-- **`[ω]`-scalarity transports along an `AModEquiv`.** -/
theorem AModEquiv.omegaScalar_target {P Q : AMod W} (e : AModEquiv W P Q) {h : ℂ}
    (hP : P.OmegaScalar h) : Q.OmegaScalar h := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
  rw [← e.map_ρ, AMod.omegaScalar_apply hP x, map_smul]
  simp

/-! ## §3  Simplicity implies the weaker scopes -/

/-- **A simple `A(𝒱)`-module is nontrivial** (the first conjunct of `IsSimpleAMod`). -/
theorem IsSimpleAMod.nontrivial {U : AMod W} (h : IsSimpleAMod U) : Nontrivial U.carrier := h.1

/-- **A simple `A(𝒱)`-module satisfies the dichotomy.** -/
theorem IsSimpleAMod.amodDichotomy {U : AMod W} (h : IsSimpleAMod U) : AModDichotomy U := by
  intro S hS
  rcases h.2 S with hb | ht
  · exact absurd hb hS
  · exact ht

/-- **Simplicity is exactly nontriviality plus the dichotomy.**  Records that the two scope
predicates of this file cut `IsSimpleAMod` apart precisely: `AModDichotomy` is the whole of
simplicity except for nontriviality, which is why the zero module and a reducible module are two
*independent* counterexamples (§7). -/
theorem isSimpleAMod_iff {U : AMod W} :
    IsSimpleAMod U ↔ Nontrivial U.carrier ∧ AModDichotomy U := by
  refine ⟨fun h => ⟨h.nontrivial, h.amodDichotomy⟩, fun ⟨hnt, hd⟩ => ⟨hnt, fun S => ?_⟩⟩
  by_cases hS : S.carrier = ⊥
  · exact Or.inl hS
  · exact Or.inr (hd S hS)

/-! ## §4  `[ω]` acts by the lowest weight on the bottom of a lowest-weight module -/

section Lowest

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **`[ω]` acts by the scalar `h` on `M_h`.**  On the lowest-weight space the descended action of
the Zhu class `[ω]` is `o(ω) = ω₍₁₎ = L₀`, which is `h • id` there by `L0_weight`.  Hence the
bundled bottom `lowestAMod hcw` satisfies `OmegaScalar h` unconditionally. -/
theorem lowestAMod_omegaScalar {P : OrdVModule W M} {h : ℂ} (hcw : IsLowestWeight P h) :
    (lowestAMod hcw).OmegaScalar h := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  let x' : P.weight h := x
  change ((actA P hcw (_root_.VOA.mk W W.conformalVector) x' : P.weight h) : M)
    = ((h • (1 : Module.End ℂ (P.weight h))) x' : P.weight h)
  rw [actA_mk_apply_coe P hcw, oMod_homogeneous P W.conformalVector_mem_grading_two]
  have h1 : ((2 : ℤ) - 1) = 1 := by norm_num
  rw [h1, P.L0_weight h (x' : M) x'.2]
  simp

end Lowest

/-- **The bottom of a bundled lowest-weight module is `[ω]`-scalar at its own lowest weight.** -/
theorem LWModule.toAMod_omegaScalar (P : LWModule W) : P.toAMod.OmegaScalar P.h :=
  lowestAMod_omegaScalar P.isLow

/-- **The corrected `hL0` necessary condition.**  If `U` is realized as the bottom of a
lowest-weight `𝒱`-module `P` — which is exactly what `M(U)_h ≅ U` asserts in the induced
construction — then `[ω]` *must* act on `U` by the single scalar `P.h`.  So an `hL0`-style field is
satisfiable only on the
`OmegaScalar` scope. -/
theorem omegaScalar_of_bottomEquiv {P : LWModule W} {U : AMod W} (e : AModEquiv W P.toAMod U) :
    U.OmegaScalar P.h :=
  e.omegaScalar_target (LWModule.toAMod_omegaScalar P)

/-- **Contrapositive certificate.**  An `A(𝒱)`-module on which `[ω]` does *not* act by the scalar
`h` is not the bottom of any lowest-weight module of lowest weight `h`. -/
theorem isEmpty_bottomEquiv_of_not_omegaScalar {U : AMod W} {h : ℂ} (hU : ¬ U.OmegaScalar h)
    (P : LWModule W) (hh : P.h = h) : IsEmpty (AModEquiv W P.toAMod U) :=
  ⟨fun e => hU (hh ▸ omegaScalar_of_bottomEquiv e)⟩

/-! ## §5  `IrrAMod` coerces into the scope

`IrrAMod W = {U // IsBottomOfIrr U}` (`Modules.ZhuVermaAnArchFaithfulBijection`) is the faithful
codomain of Theorem 5.3.4.  Nontriviality and `[ω]`-scalarity of its members are **unconditional**;
simplicity is supplied on the named gate `AllBottomRecovers`. -/

/-- **Every bottom-of-irreducible is nontrivial** — unconditional, via `nontrivial_toAMod` (the
bottom of a *realized* lowest-weight module is nonzero) transported along the defining iso. -/
theorem IsBottomOfIrr.nontrivial {U : AMod W} (hU : IsBottomOfIrr U) : Nontrivial U.carrier := by
  obtain ⟨P, _, ⟨e⟩⟩ := hU
  exact e.nontrivial_target (nontrivial_toAMod P)

/-- **Every bottom-of-irreducible is `[ω]`-scalar** — unconditional, at the lowest weight of the
realizing module. -/
theorem IsBottomOfIrr.omegaScalar {U : AMod W} (hU : IsBottomOfIrr U) :
    ∃ h : ℂ, U.OmegaScalar h := by
  obtain ⟨P, _, ⟨e⟩⟩ := hU
  exact ⟨P.h, omegaScalar_of_bottomEquiv e⟩

/-- **Members of `IrrAMod W` are nontrivial** — the coercion of the faithful codomain into the
nontriviality scope. -/
theorem IrrAMod.nontrivial (U : IrrAMod W) : Nontrivial U.1.carrier := U.2.nontrivial

/-- **Members of `IrrAMod W` are `[ω]`-scalar** — the coercion of the faithful codomain into the
`OmegaScalar` scope. -/
theorem IrrAMod.omegaScalar (U : IrrAMod W) : ∃ h : ℂ, U.1.OmegaScalar h := U.2.omegaScalar

/-- **`AllBottomRecovers W`** — the uniform form of the gated bottom-recovery predicate
`BottomRecovers` of `Modules.ZhuVermaAnArchLeaf3`: for *every* bundled lowest-weight module, a
`𝒱`-mode word returning a bottom vector to the bottom is already achieved by the Zhu-algebra action.
This is the keystone-caliber input isolated there; it is carried as an explicit hypothesis and is
**never** an axiom.  It is proved for every VOA, downstream:
`VOA.Huang.LWBottomRecovery.allBottomRecovers W`. -/
def AllBottomRecovers (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ P : LWModule W, BottomRecovers P

/-- **Every bottom-of-irreducible is a simple `A(𝒱)`-module, modulo `AllBottomRecovers`.** -/
theorem IsBottomOfIrr.isSimpleAMod (hrec : AllBottomRecovers W) {U : AMod W}
    (hU : IsBottomOfIrr U) : IsSimpleAMod U := by
  obtain ⟨P, hirr, ⟨e⟩⟩ := hU
  exact e.isSimpleAMod_target (isSimpleAMod_of_bottomRecovers P hirr (hrec P))

/-- **Members of `IrrAMod W` are simple, modulo `AllBottomRecovers`.** -/
theorem IrrAMod.isSimpleAMod (hrec : AllBottomRecovers W) (U : IrrAMod W) : IsSimpleAMod U.1 :=
  U.2.isSimpleAMod hrec

/-- **Members of `IrrAMod W` satisfy the dichotomy, modulo `AllBottomRecovers`** — this is the
corrected, scoped form of the `bottom_A0_irred` conclusion. -/
theorem IrrAMod.amodDichotomy (hrec : AllBottomRecovers W) (U : IrrAMod W) :
    AModDichotomy U.1 :=
  (U.isSimpleAMod hrec).amodDichotomy

/-! ### §5a  The gate, sharpened to the irreducible realizers only

`AllBottomRecovers W` quantifies over *all* bundled lowest-weight modules, but the proof above only
ever applies it to the **irreducible** `P` realizing `U`.  The strictly weaker gate below is
therefore the honest one, and every §5 conclusion is re-proved from it. -/

/-- **`AllIrrBottomRecovers W`** — the sharpened gate: bottom recovery is demanded only of the
*irreducible* lowest-weight modules — the only ones `IsBottomOfIrr` ever produces.  Strictly
weaker than `AllBottomRecovers W` (`AllBottomRecovers.allIrr`), and it suffices everywhere in §5. -/
def AllIrrBottomRecovers (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ P : LWModule W, P.IsIrreducibleLW → BottomRecovers P

/-- The uniform gate implies the sharpened one (the converse is not claimed). -/
theorem AllBottomRecovers.allIrr (hrec : AllBottomRecovers W) : AllIrrBottomRecovers W :=
  fun P _ => hrec P

/-- **Every bottom-of-irreducible is simple, modulo the sharpened gate.**  This supersedes
`IsBottomOfIrr.isSimpleAMod`: the hypothesis is weaker and the conclusion identical. -/
theorem IsBottomOfIrr.isSimpleAMod_irr (hrec : AllIrrBottomRecovers W) {U : AMod W}
    (hU : IsBottomOfIrr U) : IsSimpleAMod U := by
  obtain ⟨P, hirr, ⟨e⟩⟩ := hU
  exact e.isSimpleAMod_target (isSimpleAMod_of_bottomRecovers P hirr (hrec P hirr))

/-- **Members of `IrrAMod W` are simple, modulo the sharpened gate.** -/
theorem IrrAMod.isSimpleAMod_irr (hrec : AllIrrBottomRecovers W) (U : IrrAMod W) :
    IsSimpleAMod U.1 :=
  U.2.isSimpleAMod_irr hrec

/-- **Members of `IrrAMod W` satisfy the dichotomy, modulo the sharpened gate** — the corrected,
scoped form of the `bottom_A0_irred` conclusion, on the weakest gate this file needs. -/
theorem IrrAMod.amodDichotomy_irr (hrec : AllIrrBottomRecovers W) (U : IrrAMod W) :
    AModDichotomy U.1 :=
  (U.isSimpleAMod_irr hrec).amodDichotomy

/-! ## §6  The scoped quantifiers — drop-in replacements for a bare `∀ U : AMod W` -/

/-- **`ScopedNontrivial W Φ`** — `Φ` holds for every *nontrivial* bundled `A(𝒱)`-module.  The
correct scope for `hbot`-flavoured statements ("something built from `U` is nonzero"). -/
def ScopedNontrivial (W : VertexOperatorAlgebra 𝒱) (Φ : AMod W → Prop) : Prop :=
  ∀ U : AMod W, Nontrivial U.carrier → Φ U

/-- **`ScopedSimple W Φ`** — `Φ` holds for every *simple* bundled `A(𝒱)`-module.  The correct scope
for `bottom_A0_irred`/`BottomRegenData`-flavoured statements. -/
def ScopedSimple (W : VertexOperatorAlgebra 𝒱) (Φ : AMod W → Prop) : Prop :=
  ∀ U : AMod W, IsSimpleAMod U → Φ U

/-- **`ScopedIrr W Φ`** — `Φ` holds on the faithful codomain `IrrAMod W` of Theorem 5.3.4.  This is
the scope in which the Zhu correspondence is actually stated. -/
def ScopedIrr (W : VertexOperatorAlgebra 𝒱) (Φ : AMod W → Prop) : Prop :=
  ∀ U : IrrAMod W, Φ U.1

/-- **`AModIsoInvariant Φ`** — `Φ` is invariant under `A(𝒱)`-module isomorphism.  All four scope
predicates of this file are iso-invariant (§2). -/
def AModIsoInvariant (W : VertexOperatorAlgebra 𝒱) (Φ : AMod W → Prop) : Prop :=
  ∀ P Q : AMod W, AModEquiv W P Q → Φ P → Φ Q

/-- An unscoped statement is in particular scoped to the nontrivial modules. -/
theorem ScopedNontrivial.of_forall {Φ : AMod W → Prop} (h : ∀ U : AMod W, Φ U) :
    ScopedNontrivial W Φ := fun U _ => h U

/-- An unscoped statement is in particular scoped to the simple modules. -/
theorem ScopedSimple.of_forall {Φ : AMod W → Prop} (h : ∀ U : AMod W, Φ U) :
    ScopedSimple W Φ := fun U _ => h U

/-- An unscoped statement is in particular scoped to `IrrAMod`. -/
theorem ScopedIrr.of_forall {Φ : AMod W → Prop} (h : ∀ U : AMod W, Φ U) :
    ScopedIrr W Φ := fun U => h U.1

/-- **The nontrivial scope is coarser than the simple scope**: simple modules are nontrivial. -/
theorem ScopedNontrivial.scopedSimple {Φ : AMod W → Prop} (h : ScopedNontrivial W Φ) :
    ScopedSimple W Φ := fun U hU => h U hU.nontrivial

/-- **The nontrivial scope covers `IrrAMod`** — unconditionally. -/
theorem ScopedNontrivial.scopedIrr {Φ : AMod W → Prop} (h : ScopedNontrivial W Φ) :
    ScopedIrr W Φ := fun U => h U.1 U.nontrivial

/-- **The simple scope covers `IrrAMod`**, modulo the named gate `AllBottomRecovers`. -/
theorem ScopedSimple.scopedIrr (hrec : AllBottomRecovers W) {Φ : AMod W → Prop}
    (h : ScopedSimple W Φ) : ScopedIrr W Φ := fun U => h U.1 (U.isSimpleAMod hrec)

/-- **The simple scope covers `IrrAMod`**, modulo the *sharpened* gate `AllIrrBottomRecovers`. -/
theorem ScopedSimple.scopedIrr_irr (hrec : AllIrrBottomRecovers W) {Φ : AMod W → Prop}
    (h : ScopedSimple W Φ) : ScopedIrr W Φ := fun U => h U.1 (U.isSimpleAMod_irr hrec)

/-- **Checking an iso-invariant statement on `IrrAMod` reduces to the bottoms of irreducibles.** -/
theorem scopedIrr_of_bottoms {Φ : AMod W → Prop} (hinv : AModIsoInvariant W Φ)
    (hb : ∀ P : LWModule W, P.IsIrreducibleLW → Φ P.toAMod) : ScopedIrr W Φ := by
  intro U
  obtain ⟨P, hirr, ⟨e⟩⟩ := U.2
  exact hinv _ _ e (hb P hirr)

/-- **The dichotomy is an iso-invariant.** -/
theorem amodIsoInvariant_amodDichotomy (W : VertexOperatorAlgebra 𝒱) :
    AModIsoInvariant W AModDichotomy := fun _ _ e h => e.amodDichotomy_target h

/-- **Nontriviality is an iso-invariant.** -/
theorem amodIsoInvariant_nontrivial (W : VertexOperatorAlgebra 𝒱) :
    AModIsoInvariant W (fun U => Nontrivial U.carrier) := fun _ _ e h => e.nontrivial_target h

/-- **Simplicity is an iso-invariant.** -/
theorem amodIsoInvariant_isSimpleAMod (W : VertexOperatorAlgebra 𝒱) :
    AModIsoInvariant W IsSimpleAMod := fun _ _ e h => e.isSimpleAMod_target h

/-- **`[ω]`-scalarity (at an unspecified weight) is an iso-invariant.** -/
theorem amodIsoInvariant_omegaScalar (W : VertexOperatorAlgebra 𝒱) :
    AModIsoInvariant W (fun U => ∃ h : ℂ, U.OmegaScalar h) :=
  fun _ _ e h => h.imp fun _ hh => e.omegaScalar_target hh

/-- **The corrected `bottom_A0_irred` skeleton, proved on the simple scope.**  The statement that is
false at `∀ U : AMod W` scope (see §7) is true — trivially so — once the scope is the simple
`A(𝒱)`-modules.  This is the shape `InducedAssignment.BottomA0Irreducible` should be quantified
over. -/
theorem scopedSimple_amodDichotomy (W : VertexOperatorAlgebra 𝒱) :
    ScopedSimple W AModDichotomy := fun _ hU => hU.amodDichotomy

/-- **The corrected `hL0` scope, proved on `IrrAMod`.** -/
theorem scopedIrr_omegaScalar (W : VertexOperatorAlgebra 𝒱) :
    ScopedIrr W (fun U => ∃ h : ℂ, U.OmegaScalar h) := fun U => U.omegaScalar

/-! ## §7  Refutation certificates for the unscoped statements

Two independent counterexamples: the zero `A(𝒱)`-module and a reducible one. -/

/-- **The zero `A(𝒱)`-module.**  Carrier `PUnit`, action `0`.  The unit law `ρ [𝟙] = 1` and
multiplicativity hold because `End ℂ PUnit` is a subsingleton.  This is a perfectly legal `AMod W` —
`AMod` carries no nontriviality — and it is the counterexample to every `∀ U : AMod W` statement
asserting that something built from `U` is nonzero. -/
def zeroAMod (W : VertexOperatorAlgebra 𝒱) : AMod W where
  carrier := PUnit.{u+1}
  ρ := 0
  ρ_one := LinearMap.ext fun _ => Subsingleton.elim _ _
  ρ_mul _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _

/-- The carrier of `zeroAMod` is a subsingleton. -/
instance zeroAMod.instSubsingleton (W : VertexOperatorAlgebra 𝒱) :
    Subsingleton (zeroAMod W).carrier := inferInstanceAs (Subsingleton PUnit.{u+1})

/-- **The zero `A(𝒱)`-module is not nontrivial.** -/
theorem not_nontrivial_zeroAMod (W : VertexOperatorAlgebra 𝒱) :
    ¬ Nontrivial (zeroAMod W).carrier := fun h =>
  (not_subsingleton_iff_nontrivial.mpr h) inferInstance

/-- **`∀ U : AMod W, Nontrivial U.carrier` is FALSE.**  The scope bug in one line. -/
theorem not_forall_nontrivial (W : VertexOperatorAlgebra 𝒱) :
    ¬ ∀ U : AMod W, Nontrivial U.carrier := fun h => not_nontrivial_zeroAMod W (h (zeroAMod W))

/-- **The zero `A(𝒱)`-module is not simple.** -/
theorem not_isSimpleAMod_zeroAMod (W : VertexOperatorAlgebra 𝒱) :
    ¬ IsSimpleAMod (zeroAMod W) := fun h => not_nontrivial_zeroAMod W h.1

/-- **`∀ U : AMod W, IsSimpleAMod U` is FALSE.** -/
theorem not_forall_isSimpleAMod (W : VertexOperatorAlgebra 𝒱) :
    ¬ ∀ U : AMod W, IsSimpleAMod U := fun h => not_isSimpleAMod_zeroAMod W (h (zeroAMod W))

/-- **The zero module does *not* refute the dichotomy** — it satisfies it vacuously, every submodule
being `⊥`.  Recorded to show that the two scope failures of this file are genuinely different: the
dichotomy needs the *reducible* counterexample below, not the zero one. -/
theorem amodDichotomy_zeroAMod (W : VertexOperatorAlgebra 𝒱) :
    AModDichotomy (zeroAMod W) := by
  intro S hS
  exact absurd (le_antisymm (fun x _ => Submodule.mem_bot ℂ |>.mpr (Subsingleton.elim x 0))
    bot_le) hS

/-- **The direct sum of two bundled `A(𝒱)`-modules**, with the diagonal action.  Again a perfectly
legal `AMod W`: this is the *reducible* counterexample. -/
def AMod.prod (P Q : AMod W) : AMod W where
  carrier := P.carrier × Q.carrier
  ρ :=
    { toFun := fun a => LinearMap.prodMap (P.ρ a) (Q.ρ a)
      map_add' := fun a b => by refine LinearMap.ext fun x => ?_; simp
      map_smul' := fun c a => by refine LinearMap.ext fun x => ?_; simp }
  ρ_one := by refine LinearMap.ext fun x => ?_; simp [P.ρ_one, Q.ρ_one]
  ρ_mul u v := by refine LinearMap.ext fun x => ?_; simp [P.ρ_mul, Q.ρ_mul]

/-- The action on `AMod.prod` is componentwise. -/
@[simp] theorem AMod.prod_ρ_apply (P Q : AMod W) (a : A W) (x : P.carrier × Q.carrier) :
    (P.prod Q).ρ a x = (P.ρ a x.1, Q.ρ a x.2) := rfl

/-- `AMod.prod P Q` is nontrivial as soon as `P` is. -/
theorem AMod.prod_nontrivial (P Q : AMod W) (hP : Nontrivial P.carrier) :
    Nontrivial (P.prod Q).carrier := by
  obtain ⟨p, p', hpp⟩ := hP
  exact ⟨((p, 0) : P.carrier × Q.carrier), ((p', 0) : P.carrier × Q.carrier),
    fun hh => hpp (congrArg Prod.fst hh)⟩

/-- **The first summand of `AMod.prod P Q` as an `A(𝒱)`-submodule** (the action is diagonal, so the
subspace `{(x, 0)}` is stable). -/
def AMod.fstSub (P Q : AMod W) : AModSubmodule (P.prod Q) where
  carrier :=
    { carrier := {x : P.carrier × Q.carrier | x.2 = 0}
      add_mem' := fun {a b} ha hb => by
        change a.2 + b.2 = 0
        rw [show a.2 = 0 from ha, show b.2 = 0 from hb, add_zero]
      zero_mem' := rfl
      smul_mem' := fun c x hx => by
        change c • x.2 = 0
        rw [show x.2 = 0 from hx, smul_zero] }
  ρ_mem a {x} hx := by
    change Q.ρ a x.2 = 0
    rw [show x.2 = 0 from hx, map_zero]

/-- The first summand is nonzero when `P` is nontrivial. -/
theorem AMod.fstSub_ne_bot (P Q : AMod W) (hP : Nontrivial P.carrier) :
    (AMod.fstSub P Q).carrier ≠ ⊥ := by
  obtain ⟨p, p', hpp⟩ := hP
  intro hb
  have hmem : ((p - p', 0) : P.carrier × Q.carrier) ∈ (AMod.fstSub P Q).carrier := rfl
  have hz := (Submodule.eq_bot_iff _).mp hb _ hmem
  exact sub_ne_zero.mpr hpp (congrArg Prod.fst hz)

/-- The first summand is proper when `Q` is nontrivial. -/
theorem AMod.fstSub_ne_top (P Q : AMod W) (hQ : Nontrivial Q.carrier) :
    (AMod.fstSub P Q).carrier ≠ ⊤ := by
  obtain ⟨q, q', hqq⟩ := hQ
  intro ht
  have hmem : ((0, q - q') : P.carrier × Q.carrier) ∈ (AMod.fstSub P Q).carrier := by
    rw [ht]; trivial
  exact sub_ne_zero.mpr hqq (show ((0, q - q') : P.carrier × Q.carrier).2 = 0 from hmem)

/-- **A direct sum of two nontrivial `A(𝒱)`-modules refutes the dichotomy.** -/
theorem not_amodDichotomy_prod (P Q : AMod W) (hP : Nontrivial P.carrier)
    (hQ : Nontrivial Q.carrier) : ¬ AModDichotomy (P.prod Q) := fun h =>
  AMod.fstSub_ne_top P Q hQ (h _ (AMod.fstSub_ne_bot P Q hP))

/-- **A direct sum of two nontrivial `A(𝒱)`-modules is not simple.** -/
theorem not_isSimpleAMod_prod (P Q : AMod W) (hP : Nontrivial P.carrier)
    (hQ : Nontrivial Q.carrier) : ¬ IsSimpleAMod (P.prod Q) := fun h =>
  not_amodDichotomy_prod P Q hP hQ h.amodDichotomy

/-- **`∀ U : AMod W, AModDichotomy U` is FALSE** as soon as one nontrivial `A(𝒱)`-module exists —
the precise refutation of `InducedAssignment.BottomA0Irreducible`'s `∀ U : AMod W` scope. -/
theorem not_forall_amodDichotomy (P : AMod W) (hP : Nontrivial P.carrier) :
    ¬ ∀ U : AMod W, AModDichotomy U := fun h =>
  not_amodDichotomy_prod P P hP hP (h (P.prod P))

/-- **Nontriviality is NOT enough to repair the dichotomy.**  `ScopedNontrivial W AModDichotomy` is
still false: `P.prod P` is nontrivial and reducible.  The dichotomy genuinely needs the simple /
irreducible scope. -/
theorem not_scopedNontrivial_amodDichotomy (P : AMod W) (hP : Nontrivial P.carrier) :
    ¬ ScopedNontrivial W AModDichotomy := fun h =>
  not_amodDichotomy_prod P P hP hP (h (P.prod P) (AMod.prod_nontrivial P P hP))

/-! ### The `hL0` refutation: a direct sum of bottoms with distinct lowest weights -/

/-- Cancellation of a nonzero vector against two scalars in a `ℂ`-vector space. -/
theorem eq_of_smul_eq_smul_right {M : Type*} [AddCommGroup M] [Module ℂ M] {c d : ℂ} {x : M}
    (hx : x ≠ 0) (hcd : c • x = d • x) : c = d := by
  by_contra hne
  have hc : (c - d) ≠ 0 := sub_ne_zero.mpr hne
  have h0 : (c - d) • x = 0 := by rw [sub_smul, hcd, sub_self]
  have hinv := congrArg (fun y => (c - d)⁻¹ • y) h0
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] at hinv
  exact hx hinv

/-- **A direct sum of two `[ω]`-scalar modules with *distinct* scalars is `[ω]`-scalar for no `h`.**
Hence the `L0_on_deg` field of `MUFullModuleData W U h` cannot be asked of an arbitrary
`U : AMod W`: it is unsatisfiable exactly off the `OmegaScalar` scope. -/
theorem not_omegaScalar_prod (P Q : AMod W) {h₁ h₂ : ℂ} (hP : P.OmegaScalar h₁)
    (hQ : Q.OmegaScalar h₂) (hPnt : Nontrivial P.carrier) (hQnt : Nontrivial Q.carrier)
    (hne : h₁ ≠ h₂) (h : ℂ) : ¬ (P.prod Q).OmegaScalar h := by
  intro hpq
  obtain ⟨p, p', hpp⟩ := hPnt
  obtain ⟨q, q', hqq⟩ := hQnt
  have hp0 : p - p' ≠ 0 := sub_ne_zero.mpr hpp
  have hq0 : q - q' ≠ 0 := sub_ne_zero.mpr hqq
  have e1 := AMod.omegaScalar_apply hpq ((p - p', 0) : P.carrier × Q.carrier)
  have e2 := AMod.omegaScalar_apply hpq ((0, q - q') : P.carrier × Q.carrier)
  have hfst : P.ρ (_root_.VOA.mk W W.conformalVector) (p - p') = h • (p - p') :=
    congrArg Prod.fst e1
  have hsnd : Q.ρ (_root_.VOA.mk W W.conformalVector) (q - q') = h • (q - q') :=
    congrArg Prod.snd e2
  rw [AMod.omegaScalar_apply hP] at hfst
  rw [AMod.omegaScalar_apply hQ] at hsnd
  exact hne ((eq_of_smul_eq_smul_right hp0 hfst).trans
    (eq_of_smul_eq_smul_right hq0 hsnd).symm)

/-- **`∀ U : AMod W, ∃ h, U.OmegaScalar h` is FALSE** whenever two bottoms with distinct lowest
weights exist — the refutation of the `hL0` field at `∀ U : AMod W` scope. -/
theorem not_forall_exists_omegaScalar {P Q : AMod W} {h₁ h₂ : ℂ} (hP : P.OmegaScalar h₁)
    (hQ : Q.OmegaScalar h₂) (hPnt : Nontrivial P.carrier) (hQnt : Nontrivial Q.carrier)
    (hne : h₁ ≠ h₂) : ¬ ∀ U : AMod W, ∃ h : ℂ, U.OmegaScalar h := by
  intro hall
  obtain ⟨h, hh⟩ := hall (P.prod Q)
  exact not_omegaScalar_prod P Q hP hQ hPnt hQnt hne h hh

/-! ## §8  The corrected `hbot` on the β-track carrier `MUFull`

`MUFullModuleData W U h` (`Modules.ZhuVermaAnArchMUFullLW`) carries the field
`bottom_ne_bot : MUFull.deg W U 0 ≠ ⊥`.  At `∀ U : AMod W` scope that field is FALSE; on the
nontrivial scope it follows from the balanced-bottom map. -/

/-- Every element of a tensor product whose right factor is a subsingleton is `0`. -/
theorem tensor_eq_zero_of_subsingleton {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] (z : TensorProduct R M N) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul x y => rw [Subsingleton.elim y (0 : N), TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

/-- **The bottom of `M(zeroAMod W)` is `⊥`** — the refutation certificate for the `bottom_ne_bot`
field at `∀ U : AMod W` scope. -/
theorem MUFull.deg_zero_eq_bot_zeroAMod (W : VertexOperatorAlgebra 𝒱) :
    MUFull.deg W (zeroAMod W) 0 = ⊥ := by
  rw [MUFull.deg, LinearMap.range_eq_bot]
  refine LinearMap.ext fun z => ?_
  rw [tensor_eq_zero_of_subsingleton z, map_zero, LinearMap.zero_apply]

/-- **`∀ U : AMod W, MUFull.deg W U 0 ≠ ⊥` is FALSE.** -/
theorem not_forall_muFull_bottom_ne_bot (W : VertexOperatorAlgebra 𝒱) :
    ¬ ∀ U : AMod W, MUFull.deg W U 0 ≠ ⊥ := fun h =>
  h (zeroAMod W) (MUFull.deg_zero_eq_bot_zeroAMod W)

/-- **A nonzero level piece gives a nonzero graded layer** (the level projections are idempotent, so
`incl n` is injective). -/
theorem MUFull.deg_ne_bot_of_nontrivial (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (hnt : Nontrivial (MUPieceFull W U n)) : MUFull.deg W U n ≠ ⊥ := by
  obtain ⟨z, hz⟩ := exists_ne (0 : MUPieceFull W U n)
  intro hbot
  have hmem : MUFull.incl W U n z ∈ MUFull.deg W U n := ⟨z, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  refine hz ?_
  have hp := congrArg (MUFull.proj W U n) hmem
  rwa [MUFull.proj_incl_same, map_zero] at hp

/-- A surjective linear map from `A` onto a nontrivial `B` forces `A` nontrivial. -/
theorem nontrivial_of_surjective_linear {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (f : A →ₗ[ℂ] B) (hf : Function.Surjective f)
    (hB : Nontrivial B) : Nontrivial A := by
  obtain ⟨x, y, hxy⟩ := hB
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  exact ⟨a, b, fun hh => hxy (congrArg f hh)⟩

/-- **The corrected `hbot`, on the nontrivial scope.**  Given the balanced-bottom map
`f : A_{0,0}(𝒱) ⊗_ℂ U → U` (surjective — the pending balanced-bottom surgery over `AnmFull`
supplies it), the `bottom_ne_bot` field of `MUFullModuleData` follows **for nontrivial `U`**, and
by §7 only there. -/
theorem MUFull.bottom_ne_bot_of_bottomMap (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (f : MUPieceFull W U 0 →ₗ[ℂ] U.carrier) (hf : Function.Surjective f)
    (hU : Nontrivial U.carrier) : MUFull.deg W U 0 ≠ ⊥ :=
  MUFull.deg_ne_bot_of_nontrivial W U 0 (nontrivial_of_surjective_linear f hf hU)

/-- **The corrected `hbot` on `IrrAMod`.**  On the faithful codomain of Theorem 5.3.4 the
nontriviality hypothesis is automatic (`IrrAMod.nontrivial`), so a surjective bottom map is the only
remaining input. -/
theorem MUFull.bottom_ne_bot_of_bottomMap_irr (W : VertexOperatorAlgebra 𝒱) (U : IrrAMod W)
    (f : MUPieceFull W U.1 0 →ₗ[ℂ] U.1.carrier) (hf : Function.Surjective f) :
    MUFull.deg W U.1 0 ≠ ⊥ :=
  MUFull.bottom_ne_bot_of_bottomMap W U.1 f hf U.nontrivial

/-- **The corrected `hbot` as a scoped statement.**  `ScopedNontrivial W (fun U => …)` is the shape
the `bottom_ne_bot` field should be quantified over; here it is, discharged from a uniform family of
surjective bottom maps. -/
theorem scopedNontrivial_muFull_bottom_ne_bot (W : VertexOperatorAlgebra 𝒱)
    (f : ∀ U : AMod W, MUPieceFull W U 0 →ₗ[ℂ] U.carrier)
    (hf : ∀ U : AMod W, Function.Surjective (f U)) :
    ScopedNontrivial W (fun U => MUFull.deg W U 0 ≠ ⊥) :=
  fun U hU => MUFull.bottom_ne_bot_of_bottomMap W U (f U) (hf U) hU

/-- **The corrected `hbot` on the faithful codomain.**  On `IrrAMod W` — the scope in which
Theorem 5.3.4 is actually stated — nontriviality is automatic, so a uniform family of surjective
bottom maps discharges `bottom_ne_bot` outright.  No gate on `AllIrrBottomRecovers` is needed: the
`hbot` repair lives at the *nontrivial* scope, strictly coarser than the simple scope. -/
theorem scopedIrr_muFull_bottom_ne_bot (W : VertexOperatorAlgebra 𝒱)
    (f : ∀ U : AMod W, MUPieceFull W U 0 →ₗ[ℂ] U.carrier)
    (hf : ∀ U : AMod W, Function.Surjective (f U)) :
    ScopedIrr W (fun U => MUFull.deg W U 0 ≠ ⊥) :=
  (scopedNontrivial_muFull_bottom_ne_bot W f hf).scopedIrr

end AModScope

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.AModDichotomy
  #print axioms VOA.AMod.OmegaScalar
  #print axioms VOA.AModEquiv.comapSubmodule
  #print axioms VOA.AModEquiv.isSimpleAMod_target
  #print axioms VOA.AModEquiv.amodDichotomy_target
  #print axioms VOA.AModEquiv.omegaScalar_target
  #print axioms VOA.lowestAMod_omegaScalar
  #print axioms VOA.LWModule.toAMod_omegaScalar
  #print axioms VOA.omegaScalar_of_bottomEquiv
  #print axioms VOA.IrrAMod.nontrivial
  #print axioms VOA.IrrAMod.omegaScalar
  #print axioms VOA.IrrAMod.isSimpleAMod
  #print axioms VOA.IrrAMod.amodDichotomy
  #print axioms VOA.isSimpleAMod_iff
  #print axioms VOA.AllIrrBottomRecovers
  #print axioms VOA.AllBottomRecovers.allIrr
  #print axioms VOA.IsBottomOfIrr.isSimpleAMod_irr
  #print axioms VOA.IrrAMod.isSimpleAMod_irr
  #print axioms VOA.IrrAMod.amodDichotomy_irr
  #print axioms VOA.ScopedSimple.scopedIrr_irr
  #print axioms VOA.scopedIrr_muFull_bottom_ne_bot
  #print axioms VOA.scopedSimple_amodDichotomy
  #print axioms VOA.scopedIrr_omegaScalar
  #print axioms VOA.zeroAMod
  #print axioms VOA.not_forall_nontrivial
  #print axioms VOA.not_forall_isSimpleAMod
  #print axioms VOA.not_forall_amodDichotomy
  #print axioms VOA.not_scopedNontrivial_amodDichotomy
  #print axioms VOA.not_forall_exists_omegaScalar
  #print axioms VOA.MUFull.deg_zero_eq_bot_zeroAMod
  #print axioms VOA.not_forall_muFull_bottom_ne_bot
  #print axioms VOA.MUFull.bottom_ne_bot_of_bottomMap
  #print axioms VOA.scopedNontrivial_muFull_bottom_ne_bot
-/
