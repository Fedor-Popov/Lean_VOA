/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLU
import VOA.Modules.ZhuVermaAnArchAModScope

/-!
# Zhu 5.3.4 — the final assembly of `Function.Bijective (forwardMapIrr W)`

`Modules.ZhuVermaAnArchFaithfulBijection` defines the faithful forward map

  `forwardMapIrr W : IrrLWModuleIsoClass W → IrrAModIsoClass W`,  `[M] ↦ [M_h]`,

between iso-classes of **irreducible** bundled lowest-weight `𝒱`-modules and the image-defined
codomain `IrrAMod W = {U : AMod W // IsBottomOfIrr U}`.  Its existing bijectivity theorem
(`InducedAssignment.forwardMapIrr_bijective`) consumes a **total** `InducedAssignment W`
(`realize : AMod W → LWModule W` for *every* bundled `A(𝒱)`-module), the global
`RealizeIrreducible` (`∀ U`), and the universal property `GeneratedFromBottom W`.

This file replaces that input list by a **single** named hypothesis and shows the replacement is
optimal.  Nothing existing is modified.

## What is proved here (proof terms `#print axioms`-clean, no `sorry`, no new axiom)

This is a proof-term audit, not an unconditionality claim: declarations in §6 explicitly carry
`Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))`. Explicit parameters are not
reported by `#print axioms`. The project-level witness `voaPBWBottomProjection` is supplied from
the generic relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.

### §1 Surjectivity is unconditional
**`forwardMapIrr_surjective_uncond`** — `Function.Surjective (forwardMapIrr W)` with **no**
hypothesis at all.  ⚠ Read this honestly: the codomain `IrrAMod W` is *defined* as the image
predicate `IsBottomOfIrr U := ∃ P irreducible, P.toAMod ≅ U`, so surjectivity of `forwardMapIrr`
is a tautology of the statement, **not** the mathematical surjectivity of Zhu's correspondence.
The genuine surjectivity content is `SimpleAModsRealized` (§5): *every simple `A(𝒱)`-module is a
bottom*.  It follows that the `A : InducedAssignment W` and `hirr` arguments of the existing
`InducedAssignment.forwardMapIrr_surjective` are **not needed**.

### §2–§3 Injectivity is EXACTLY `IrredBottomRigidity`
**`forwardMapIrr_injective_of_rigidity`**, **`irredBottomRigidity_of_injective`**,
**`forwardMapIrr_injective_iff_rigidity`**, and the headline
**`forwardMapIrr_bijective_iff_rigidity`** :
`Function.Bijective (forwardMapIrr W) ↔ IrredBottomRigidity W`.
So `IrredBottomRigidity W` (Zhu's irreducible uniqueness) is not merely *sufficient* — it is
**necessary and sufficient**.  No smaller hypothesis set can exist.

### §4 The scoped universal property, and a REFUTATION
**`GeneratedFromBottomIrr W`** — the universal property indexed by `IrrAMod W` only, strictly
weaker than the repo's `InducedAssignment.GeneratedFromBottom W`
(`generatedFromBottomIrr_of_generatedFromBottom`), and still enough:
**`irredBottomRigidity_of_universalIrr`**, **`forwardMapIrr_bijective_of_universalIrr`**; the
converse `generatedFromBottomIrr_of_rigidity` makes all three notions equivalent.

⚠⚠ **`not_nonempty_inducedAssignment` — `InducedAssignment W` IS UNINHABITED**, because `realize`
is total on `AMod W` while `zeroAMod W` has a subsingleton carrier and every `LWModule` bottom is
nontrivial.  Hence `not_nonempty_faithfulScorecard`, and hence *every* bijection theorem consuming
an `InducedAssignment` (`InducedAssignment.forwardMapIrr_bijective`,
`FaithfulScorecard.bijectiveIrr`, `zhuBijectionIrr_scorecard`, the `zhuBijection_*` family) is
**vacuously** true and can never be discharged as typed.  Also
`not_forall_hasInducedModule` refutes `Modules/ZhuInducedPointwise`'s pointwise hypothesis.  The
`IrredBottomRigidity` route of §3 is therefore not merely weaker — it is the only satisfiable one.

### §5 The C5 bridge: finrank-free graded modules into the `LWModule` chain
`GradedLWWeakModule.FiniteWeights`, **`GradedLWWeakModule.toOrdVModule`**,
**`GradedLWWeakModule.toLWModule`**, `toLWModule_isIrreducibleLW`, the packaged
**`IrrRealization W U`**, **`isBottomOfIrr_of_irrRealization`**, `SimpleAModsRealized`, and the
codomain-fidelity theorem **`isBottomOfIrr_iff_isSimpleAMod`** (`IrrAMod W` really is
`Irr A(𝒱)`, modulo `AllBottomRecovers` one way and `SimpleAModsRealized` the other).

### §6 Dong–Jiang's `L(U)` wired in
**`djLU_bottom_U_oMod`** (the `A(𝒱)`-equivariance of `L(U)_h ≅ U` for *all* — not only
homogeneous — algebra elements, through the module zero mode `o(u)`),
**`djLU_bottomAModEquiv`**, **`djIrrRealization`**, **`djLU_isBottomOfIrr`**.

## What is NOT proved (see the module's closing section for the full ledger)

`Function.Bijective (forwardMapIrr W)` does **not** assemble unconditionally.  The exact residual
is `IrredBottomRigidity W`, equivalently `GeneratedFromBottomIrr W` — the universal property of
`M(U)`, which C5 explicitly did **not** build (`ZhuVermaAnArchLU`, "The other bijection direction,
and exactly what is still missing").  §5–§6 discharge everything on the *existence* side except the
two named data `FiniteWeights` (the `OrdVModule.finrank` field, absent from the finrank-free C5
layer) and the C5 scope `Pr`/`hU`/`hL0`/`hsimple`.

## References
Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu; Dong–Jiang `math/0601626` Thm 4.13;
Dong–Li–Mason `q-alg/9612010` §4.  Repo: `ZhuVermaAnArchFaithfulBijection` (`forwardMapIrr`),
`ZhuVermaAnArchRigidity` (`IrredBottomRigidity`), `ZhuVermaAnArchGameTwo` (`GeneratedFromBottom`),
`ZhuVermaAnArchLUGraded` / `ZhuVermaAnArchLU` (C5), `ZhuVermaAnArchAModScope` (the scope).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 Surjectivity of the faithful forward map is unconditional -/

/-- **`forwardMapIrr` is surjective — with no hypotheses whatsoever.**

Given `U : IrrAMod W`, its defining property `IsBottomOfIrr U.1` *is* a witness: an irreducible
`P : LWModule W` together with an `A(𝒱)`-iso `P.toAMod ≅ U.1`.  Then `[⟨P, hP⟩]` maps to `[U]`.

⚠ **Honest reading.**  The codomain `IrrAMod W` is the *image* predicate, so this is a tautology of
the statement of the faithful bijection, not the mathematical content "every irreducible
`A(𝒱)`-module is the bottom of an irreducible `𝒱`-module".  That content is `SimpleAModsRealized`
(§5), which is what Dong–Jiang's `L(U)` supplies.  What this theorem *does* establish is that the
`InducedAssignment` and `RealizeIrreducible` arguments of the existing
`InducedAssignment.forwardMapIrr_surjective` are **unnecessary**. -/
theorem forwardMapIrr_surjective_uncond (W : VertexOperatorAlgebra 𝒱) :
    Function.Surjective (forwardMapIrr W) := by
  intro y
  induction y using Quotient.ind with
  | _ U =>
    obtain ⟨P, hP, he⟩ := U.2
    refine ⟨Quotient.mk (IrrLWModule.setoid W) ⟨P, hP⟩, ?_⟩
    rw [forwardMapIrr_mk]
    exact Quotient.sound he

/-! ## §2 Injectivity is *exactly* `IrredBottomRigidity` -/

section Injectivity

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Injectivity of `forwardMapIrr` from `IrredBottomRigidity`.**  Two irreducible classes with
the same bottom class have `A(𝒱)`-isomorphic bottoms (`Quotient.exact` in the codomain), so
rigidity makes them `𝒱`-isomorphic. -/
theorem forwardMapIrr_injective_of_rigidity (hrig : IrredBottomRigidity W) :
    Function.Injective (forwardMapIrr W) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro P Q hPQ
  rw [forwardMapIrr_mk, forwardMapIrr_mk] at hPQ
  exact Quotient.sound (hrig P.1 Q.1 P.2 Q.2 (Quotient.exact hPQ))

/-- **`IrredBottomRigidity` from injectivity of `forwardMapIrr`** — the converse, so the hypothesis
of `forwardMapIrr_injective_of_rigidity` is *necessary*, not merely sufficient. -/
theorem irredBottomRigidity_of_injective (hinj : Function.Injective (forwardMapIrr W)) :
    IrredBottomRigidity W := by
  intro P Q hP hQ hbot
  refine Quotient.exact (hinj ?_ : (Quotient.mk (IrrLWModule.setoid W) ⟨P, hP⟩
    : IrrLWModuleIsoClass W) = Quotient.mk (IrrLWModule.setoid W) ⟨Q, hQ⟩)
  rw [forwardMapIrr_mk, forwardMapIrr_mk]
  exact Quotient.sound hbot

/-- **Injectivity of `forwardMapIrr` *is* Zhu's irreducible uniqueness.** -/
theorem forwardMapIrr_injective_iff_rigidity :
    Function.Injective (forwardMapIrr W) ↔ IrredBottomRigidity W :=
  ⟨irredBottomRigidity_of_injective, forwardMapIrr_injective_of_rigidity⟩

end Injectivity

/-! ## §3 The headline: `Bijective (forwardMapIrr W) ↔ IrredBottomRigidity W` -/

section Bijection

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Zhu 5.3.4 at the irreducible scope, from ONE named hypothesis.**

`Function.Bijective (forwardMapIrr W)` — the faithful bijection `Φ(𝒱) ↔ Irr A(𝒱)` — follows from
the single Prop `hrig : IrredBottomRigidity W` (any two irreducible bundled lowest-weight
`𝒱`-modules with `A(𝒱)`-isomorphic bottoms are `𝒱`-isomorphic).  Surjectivity needs nothing.

Compare `InducedAssignment.forwardMapIrr_bijective`, which consumes a total `InducedAssignment W`,
`RealizeIrreducible` and `GeneratedFromBottom W`.  Of those, `GeneratedFromBottom` alone already
implies the hypothesis used here (`GeneratedFromBottom ⟹ GeneratedFromBottomIrr ⟹
IrredBottomRigidity`, §4), so `A` and `hirr` are redundant — and `A` is moreover *unsatisfiable*
(`not_nonempty_inducedAssignment`, §4). -/
theorem forwardMapIrr_bijective_of_rigidity (hrig : IrredBottomRigidity W) :
    Function.Bijective (forwardMapIrr W) :=
  ⟨forwardMapIrr_injective_of_rigidity hrig, forwardMapIrr_surjective_uncond W⟩

/-- **The hypothesis is exactly right**: the faithful Zhu bijection at the irreducible scope
holds **iff** irreducibles are determined by their bottoms.  No weaker input can suffice. -/
theorem forwardMapIrr_bijective_iff_rigidity :
    Function.Bijective (forwardMapIrr W) ↔ IrredBottomRigidity W :=
  ⟨fun hb => irredBottomRigidity_of_injective hb.1, forwardMapIrr_bijective_of_rigidity⟩

/-- **The faithful Zhu bijection as an `Equiv`**, from the single rigidity hypothesis. -/
noncomputable def zhuEquivIrrOfRigidity (hrig : IrredBottomRigidity W) :
    IrrLWModuleIsoClass W ≃ IrrAModIsoClass W :=
  Equiv.ofBijective _ (forwardMapIrr_bijective_of_rigidity hrig)

@[simp] theorem zhuEquivIrrOfRigidity_apply (hrig : IrredBottomRigidity W)
    (x : IrrLWModuleIsoClass W) : zhuEquivIrrOfRigidity hrig x = forwardMapIrr W x := rfl

end Bijection

/-! ## §4 The universal property, scoped to the irreducible codomain -/

section Universal

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`GeneratedFromBottomIrr W`** — the universal property of the generalized Verma module,
indexed **only** by the faithful codomain `IrrAMod W`.  There is a family `K` of bundled
lowest-weight modules, one per bottom-of-an-irreducible, that is constant on `A(𝒱)`-iso classes and
recovers every irreducible from its own bottom.

This is strictly weaker than `InducedAssignment.GeneratedFromBottom W`, which demands `K` on **all**
of `AMod W` (see `generatedFromBottomIrr_of_generatedFromBottom`); the difference matters because a
total `AMod W → LWModule W` assignment is exactly what the `OrdVModule.finrank` field obstructs. -/
def GeneratedFromBottomIrr (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∃ K : IrrAMod W → LWModule W,
    (∀ U₁ U₂ : IrrAMod W, Nonempty (AModEquiv W U₁.1 U₂.1) → LWModule.Iso W (K U₁) (K U₂)) ∧
    (∀ P : IrrLWModule W, LWModule.Iso W (K P.toIrrAMod) P.1)

/-- The repo's total universal property implies the scoped one (restrict `K` along
`Subtype.val`). -/
theorem generatedFromBottomIrr_of_generatedFromBottom
    (hgen : InducedAssignment.GeneratedFromBottom W) : GeneratedFromBottomIrr W := by
  obtain ⟨K, hKwd, hKreal⟩ := hgen
  exact ⟨fun U => K U.1, fun U₁ U₂ h => hKwd U₁.1 U₂.1 h, fun P => hKreal P.1 P.2⟩

/-- **`IrredBottomRigidity` from the scoped universal property.**  Both irreducibles are `≅ K` of
their (common, up to iso) bottom. -/
theorem irredBottomRigidity_of_universalIrr (hgen : GeneratedFromBottomIrr W) :
    IrredBottomRigidity W := by
  obtain ⟨K, hKwd, hKreal⟩ := hgen
  intro P Q hP hQ hbot
  have hP' : LWModule.Iso W P (K (IrrLWModule.toIrrAMod ⟨P, hP⟩)) :=
    (LWModule.setoid W).symm (hKreal ⟨P, hP⟩)
  have hK : LWModule.Iso W (K (IrrLWModule.toIrrAMod ⟨P, hP⟩))
      (K (IrrLWModule.toIrrAMod ⟨Q, hQ⟩)) := hKwd _ _ hbot
  have hQ' : LWModule.Iso W (K (IrrLWModule.toIrrAMod ⟨Q, hQ⟩)) Q := hKreal ⟨Q, hQ⟩
  exact (LWModule.setoid W).trans ((LWModule.setoid W).trans hP' hK) hQ'

/-- **The faithful Zhu bijection from the scoped universal property.** -/
theorem forwardMapIrr_bijective_of_universalIrr (hgen : GeneratedFromBottomIrr W) :
    Function.Bijective (forwardMapIrr W) :=
  forwardMapIrr_bijective_of_rigidity (irredBottomRigidity_of_universalIrr hgen)

/-- **The scoped universal property is also necessary** (take `K [U] := ` a realizer supplied by
the bijection).  Together with `forwardMapIrr_bijective_iff_rigidity` this shows
`GeneratedFromBottomIrr`, `IrredBottomRigidity` and `Bijective (forwardMapIrr W)` are all
equivalent. -/
theorem generatedFromBottomIrr_of_rigidity (hrig : IrredBottomRigidity W) :
    GeneratedFromBottomIrr W := by
  classical
  refine ⟨fun U => U.2.choose, ?_, ?_⟩
  · intro U₁ U₂ h
    obtain ⟨e⟩ := h
    have h₁ := U₁.2.choose_spec
    have h₂ := U₂.2.choose_spec
    obtain ⟨e₁⟩ := h₁.2
    obtain ⟨e₂⟩ := h₂.2
    exact hrig _ _ h₁.1 h₂.1
      ⟨AModEquiv.trans W (AModEquiv.trans W e₁ e) (AModEquiv.symm W e₂)⟩
  · intro P
    have hspec := (P.toIrrAMod).2.choose_spec
    obtain ⟨e⟩ := hspec.2
    exact hrig _ _ hspec.1 P.2 ⟨e⟩

/-! ### ⚠ REFUTATION — `InducedAssignment W` is UNINHABITED, so the hypothesis bundle route is vacuous

The three theorems below are a *hard refutation*, not a reduction.  `InducedAssignment.realize` is
a **total** map `AMod W → LWModule W` whose value at `U` must have bottom `≅ U`; but every bundled
lowest-weight module is *realized* (`LWModule.realized : M_h ≠ ⊥`), so every bottom is nontrivial
(`nontrivial_toAMod`), while `zeroAMod W` (`ZhuVermaAnArchAModScope`) is a perfectly legal `AMod W`
with a subsingleton carrier.

Consequences, all sharp:
* `InducedAssignment W` has no inhabitant, hence `FaithfulScorecard W` (whose first field is an
  `InducedAssignment W`) has none either;
* every theorem of the form `… (A : InducedAssignment W) … → Function.Bijective (forwardMapIrr W)`
  — `InducedAssignment.forwardMapIrr_bijective`, `FaithfulScorecard.bijectiveIrr`,
  `zhuBijectionIrr_scorecard`, and the whole `zhuBijection_*` family — is **vacuously** true and can
  never be discharged as typed;
* `Modules/ZhuInducedPointwise`'s `∀ U, HasInducedModule W U` is false for the same reason.

This is why §3's `IrredBottomRigidity` route is not merely *weaker*: it is the only satisfiable one.
The repair on the existence side is the scoped `IrrRealization`/`SimpleAModsRealized` of §5. -/

/-- **No lowest-weight `𝒱`-module realizes the zero `A(𝒱)`-module.** -/
theorem not_hasInducedModule_zeroAMod (W : VertexOperatorAlgebra 𝒱) :
    ¬ HasInducedModule W (zeroAMod W) := by
  rintro ⟨R⟩
  exact not_nontrivial_zeroAMod W (R.bottomEquiv.nontrivial_target (nontrivial_toAMod R.N))

/-- **`∀ U : AMod W, HasInducedModule W U` is FALSE** — the pointwise hypothesis of
`Modules/ZhuInducedPointwise` is unsatisfiable as stated. -/
theorem not_forall_hasInducedModule (W : VertexOperatorAlgebra 𝒱) :
    ¬ ∀ U : AMod W, HasInducedModule W U :=
  fun h => not_hasInducedModule_zeroAMod W (h (zeroAMod W))

/-- ⚠⚠ **`InducedAssignment W` IS UNINHABITED.**  Hence `FaithfulScorecard W` is uninhabited and
every bijection theorem consuming one is vacuous. -/
theorem not_nonempty_inducedAssignment (W : VertexOperatorAlgebra 𝒱) :
    ¬ Nonempty (InducedAssignment W) := by
  rintro ⟨A⟩
  exact not_forall_hasInducedModule W (fun U => ⟨A.toRealization U⟩)

/-- **`FaithfulScorecard W` is uninhabited** — the corollary that matters for the ledger. -/
theorem not_nonempty_faithfulScorecard (W : VertexOperatorAlgebra 𝒱) :
    ¬ Nonempty (FaithfulScorecard W) :=
  fun h => not_nonempty_inducedAssignment W ⟨h.some.A⟩

/-! ### The existing hypothesis bundle route factors through the rigidity hypothesis

The two theorems below are `zhuBijectionIrr_scorecard` / `FaithfulScorecard.bijectiveIrr` with the
`A : InducedAssignment W` and `hirr : A.RealizeIrreducible` arguments **deleted** — a strict
weakening that also removes the *unsatisfiable* one. -/

/-- **The faithful bijection from the total universal property alone** — no `InducedAssignment`,
no `RealizeIrreducible`. -/
theorem forwardMapIrr_bijective_of_generatedFromBottom
    (hgen : InducedAssignment.GeneratedFromBottom W) :
    Function.Bijective (forwardMapIrr W) :=
  forwardMapIrr_bijective_of_rigidity (InducedAssignment.irredBottomRigidity_of_universal hgen)

/-- **The faithful bijection from the `L(U)`-family alone** — exactly `zhuBijectionIrr_scorecard`
with its `A` and `hirr` arguments removed. -/
theorem zhuBijectionIrr_of_LUFamily (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  forwardMapIrr_bijective_of_generatedFromBottom
    (InducedAssignment.generatedFromBottom_final F hiso G)

end Universal

/-! ## §5 The C5 bridge — finrank-free graded modules into the `LWModule` chain -/

namespace GradedLWWeakModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M] {hw : ℂ}

/-- **`FiniteWeights N`** — the one `OrdVModule` field that the finrank-free C5 layer deliberately
drops: every weight space is finite-dimensional.  Carried as an explicit named hypothesis, never
assumed. -/
def FiniteWeights (N : GradedLWWeakModule W M hw) : Prop :=
  ∀ α : ℂ, FiniteDimensional ℂ (N.weight α)

/-- **A finrank-free graded lowest-weight weak module becomes a `OrdVModule`** once `FiniteWeights` is
supplied.  This is the *only* difference between `GradedLWWeakModule` and `OrdVModule`. -/
def toOrdVModule (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights) : OrdVModule W M where
  toWeakModule := N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  L0_weight := N.L0_weight
  finrank := hfin
  boundedBelow := N.boundedBelow

@[simp] theorem toOrdVModule_weight (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights)
    (α : ℂ) : (N.toOrdVModule hfin).weight α = N.weight α := rfl

@[simp] theorem toOrdVModule_toWeakModule (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights) :
    (N.toOrdVModule hfin).toWeakModule = N.toWeakModule := rfl

/-- The lowest-weight datum transfers verbatim. -/
theorem toOrdVModule_isLowestWeight (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights) :
    IsLowestWeight (N.toOrdVModule hfin) hw := N.isLow

/-- **The bundled lowest-weight `𝒱`-module of a finrank-free graded module**, i.e. the entry point
into the `forwardMapIrr` chain.  `realized` is the C5 structure's own field. -/
def toLWModule (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights) : LWModule W where
  carrier := M
  isMod := N.toOrdVModule hfin
  h := hw
  isLow := N.isLow
  realized := N.realized

@[simp] theorem toLWModule_isMod (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights) :
    (N.toLWModule hfin).isMod = N.toOrdVModule hfin := rfl

@[simp] theorem toLWModule_h (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights) :
    (N.toLWModule hfin).h = hw := rfl

/-- **Irreducibility transfers.**  `GradedLWWeakModule.IsIrreducible` and
`OrdVModule.IsIrreducible` are the same statement about the same weak-module structure. -/
theorem toLWModule_isIrreducibleLW (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights)
    (hirr : GradedLWWeakModule.IsIrreducible N) : (N.toLWModule hfin).IsIrreducibleLW := hirr

/-! ### The `A(𝒱)`-action on the bottom, in terms of the graded weak module's own modes

`LWModule.toAMod` acts by `actA`/`rhoLW`, i.e. by the *summed* module zero mode `o(u)`.  C5's
equivariance statements are phrased with the raw mode `a₍ₖ₋₁₎` of a homogeneous `a ∈ 𝒱ₖ`.  The two
lemmas below bridge that gap **abstractly** (no `DJCarrier` in sight), which is also what keeps the
elaboration cheap at the instantiation. -/

/-- On a homogeneous `a ∈ 𝒱ₖ` the bottom action `rhoLW` is the raw mode `a₍ₖ₋₁₎`. -/
theorem rhoLW_homog_coe (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights)
    {k : ℤ} {a : 𝒱} (ha : a ∈ W.grading k) (y : N.weight hw) :
    ((rhoLW (N.toOrdVModule hfin) hw a y : (N.toOrdVModule hfin).weight hw) : M)
      = N.toWeakModule.act a (k - 1) (y : M) := by
  rw [rhoLW_apply_coe, oMod_homogeneous (N.toOrdVModule hfin) ha, WeakModule.act_def]
  rfl

/-- **From homogeneous equivariance to `A(𝒱)`-equivariance.**  If a linear equivalence `e` of the
bottom onto a space `C` intertwines every raw mode `a₍ₖ₋₁₎` (`a ∈ 𝒱ₖ`) with a `ℂ`-linear family
`σ : 𝒱 →ₗ[ℂ] End ℂ C`, then it intertwines the full zero-mode action `rhoLW` for **every** `u : 𝒱`.
Both sides are linear in `u`, so the `𝒱`-grading induction closes it. -/
theorem bottom_equivariance_of_homog (N : GradedLWWeakModule W M hw) (hfin : N.FiniteWeights)
    {C : Type u} [AddCommGroup C] [Module ℂ C] (e : N.weight hw ≃ₗ[ℂ] C)
    (σ : 𝒱 →ₗ[ℂ] Module.End ℂ C)
    (hhom : ∀ {k : ℤ} {a : 𝒱}, a ∈ W.grading k → ∀ (y : N.weight hw)
      (hmem : N.toWeakModule.act a (k - 1) (y : M) ∈ N.weight hw),
      e ⟨N.toWeakModule.act a (k - 1) (y : M), hmem⟩ = σ a (e y))
    (u : 𝒱) (y : N.weight hw) :
    e (rhoLW (N.toOrdVModule hfin) hw u y) = σ u (e y) := by
  classical
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => e (rhoLW (N.toOrdVModule hfin) hw u y) = σ u (e y)) hutop ?_ ?_ ?_
  · intro k a ha
    have hcoe := N.rhoLW_homog_coe hfin ha y
    have hmem : N.toWeakModule.act a (k - 1) (y : M) ∈ N.weight hw := by
      rw [← hcoe]; exact (rhoLW (N.toOrdVModule hfin) hw a y).2
    have hEq : rhoLW (N.toOrdVModule hfin) hw a y
        = (⟨N.toWeakModule.act a (k - 1) (y : M), hmem⟩ : N.weight hw) := Subtype.ext hcoe
    rw [hEq]
    exact hhom ha y hmem
  · show e (rhoLW (N.toOrdVModule hfin) hw 0 y) = σ 0 (e y)
    rw [map_zero, map_zero]
    simp
    rfl
  · intro u₁ u₂ h₁ h₂
    show e (rhoLW (N.toOrdVModule hfin) hw (u₁ + u₂) y) = σ (u₁ + u₂) (e y)
    have hsplit : rhoLW (N.toOrdVModule hfin) hw (u₁ + u₂) y
        = rhoLW (N.toOrdVModule hfin) hw u₁ y + rhoLW (N.toOrdVModule hfin) hw u₂ y := by
      rw [map_add]; rfl
    have hcomb : e (rhoLW (N.toOrdVModule hfin) hw u₁ y + rhoLW (N.toOrdVModule hfin) hw u₂ y)
        = e (rhoLW (N.toOrdVModule hfin) hw u₁ y) + e (rhoLW (N.toOrdVModule hfin) hw u₂ y) :=
      map_add e _ _
    have hσ : σ (u₁ + u₂) (e y) = σ u₁ (e y) + σ u₂ (e y) := by
      rw [map_add]; rfl
    rw [hsplit, hcomb, h₁, h₂, hσ]

end GradedLWWeakModule

section Realization

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`IrrRealization W U`** — a realization of the bundled `A(𝒱)`-module `U` by an *irreducible*
finrank-free graded lowest-weight weak module.  This is precisely the shape Dong–Jiang's `L(U)`
produces (`ZhuVermaAnArchLU`), packaged so that the `OrdVModule.finrank` obligation is a single named
field rather than an invisible obstruction. -/
structure IrrRealization (W : VertexOperatorAlgebra 𝒱) (U : AMod W) where
  /-- The underlying space of the realizing module. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- Its lowest weight. -/
  lowestWeight : ℂ
  /-- The finrank-free graded lowest-weight weak-module structure. -/
  graded : GradedLWWeakModule W carrier lowestWeight
  /-- Every weight space is finite-dimensional (the `OrdVModule.finrank` obligation). -/
  finiteWeights : graded.FiniteWeights
  /-- The realizing module is irreducible. -/
  irreducible : GradedLWWeakModule.IsIrreducible graded
  /-- Its bottom is `U`, as a bundled `A(𝒱)`-module. -/
  bottomEquiv : AModEquiv W (graded.toLWModule finiteWeights).toAMod U

attribute [instance] IrrRealization.addCommGroup IrrRealization.module

/-- **A realization puts `U` into the faithful codomain `IrrAMod W`.** -/
theorem isBottomOfIrr_of_irrRealization {U : AMod W} (R : IrrRealization W U) :
    IsBottomOfIrr U :=
  ⟨R.graded.toLWModule R.finiteWeights,
    R.graded.toLWModule_isIrreducibleLW R.finiteWeights R.irreducible, ⟨R.bottomEquiv⟩⟩

/-- **`SimpleAModsRealized W`** — the *genuine* surjectivity content of Zhu 5.3.4: every simple
bundled `A(𝒱)`-module is realized as the bottom of an irreducible lowest-weight `𝒱`-module.
(Contrast §1: surjectivity of `forwardMapIrr` onto the *image-defined* codomain is free.) -/
def SimpleAModsRealized (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ U : AMod W, IsSimpleAMod U → Nonempty (IrrRealization W U)

/-- Simple `A(𝒱)`-modules are bottoms, given the realization family. -/
theorem isBottomOfIrr_of_simple (hreal : SimpleAModsRealized W) {U : AMod W}
    (hs : IsSimpleAMod U) : IsBottomOfIrr U :=
  (hreal U hs).elim isBottomOfIrr_of_irrRealization

/-- **The codomain is honest**: `IrrAMod W` is *exactly* the simple `A(𝒱)`-modules.  The `→`
direction is the proved `IsBottomOfIrr.isSimpleAMod` (gated on `AllBottomRecovers`); the `←`
direction is the realization family (Dong–Jiang's `L(U)`).  With both, "`Irr A(𝒱)`" in
`forwardMapIrr`'s codomain means what it says. -/
theorem isBottomOfIrr_iff_isSimpleAMod (hrec : AllBottomRecovers W)
    (hreal : SimpleAModsRealized W) (U : AMod W) :
    IsBottomOfIrr U ↔ IsSimpleAMod U :=
  ⟨fun hU => hU.isSimpleAMod hrec, fun hs => isBottomOfIrr_of_simple hreal hs⟩

end Realization

/-! ## §6 Dong–Jiang's `L(U)` as an `IrrRealization` -/

section DJ

open VHat VHat.DLM3 GradedLWWeakModule

variable {W : VertexOperatorAlgebra 𝒱}
variable (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AMod W)
  (hU : Nontrivial U.carrier) (hval : ℂ)
  (hL0 : ∀ (n : ℕ) (x : DJCarrier W U.toAmModZero), x ∈ DJCarrier.deg W U.toAmModZero n →
    djModeZero W U.toAmModZero 1 W.conformalVector x = (hval + n) • x)
  (hfin : (djLU Pr U.toAmModZero hU hval hL0).FiniteWeights)

/-- **`L(U)_h ≅ U` is `A(𝒱)`-equivariant for the FULL module zero mode `o(u)`.**

`djLU_bottom_U_rho` (`ZhuVermaAnArchLU`) gives the intertwining only for a *homogeneous* `a ∈ 𝒱ₖ`
and its conformal mode `a₍ₖ₋₁₎`.  The `AMod`-level statement needs it for every `u : 𝒱` through
`oMod`/`rhoLW`, which is what `LWModule.toAMod` uses.  Both sides are `ℂ`-linear in `u`, so the
homogeneous case propagates by `Submodule.iSup_induction` over the `𝒱`-grading. -/
theorem djLU_bottom_U_oMod (u : 𝒱)
    (y : (djLU Pr U.toAmModZero hU hval hL0).weight hval) :
    djLU_bottom_U Pr U.toAmModZero hU hval hL0
        (rhoLW ((djLU Pr U.toAmModZero hU hval hL0).toOrdVModule hfin) hval u y)
      = U.ρ (VOA.mk W u) (djLU_bottom_U Pr U.toAmModZero hU hval hL0 y) :=
  GradedLWWeakModule.bottom_equivariance_of_homog (djLU Pr U.toAmModZero hU hval hL0) hfin
    (djLU_bottom_U Pr U.toAmModZero hU hval hL0) (U.ρ.comp (O W).mkQ)
    (fun {_ _} ha y hmem => by
      rw [djLU_bottom_U_rho Pr U.toAmModZero hU hval hL0 ha y hmem]
      rfl) u y

/-- **The bottom of `L(U)` is `U` as a bundled `A(𝒱)`-module.** Carried inputs, all displayed:
the independent `BottomProjection` assumption `Pr`, the `AModScope` nontriviality `hU`, the
grading scalar `hL0`, and the
`OrdVModule.finrank` obligation `hfin`. -/
noncomputable def djLU_bottomAModEquiv :
    AModEquiv W ((djLU Pr U.toAmModZero hU hval hL0).toLWModule hfin).toAMod U where
  toLinearEquiv := djLU_bottom_U Pr U.toAmModZero hU hval hL0
  map_ρ := by
    intro a x
    refine Submodule.Quotient.induction_on (O W) a (fun v => ?_)
    show djLU_bottom_U Pr U.toAmModZero hU hval hL0
        (actA ((djLU Pr U.toAmModZero hU hval hL0).toOrdVModule hfin)
          ((djLU Pr U.toAmModZero hU hval hL0).toLWModule hfin).isLow
          (VOA.mk W v) x)
      = U.ρ (VOA.mk W v) (djLU_bottom_U Pr U.toAmModZero hU hval hL0 x)
    rw [actA_mk]
    exact djLU_bottom_U_oMod Pr U hU hval hL0 hfin v x

/-- **Dong–Jiang's `L(U)` packaged as an `IrrRealization W U`** — C5's existence direction wired
into the `forwardMapIrr` chain. Carried, all displayed: `Pr` (the independent `BottomProjection`
assumption),
`hU`, `hL0`, `hfin` (`OrdVModule.finrank`), and `hsimple` (the `AModScope` simplicity of `U`). -/
noncomputable def djIrrRealization (hsimple : IsSimpleAMod U) : IrrRealization W U where
  carrier := DJCarrier W U.toAmModZero ⧸ (djJ Pr U.toAmModZero hU hval hL0).carrier
  lowestWeight := hval
  graded := djLU Pr U.toAmModZero hU hval hL0
  finiteWeights := hfin
  irreducible :=
    djLU_isIrreducible Pr U.toAmModZero hU hval hL0 (isSimpleAmMod_toAmModZero hsimple)
  bottomEquiv := djLU_bottomAModEquiv Pr U hU hval hL0 hfin

include Pr hU hL0 hfin in
/-- **`U` lands in the faithful codomain `IrrAMod W`** — i.e. `L(U)` witnesses `IsBottomOfIrr U`. -/
theorem djLU_isBottomOfIrr (hsimple : IsSimpleAMod U) : IsBottomOfIrr U :=
  isBottomOfIrr_of_irrRealization (djIrrRealization Pr U hU hval hL0 hfin hsimple)

end DJ

end VOA
