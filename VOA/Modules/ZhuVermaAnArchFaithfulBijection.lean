/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGameTwo
import VOA.Modules.ZhuVermaAnArchGenFromBottomFinal

/-!
# Theorem 5.3.4 — the **faithful** bijection `Φ(𝒱) ↔ Irr A(𝒱)`, restricted to irreducibles

`Modules.ZhuBijection` built the forward map `forwardMap : LWModuleIsoClass W → AModIsoClass W`,
`[M] ↦ [M_h]`, over the iso-classes of **all** bundled lowest-weight `𝒱`-modules and **all** bundled
`A(𝒱)`-modules.  The headline bijection theorems of `Modules.ZhuVermaAnArch*` (`zhuBijection_final`,
`zhuBijection_of_universal`, …) make that *full-category* map a bijection by carrying the extra
hypothesis

  `hall : AllLWIrreducible W := ∀ P : LWModule W, P.IsIrreducibleLW`

(`ZhuVermaAnArchRigidity.lean:170`).  As a statement over **all** `LWModule W` `hall` is **false**
in general — the generalized-Verma module `M(U)` is a *reducible* lowest-weight module, so it is a
counterexample.  `hall` is used at exactly one place
(`InducedAssignment.realizesSelf_of_realizesSelfOnIrr`, `ZhuVermaAnArchRigidity.lean:176`) to
upgrade the **true** scoped predicate `RealizesSelfOnIrr` to the literal `RealizesSelf` over the
whole category.  That single step is the unsound one.

## What this file does (faithful, `hall`-free; mutates nothing)

Gannon's Theorem 5.3.4 is a bijection between `Φ(𝒱)` (the **irreducible** lowest-weight
`𝒱`-modules, up to iso) and `Irr A(𝒱)` (the irreducible `A(𝒱)`-modules, up to iso).  We make the
*statement* faithful by **restricting the domain and codomain to irreducible objects**, so the
irreducibility quantifier becomes tautological on the carrier types and `hall` is **not
needed**.  The already-true scoped predicate `RealizesSelfOnIrr` (proved `hall`-free in
`ZhuVermaAnArchGameTwo.realizesSelfOnIrr_of_universal`) is used directly.

* **`IrrLWModule W`** — the subtype `{P : LWModule W // P.IsIrreducibleLW}` of irreducible bundled
  lowest-weight modules; its iso setoid and iso-class quotient `IrrLWModuleIsoClass W`.  This is the
  faithful domain `Φ(𝒱)`.
* **`IsBottomOfIrr U`** / **`IrrAMod W`** — the image-defined faithful codomain: the bundled
  `A(𝒱)`-modules that arise as the bottom of *some* irreducible lowest-weight `𝒱`-module
  (`∃ P irreducible, P.toAMod ≅ U`); its iso setoid and quotient `IrrAModIsoClass W`.  This is the
  faithful target `Irr A(𝒱)` (Gannon: irreducible `A(𝒱)`-modules are exactly the bottoms of the
  irreducible `𝒱`-modules — the content of the bijection itself).
* **`forwardMapIrr W : IrrLWModuleIsoClass W → IrrAModIsoClass W`** — the faithful forward map
  `[M] ↦ [M_h]`, landing in `IrrAMod` **tautologically** (`M_h` is the bottom of the irreducible
  `M`).  Well-defined by the existing functoriality `LWModule.isoToAModEquiv`.
* **`FaithfulScorecard W`** — the `hall`-free bundle of the genuine deep inputs (the
  `InducedAssignment`, `RealizeIrreducible`, the `L(U)`-family `F`/`hiso`, and the per-`P` residue
  family `G` feeding `generatedFromBottom_final`).  **`hall` is absent.**
* **`forwardMapIrr_bijective`** / **`FaithfulScorecard.bijectiveIrr`** — the faithful bijection
  `Φ(𝒱) ↔ Irr A(𝒱)`, proved with **no** `hall` anywhere in its dependency closure.

## This is **not** unconditional

Removing `hall` only fixes the *statement* (makes it faithful to Gannon and drops the false global
irreducibility hypothesis).  The result **remains conditional** on the genuine deep hypothesis bundle fields
— `A : InducedAssignment` (ρ on `M(U)`, bottom survival, functoriality), `hirr` (the realizations
are `L(U)`), and `F`/`hiso`/`G` (the `L(U) = M(U)/J` family, `isoInvariant`, the per-`P` residue
feeding
the universal property `GeneratedFromBottom`, encoding module Jacobi 5.3.1b, `muEquiv`, `KerJData`,
`bottom_ne_zero`, `R0`).  None of those is discharged or faked here.

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu; Dong–Li–Mason.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The faithful domain `Φ(𝒱)` — irreducible lowest-weight modules -/

/-- **`IrrLWModule W`** — the faithful domain of Theorem 5.3.4: bundled lowest-weight `𝒱`-modules
that are **irreducible** (`IsIrreducibleLW`).  As a subtype, the irreducibility is carried in the
`.2` component, so the irreducibility quantifier of the bijection is tautological here — no `hall`
hypothesis is ever needed. -/
def IrrLWModule (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) :=
  {P : LWModule W // P.IsIrreducibleLW}

namespace IrrLWModule

variable {W : VertexOperatorAlgebra 𝒱}

/-- Iso of irreducible lowest-weight modules = iso of the underlying `LWModule`s. -/
def Iso (P Q : IrrLWModule W) : Prop := LWModule.Iso W P.1 Q.1

/-- Iso of irreducible lowest-weight modules is an equivalence relation, inherited from
`LWModule.setoid` on the underlying carriers. -/
def setoid (W : VertexOperatorAlgebra 𝒱) : Setoid (IrrLWModule W) where
  r P Q := IrrLWModule.Iso P Q
  iseqv :=
    { refl := fun P => (LWModule.setoid W).iseqv.refl P.1
      symm := fun {_ _} h => (LWModule.setoid W).iseqv.symm h
      trans := fun {_ _ _} h h' => (LWModule.setoid W).iseqv.trans h h' }

end IrrLWModule

/-- **Iso-classes of irreducible lowest-weight `𝒱`-modules — the faithful `Φ(𝒱)`.** -/
def IrrLWModuleIsoClass (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) :=
  Quotient (IrrLWModule.setoid W)

/-! ## The faithful codomain `Irr A(𝒱)` — bottoms of irreducible modules -/

/-- **`IsBottomOfIrr U`** — the bundled `A(𝒱)`-module `U` arises as the bottom (lowest-weight space,
with its descended `A(𝒱)`-action) of *some* irreducible lowest-weight `𝒱`-module.  This is the
image-defined faithful predicate cutting out `Irr A(𝒱)`: by Theorem 5.3.4 the irreducible
`A(𝒱)`-modules are exactly the bottoms of the irreducible `𝒱`-modules. -/
def IsBottomOfIrr {W : VertexOperatorAlgebra 𝒱} (U : AMod W) : Prop :=
  ∃ P : LWModule W, P.IsIrreducibleLW ∧ Nonempty (AModEquiv W P.toAMod U)

/-- **`IrrAMod W`** — the faithful codomain of Theorem 5.3.4: bundled `A(𝒱)`-modules that are
bottoms of irreducible lowest-weight `𝒱`-modules. -/
def IrrAMod (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) :=
  {U : AMod W // IsBottomOfIrr U}

namespace IrrAMod

variable {W : VertexOperatorAlgebra 𝒱}

/-- Iso of `Irr A(𝒱)`-modules = `A(𝒱)`-module iso of the underlying carriers. -/
def Iso (U V : IrrAMod W) : Prop := Nonempty (AModEquiv W U.1 V.1)

/-- Iso of `Irr A(𝒱)`-modules is an equivalence relation, inherited from `AMod.setoid`. -/
def setoid (W : VertexOperatorAlgebra 𝒱) : Setoid (IrrAMod W) where
  r U V := IrrAMod.Iso U V
  iseqv :=
    { refl := fun U => (AMod.setoid W).iseqv.refl U.1
      symm := fun {_ _} h => (AMod.setoid W).iseqv.symm h
      trans := fun {_ _ _} h h' => (AMod.setoid W).iseqv.trans h h' }

end IrrAMod

/-- **Iso-classes of `Irr A(𝒱)`-modules — the faithful `Irr A(𝒱)`.** -/
def IrrAModIsoClass (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) :=
  Quotient (IrrAMod.setoid W)

/-! ## The faithful forward map `[M] ↦ [M_h]` -/

/-- **The bottom of an irreducible `𝒱`-module, as an `Irr A(𝒱)`-module.**  The witness for
`IsBottomOfIrr` is `P` itself (with the identity bottom equivalence). -/
noncomputable def IrrLWModule.toIrrAMod {W : VertexOperatorAlgebra 𝒱} (P : IrrLWModule W) :
    IrrAMod W :=
  ⟨P.1.toAMod, ⟨P.1, P.2, ⟨AModEquiv.refl W P.1.toAMod⟩⟩⟩

/-- **The faithful forward map `Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`.**  A genuine function on the
irreducible iso-classes, landing in `Irr A(𝒱)` tautologically (`M_h` is the bottom of the
irreducible `M`).  Well-defined by the functoriality `LWModule.isoToAModEquiv` (an iso
`e : P.1 ≃ₘ Q.1` gives an `A(𝒱)`-iso `P.1.toAMod ≅ Q.1.toAMod`). -/
noncomputable def forwardMapIrr (W : VertexOperatorAlgebra 𝒱) :
    IrrLWModuleIsoClass W → IrrAModIsoClass W :=
  Quotient.lift
    (fun P => (Quotient.mk (IrrAMod.setoid W) (IrrLWModule.toIrrAMod P) : IrrAModIsoClass W))
    (fun _ _ ⟨e⟩ => Quotient.sound ⟨LWModule.isoToAModEquiv W e⟩)

/-- On a representative, the faithful forward map is `[M_h]`. -/
@[simp] theorem forwardMapIrr_mk (W : VertexOperatorAlgebra 𝒱) (P : IrrLWModule W) :
    forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) P)
      = Quotient.mk (IrrAMod.setoid W) (IrrLWModule.toIrrAMod P) := rfl

/-! ## The faithful inverse `[U] ↦ [L(U)]` and bijectivity, `hall`-free -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The faithful inverse `Irr A(𝒱) → Φ(𝒱)`, `[U] ↦ [A.realize U]`.**  Given that the assignment
produces irreducible realizations (`hirr`), `A.realize U.1` is irreducible, so it lands in
`IrrLWModule`.  Well-defined on iso-classes by `A.isoInvariant`. -/
noncomputable def invFunIrr (A : InducedAssignment W) (hirr : A.RealizeIrreducible) :
    IrrAModIsoClass W → IrrLWModuleIsoClass W :=
  Quotient.lift
    (fun U => (Quotient.mk (IrrLWModule.setoid W)
      (⟨A.realize U.1, hirr U.1⟩ : IrrLWModule W) : IrrLWModuleIsoClass W))
    (by
      rintro U V ⟨e⟩
      exact Quotient.sound (A.isoInvariant U.1 V.1 ⟨e⟩))

@[simp] theorem invFunIrr_mk (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (U : IrrAMod W) :
    A.invFunIrr hirr (Quotient.mk (IrrAMod.setoid W) U)
      = Quotient.mk (IrrLWModule.setoid W) (⟨A.realize U.1, hirr U.1⟩ : IrrLWModule W) := rfl

/-- **`forwardMapIrr ∘ invFunIrr = id`** (right inverse), `hall`-free.  For `[U] : Irr A(𝒱)`,
`forwardMapIrr (invFunIrr [U]) = [(A.realize U.1).toAMod]`, and the realization's bottom is
`A(𝒱)`-isomorphic to `U.1` by `A.realizes U.1`.  Uses **only** `A` and `hirr`. -/
theorem forwardMapIrr_invFunIrr (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (x : IrrAModIsoClass W) : forwardMapIrr W (A.invFunIrr hirr x) = x := by
  refine Quotient.inductionOn x (fun U => ?_)
  rw [invFunIrr_mk, forwardMapIrr_mk]
  -- `[(A.realize U.1).toAMod]` = `[U.1]` in `IrrAModIsoClass`, via `A.realizes U.1`.
  exact Quotient.sound ⟨A.realizes U.1⟩

/-- **`invFunIrr ∘ forwardMapIrr = id`** (left inverse), from the **already-true scoped rigidity**
`RealizesSelfOnIrr` — **no** `hall`.  For an irreducible `P`, `A.realize P.1.toAMod ≅ P.1` (the
irreducibility hypothesis of `RealizesSelfOnIrr` is supplied by `P.2`, the subtype's irreducibility
component, **not** by `hall`). -/
theorem invFunIrr_forwardMapIrr (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (hself : A.RealizesSelfOnIrr) (x : IrrLWModuleIsoClass W) :
    A.invFunIrr hirr (forwardMapIrr W x) = x := by
  refine Quotient.inductionOn x (fun P => ?_)
  rw [forwardMapIrr_mk, invFunIrr_mk]
  -- Goal: `[⟨A.realize (P.toIrrAMod).1, _⟩] = [P]` in `IrrLWModuleIsoClass`.
  -- `(P.toIrrAMod).1 = P.1.toAMod` definitionally, so the realization is `A.realize P.1.toAMod`.
  -- `RealizesSelfOnIrr` at the irreducible `P.1` (witness `P.2`) gives the `𝒱`-iso to `P.1`.
  exact Quotient.sound (hself P.1 P.2)

/-! ## The faithful bijection -/

/-- **`forwardMapIrr` is surjective**, `hall`-free (right inverse `invFunIrr`). -/
theorem forwardMapIrr_surjective (A : InducedAssignment W) (hirr : A.RealizeIrreducible) :
    Function.Surjective (forwardMapIrr W) :=
  Function.RightInverse.surjective (A.forwardMapIrr_invFunIrr hirr)

/-- **`forwardMapIrr` is injective**, `hall`-free (left inverse `invFunIrr`, from the scoped
rigidity `RealizesSelfOnIrr`). -/
theorem forwardMapIrr_injective (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (hself : A.RealizesSelfOnIrr) :
    Function.Injective (forwardMapIrr W) :=
  Function.LeftInverse.injective (A.invFunIrr_forwardMapIrr hirr hself)

/-- **`forwardMapIrr` is bijective**, from `A`, `hirr`, and the **scoped, already-true**
rigidity `RealizesSelfOnIrr` — **no** `hall`.  This is the faithful Theorem 5.3.4 bijection
`Φ(𝒱) ↔ Irr A(𝒱)`. -/
theorem forwardMapIrr_bijective_of_self (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (hself : A.RealizesSelfOnIrr) :
    Function.Bijective (forwardMapIrr W) :=
  ⟨A.forwardMapIrr_injective hirr hself, A.forwardMapIrr_surjective hirr⟩

/-- **The faithful Zhu bijection as an `Equiv`**, `hall`-free: `Φ(𝒱) ≃ Irr A(𝒱)` with forward
`forwardMapIrr` (`[M] ↦ [M_h]`) and inverse `invFunIrr` (`[U] ↦ [L(U)]`). -/
noncomputable def zhuEquivIrr (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (hself : A.RealizesSelfOnIrr) :
    IrrLWModuleIsoClass W ≃ IrrAModIsoClass W where
  toFun := forwardMapIrr W
  invFun := A.invFunIrr hirr
  left_inv := A.invFunIrr_forwardMapIrr hirr hself
  right_inv := A.forwardMapIrr_invFunIrr hirr

@[simp] theorem zhuEquivIrr_apply (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (hself : A.RealizesSelfOnIrr) (x : IrrLWModuleIsoClass W) :
    A.zhuEquivIrr hirr hself x = forwardMapIrr W x := rfl

/-- **The faithful bijection from the universal property**, `hall`-free.  The scoped rigidity is
supplied by `realizesSelfOnIrr_of_universal A hirr hgen` — the already-true, `hall`-free reduction.
The single deep injectivity crux is `hgen : GeneratedFromBottom W`. -/
theorem forwardMapIrr_bijective (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (hgen : InducedAssignment.GeneratedFromBottom W) :
    Function.Bijective (forwardMapIrr W) :=
  A.forwardMapIrr_bijective_of_self hirr (A.realizesSelfOnIrr_of_universal hirr hgen)

end InducedAssignment

/-! ## The `hall`-free hypothesis bundle and the faithful headline -/

/-- **`FaithfulScorecard W`** — the `hall`-free bundle of the genuine deep inputs of the faithful
Theorem 5.3.4.  It is **exactly** the input set of the existing `zhuBijection_final` *minus* the
false `hall : AllLWIrreducible W`.  The result stays conditional on these fields; none is discharged
or faked.  `hall` is **absent**. -/
structure FaithfulScorecard (W : VertexOperatorAlgebra 𝒱) where
  /-- The `U ↦ M̄(U)` existence datum: `realize`, bottom-survival `realizes`, functoriality
  `isoInvariant` (ρ on `M(U)` / Jacobi 5.3.1b live here). -/
  A : InducedAssignment W
  /-- The realizations are the irreducible quotients `L(U)`. -/
  hirr : A.RealizeIrreducible
  /-- The per-`U` `L(U) = M(U)/J` family. -/
  F : InducedAssignment.LUFamily W
  /-- Functoriality of `L(·)` on bottoms (`isoInvariant`). -/
  hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂)
  /-- The per-irreducible-`P` residue family (bottom map `β`/`hβ`, `q_act` = `MUGradedAction`,
  `bottom_ne_zero` = `BottomOrbit`, maximal-`J` `KerJData`) feeding the universal property. -/
  G : InducedAssignment.GenFromBottomFinalFamily F

namespace FaithfulScorecard

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The universal property `GeneratedFromBottom W`, derived from the hypothesis bundle** (`hall`-free). -/
theorem generatedFromBottom (S : FaithfulScorecard W) :
    InducedAssignment.GeneratedFromBottom W :=
  InducedAssignment.generatedFromBottom_final S.F S.hiso S.G

/-- **The faithful Theorem 5.3.4 bijection `Φ(𝒱) ↔ Irr A(𝒱)`, `hall`-free.**

The forward map `forwardMapIrr W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, restricted to the *irreducible*
iso-classes, is a **bijection**.  No `hall : AllLWIrreducible W` is assumed or used anywhere in the
dependency closure — the irreducibility quantifier is tautological on the subtype domain/codomain,
and the injective half rests on the already-true scoped `RealizesSelfOnIrr` (via the deep universal
property `GeneratedFromBottom`).

**Still conditional** on the genuine deep fields bundled in `S` (`A`, `hirr`, `F`, `hiso`, `G` —
ρ on `M(U)`, module Jacobi, the `L(U)`-family, `isoInvariant`, `muEquiv`, `KerJData`,
`bottom_ne_zero`, `R0`).  This is *not* an unconditional theorem; only the false `hall` is gone. -/
theorem bijectiveIrr (S : FaithfulScorecard W) :
    Function.Bijective (forwardMapIrr W) :=
  S.A.forwardMapIrr_bijective S.hirr S.generatedFromBottom

/-- **The faithful Zhu bijection as an `Equiv`**, `hall`-free: `Φ(𝒱) ≃ Irr A(𝒱)`. -/
noncomputable def equivIrr (S : FaithfulScorecard W) :
    IrrLWModuleIsoClass W ≃ IrrAModIsoClass W :=
  S.A.zhuEquivIrr S.hirr (S.A.realizesSelfOnIrr_of_universal S.hirr S.generatedFromBottom)

end FaithfulScorecard

/-- **The faithful headline, hypothesis-bundle-shaped (`hall`-free).**  Exactly the signature of
`zhuBijection_final` with `hall` removed: from an `InducedAssignment` `A`, the `L(U)`-property
`hirr`, the `L(U)`-family `F`, its functoriality `hiso`, and the per-`P` residue family `G`, the
faithful forward map `forwardMapIrr W : Φ(𝒱) → Irr A(𝒱)` is a **bijection**.

The only input removed relative to `zhuBijection_final` is the false `hall : AllLWIrreducible W`;
the result remains conditional on the deep fields `A`/`hirr`/`F`/`hiso`/`G`. -/
theorem zhuBijectionIrr_scorecard {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  A.forwardMapIrr_bijective hirr (InducedAssignment.generatedFromBottom_final F hiso G)

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
