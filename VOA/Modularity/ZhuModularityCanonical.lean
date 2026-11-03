/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.GNProp8PBW
import VOA.Modularity.ZhuStronglyRational
import VOA.Modularity.LowestWeightExistence
import VOA.Classification.COne.McRaeO1FinitePhi
import VOA.Examples.ZhuInstantiation
import VOA.Examples.TrivialRationalityLattice
import VOA.Huang.ZhuSemisimple
import VOA.Modules.StronglyRational

/-!
# Zhu modularity for the canonical family, and the combined Zhu correspondence

This leaf states two forms of the main theorem with every dischargeable hypothesis discharged.

* `zhuModularity_canonical_of_C2Cofinite_semisimple`: **pinned Zhu modularity for one-point
  functions**, for the canonical family `canonicalIrrModule : Φ W → IrrModule W` (one chosen
  representative of each isomorphism class of irreducible ordinary modules, each with its own
  conformal weight).  The only hypotheses are
  - `C2Cofinite W`, and
  - `IsSemisimpleRing (A W)` (semisimplicity of the Zhu algebra).

  The implication "rational ⟹ `A(V)` semisimple" **is** formalized for the library's rationality
  predicate `AdmissiblyRational` (every admissible module completely reducible):
  `VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational`, with its PBW datum supplied
  by `VOA.pbw`.  Hence the corollaries `zhuModularity_canonical_of_C2Cofinite_admissiblyRational`
  and `zhuModularity_canonical_of_stronglyRational` below.  What remains unsettled is only the
  relation of `AdmissiblyRational` to other formulations of rationality in the literature (e.g.
  Dong–Li–Mason's, stated with their own module conventions); on paper every rational
  `C₂`-cofinite VOA satisfies the hypotheses (Zhu; Dong–Li–Mason).  CFT type is built into
  `VertexOperatorAlgebra` (`vacuum_grade`, `positivity`).  The conclusion `ZhuModularityAnalytic`
  concerns one-point functions `tr_M o(v) q^{L₀ − c/24}` only, not `n`-point functions.
  Finiteness of `Φ W` is not assumed: it is supplied by
  `VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw`.

* `trivialVOA_zhuModularity_closed`: the same, closed at the trivial VOA `ℂ𝟙`, with no
  hypotheses at all.

* `zhuCorrespondence_of_C2Cofinite`: **Zhu's correspondence as one bijection** for `C₂`-cofinite
  `W`: isomorphism classes `Φ W` of irreducible ordinary `W`-modules are in bijection with
  isomorphism classes of *simple* `A(W)`-modules (`SimpleAModIsoClass W`, defined here by the
  intrinsic predicate `IsSimpleAMod`, not by an image), the bijection sending `[M]` to the class of
  its bottom `M_h`.  Injectivity is `zhuBijective_of_voaPBW` (no `C₂`); bottoms of irreducibles
  are simple by `allBottomRecovers` (no `C₂`); every simple `A(W)`-module is realized by
  `simpleAModsRealized_of_C2Cofinite` (this is where `C₂` is used — Zhu's own existence theorem
  does not need it).

All three rest on the project's PBW theorem `VOA.pbw` through `voaPBWBottomProjection`.
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Canonical-family Zhu modularity -/

/-- **Zhu's modularity theorem for one-point functions, canonical family.**  For a
`C₂`-cofinite VOA (of CFT type, built into `VertexOperatorAlgebra`) whose Zhu algebra is
semisimple, the one-point functions of the canonical representatives of the irreducible ordinary
modules, with their conformal weights, form a `ModularData` satisfying `ZhuModularityAnalytic`:
they transform under `SL₂(ℤ)` by a genuine matrix representation with diagonal `ρ(T)`.
No finiteness, family, cardinality or separation hypothesis is assumed. -/
theorem zhuModularity_canonical_of_C2Cofinite_semisimple (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    letI : Finite (Φ W) := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw hC2
    letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
    letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
    ∃ D : ModularData W (Φ W), D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧ ZhuModularityAnalytic D := by
  classical
  letI : Finite (Φ W) := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw hC2
  letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
  letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
  exact zhuModularity_pinned_of_C2Cofinite_voaPBW (canonicalIrrModule (W := W))
    (fun c => conformalWeightOf (canonicalIrrModule c)) hC2 hss canonicalIrrFamily_card
    canonicalIrrFamily_hasConformalWeight
    (fun _ _ hjk hw => canonicalIrrFamily_bottomSeparated hjk hw)

/-- **Zhu modularity, canonical family, from `C₂`-cofiniteness and rationality.**
`AdmissiblyRational W` gives `IsSemisimpleRing (A W)` by
`VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational` (Zhu / Dong–Li–Mason), whose
PBW datum is supplied by `VOA.pbw`. -/
theorem zhuModularity_canonical_of_C2Cofinite_admissiblyRational (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) (hrat : AdmissiblyRational W) :
    letI : Finite (Φ W) := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw hC2
    letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
    letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
    ∃ D : ModularData W (Φ W), D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧ ZhuModularityAnalytic D :=
  zhuModularity_canonical_of_C2Cofinite_semisimple W hC2
    (VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational
      (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hrat)

/-- **Zhu modularity, canonical family, for every strongly rational VOA** (simple,
self-dual, `C₂`-cofinite, `AdmissiblyRational`).  Unlike `zhuModularity_stronglyRational_voaPBW`,
no Dong–Li–Mason finiteness or Zhu-semisimplicity input is assumed. -/
theorem zhuModularity_canonical_of_stronglyRational (W : VertexOperatorAlgebra 𝒱)
    (hSR : StronglyRational W) :
    letI : Finite (Φ W) := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw hSR.c2Cofinite
    letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
    letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
    ∃ D : ModularData W (Φ W), D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧ ZhuModularityAnalytic D :=
  zhuModularity_canonical_of_C2Cofinite_admissiblyRational W hSR.c2Cofinite hSR.rational

/-- **Zhu modularity at the trivial VOA `ℂ𝟙`, with every hypothesis discharged.**  The modular
content is trivial (`c = 0`, one module, character `1`); this is a non-vacuity check of the
hypotheses only. -/
theorem trivialVOA_zhuModularity_closed :
    ∃ D : ModularData trivialVOA (Fin 1),
      D.Mfam = (fun _ => trivialAdjointIrr) ∧ D.h = (fun _ => 0) ∧ ZhuModularityAnalytic D := by
  haveI : Finite (Φ trivialVOA) :=
    VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw trivial_C2Cofinite
  exact trivialVOA_zhuModularity trivial_card_Φ

/-! ## The combined Zhu correspondence -/

/-- Bundled `A(W)`-modules that are **simple** in the intrinsic sense `IsSimpleAMod`
(nonzero, no `A(W)`-submodules other than `⊥`, `⊤`). -/
def SimpleAMod (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) :=
  {U : AMod W // IsSimpleAMod U}

/-- `A(W)`-module isomorphism on simple `A(W)`-modules. -/
def SimpleAMod.setoid (W : VertexOperatorAlgebra 𝒱) : Setoid (SimpleAMod W) where
  r U V := Nonempty (AModEquiv W U.1 V.1)
  iseqv :=
    { refl := fun U => (AMod.setoid W).iseqv.refl U.1
      symm := fun {_ _} h => (AMod.setoid W).iseqv.symm h
      trans := fun {_ _ _} h h' => (AMod.setoid W).iseqv.trans h h' }

/-- Isomorphism classes of simple `A(W)`-modules. -/
def SimpleAModIsoClass (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) :=
  Quotient (SimpleAMod.setoid W)

/-- The bottom of an irreducible lowest-weight module, as a simple `A(W)`-module (simplicity is
`allBottomRecovers`, valid for every VOA). -/
noncomputable def IrrLWModule.toSimpleAMod {W : VertexOperatorAlgebra 𝒱} (P : IrrLWModule W) :
    SimpleAMod W :=
  ⟨P.1.toAMod,
    (IrrLWModule.toIrrAMod P).2.isSimpleAMod (VOA.Huang.LWBottomRecovery.allBottomRecovers W)⟩

/-- **Zhu's correspondence (Zhu Thm 5.3.4 / Gannon Thm 5.3.4) as a single bijection, for
`C₂`-cofinite `W`.**  There is an equivalence between `Φ W` (isomorphism classes of irreducible
ordinary `W`-modules) and isomorphism classes of simple `A(W)`-modules which sends the class of
every irreducible lowest-weight module `P` to the class of its bottom `P_h`. -/
theorem zhuCorrespondence_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ e : Φ W ≃ SimpleAModIsoClass W, ∀ P : IrrLWModule W,
      e (forgetClass W (Quotient.mk (IrrLWModule.setoid W) P)) =
        Quotient.mk (SimpleAMod.setoid W) (IrrLWModule.toSimpleAMod P) := by
  have hiff : ∀ U : AMod W, IsBottomOfIrr U ↔ IsSimpleAMod U :=
    isBottomOfIrr_iff_isSimpleAMod (VOA.Huang.LWBottomRecovery.allBottomRecovers W)
      (simpleAModsRealized_of_C2Cofinite hC2
        (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))))
  let g : IrrAModIsoClass W ≃ SimpleAModIsoClass W :=
    Quotient.congr (Equiv.subtypeEquivRight hiff) (fun _ _ => Iff.rfl)
  refine ⟨(irrLWModuleIsoClass_equiv_Φ W).symm.trans
    ((Equiv.ofBijective _ (zhuBijective_of_voaPBW W)).trans g), fun P => ?_⟩
  have h1 : (irrLWModuleIsoClass_equiv_Φ W).symm
      (forgetClass W (Quotient.mk (IrrLWModule.setoid W) P)) =
        Quotient.mk (IrrLWModule.setoid W) P := by
    change (irrLWModuleIsoClass_equiv_Φ W).symm
      ((irrLWModuleIsoClass_equiv_Φ W) (Quotient.mk (IrrLWModule.setoid W) P)) = _
    exact (irrLWModuleIsoClass_equiv_Φ W).symm_apply_apply _
  simp only [Equiv.trans_apply, h1, Equiv.ofBijective_apply, forwardMapIrr_mk]
  rfl

end VOA
