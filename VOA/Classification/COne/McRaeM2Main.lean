import VOA.Classification.COne.McRaeM2DoubleDual
import VOA.Classification.COne.McRaeM2Exact

/-!
# McRae's route: `UnimodularSocleFact` from `P_S ≅ (P_{S'})'`

* `isSimple_contra` — the contragredient of a simple module is simple (annihilator anti-iso);
* `CoverDualLitFact hC2` — named `Prop` (NOT proved, NOT an axiom), the literature statement used
  by McRae (Prop 5.14, from ENO Prop 4.5 / EGNO §6.4–6.5 in a factorizable finite ribbon category):
  for every simple `S` with Huang cover `P_S`, some Huang cover `P_{S'}` of `S' = contra S`
  satisfies `(P_{S'})' ≅ P_S`;
* `coverDualFact_of_lit` and `unimodularSocleFact_of_coverDualLit (hC2) (h)`;
* `admissiblyRational_of_coverDualLit (hC2) (hss) (h)` and the `A₄` instance
  `cubicModel_admissiblyRational_of_coverDualLit`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.OrbMcRae VOA.Classification.COne.McRaeM1
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V}

/-- The contragredient of a simple generalized-eigenspace-graded module is simple. -/
theorem isSimple_contra (N : GWModule W M) (hN : IsGenGraded N)
    (hS : IsSimpleModule (modeAlg N.toWeakModule) M) :
    IsSimpleModule (modeAlg (contra N).toWeakModule) (RestrictedDual N) := by
  haveI : IsSimpleOrder (Submodule (modeAlg N.toWeakModule) M) := hS.toIsSimpleOrder
  have h : IsSimpleOrder (Submodule (modeAlg (Dm N).toWeakModule) (RestrictedDual N))ᵒᵈ :=
    (perpIsoGen N hN).symm.isSimpleOrder
  haveI := isSimpleOrder_iff_isSimpleOrder_orderDual.mpr h
  exact {}

/-- A simple module has finite length. -/
theorem finiteLength_of_simple {X : Type u} [AddCommGroup X] [Module ℂ X] {B : WeakModule W X}
    (hB : IsSimpleModule (modeAlg B) X) : IsFiniteLength (modeAlg B) X := by
  haveI := hB
  haveI : IsSimpleModule (modeAlg B) (X ⧸ (⊥ : Submodule (modeAlg B) X)) :=
    IsSimpleModule.congr (Submodule.quotEquivOfEqBot ⊥ rfl)
  exact .of_simple_quotient (N := ⊥) .of_subsingleton

/-- **Unimodularity, literature form** (McRae Prop 5.14 input: `P'_{W'} ≅ P_W`, from ENO
Prop 4.5 and EGNO §§6.4–6.5 for the factorizable category of McRae Thm 5.3).  Named `Prop`; NOT
proved, NOT an axiom. -/
def CoverDualLitFact (hC2 : C2Cofinite W) : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X)
    (hB : IsSimpleModule (modeAlg B) X), ∀ C : HuangCover B,
    ∃ D : HuangCover (contra (gwOfFiniteLength hC2 B (finiteLength_of_simple hB))).toWeakModule,
      ∃ e : (contra (gwOfFiniteLength hC2 D.BP D.finiteLength)).toWeakModule.Hom C.BP,
        Function.Bijective e.toLinearMap

/-- The literature form of unimodularity gives the module form used by the socle argument
(double dual `S ≅ S''`, simplicity of `S'`). -/
theorem coverDualFact_of_lit (hC2 : C2Cofinite W) (h : CoverDualLitFact hC2) :
    CoverDualFact W := by
  intro X _ _ B hB C
  obtain ⟨D, e, he⟩ := h B hB C
  let Sg := gwOfFiniteLength hC2 B (finiteLength_of_simple hB)
  have hSg : IsGenGraded Sg := isGenGraded_gwOfFiniteLength hC2 B _
  exact ⟨D.P, RestrictedDual Sg, _, _, _, _, gwOfFiniteLength hC2 D.BP D.finiteLength, contra Sg,
    isGenGraded_gwOfFiniteLength hC2 D.BP D.finiteLength, isGenGraded_contra Sg hSg, D.p, D.surj,
    D.superfluous, isSimple_contra Sg hSg hB, e, he, iotaHom Sg, iota_bijective Sg⟩

/-- **McRae Prop 5.14, formalized**: `C₂` + literature unimodularity ⟹ unimodular socle. -/
theorem unimodularSocleFact_of_coverDualLit (hC2 : C2Cofinite W) (h : CoverDualLitFact hC2) :
    UnimodularSocleFact W :=
  unimodularSocleFact_of_coverDual (coverDualFact_of_lit hC2 h)

/-- Rationality from `C₂`, semisimple Zhu algebra, and literature unimodularity. -/
theorem admissiblyRational_of_coverDualLit (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) (h : CoverDualLitFact hC2) :
    AdmissiblyRational W :=
  admissiblyRational_of_unimodularSocle hC2 hss (unimodularSocleFact_of_coverDualLit hC2 h)

/-- **B3 for `A₄`** from literature unimodularity of its module category. -/
theorem cubicModel_admissiblyRational_of_coverDualLit
    (h : CoverDualLitFact OrbTop.cubicModel_stronglyFinite.c2Cofinite) :
    AdmissiblyRational OrbRat2.cubicModel :=
  admissiblyRational_of_coverDualLit _ OrbTop.cubicModel_zhuSemisimple h

/-- Conversely, rationality gives literature unimodularity: the reduction loses nothing for the
exceptional orbifolds (`C₂` + semisimple Zhu algebra). -/
theorem coverDualLit_iff_admissiblyRational (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) :
    CoverDualLitFact hC2 ↔ AdmissiblyRational W := by
  refine ⟨admissiblyRational_of_coverDualLit hC2 hss, fun hR => ?_⟩
  intro X _ _ B hB C
  -- under rationality every Huang cover is an isomorphism
  have hiso : ∀ {Y : Type u} [AddCommGroup Y] [Module ℂ Y] {B' : WeakModule W Y}
      (C' : HuangCover B'), Function.Bijective C'.p.toLinearMap := by
    intro Y _ _ B' C'
    haveI := McRaeM2.isSemisimple_of_admissiblyRational hC2 hss hR C'.BP
    obtain ⟨Q, hQ⟩ := exists_isCompl (modeComap C'.p ⊥)
    exact ⟨McRaeM2.injective_of_superfluous_compl C'.p C'.superfluous C'.surj hQ, C'.surj⟩
  let Sg := gwOfFiniteLength hC2 B (finiteLength_of_simple hB)
  have hSg : IsGenGraded Sg := isGenGraded_gwOfFiniteLength hC2 B _
  let T := contra Sg
  have hT : IsGenGraded T := isGenGraded_contra Sg hSg
  obtain ⟨D⟩ := huangCoverFact_of_c2 hC2 T.toWeakModule (isSimple_contra Sg hSg hB)
  let G := gwOfFiniteLength hC2 D.BP D.finiteLength
  have hG : IsGenGraded G := isGenGraded_gwOfFiniteLength hC2 D.BP D.finiteLength
  let dinv : T.toWeakModule.Hom G.toWeakModule := homInv D.p (hiso D)
  have hdinv : Function.Bijective dinv.toLinearMap :=
    (LinearEquiv.ofBijective D.p.toLinearMap (hiso D)).symm.bijective
  have hgr := gradedHom_of_isGenGraded T G dinv hT hG
  let tr := transpose T G dinv hgr
  have htr : Function.Bijective tr.toLinearMap :=
    ⟨transpose_injective_of_surjective T G dinv hgr hdinv.2,
      transpose_surjective_of_injective T G dinv hgr hdinv.1⟩
  let iinv : (contra T).toWeakModule.Hom Sg.toWeakModule := homInv (iotaHom Sg) (iota_bijective Sg)
  have hiinv : Function.Bijective iinv.toLinearMap :=
    (LinearEquiv.ofBijective (iota Sg) (iota_bijective Sg)).symm.bijective
  let cinv : B.Hom C.BP := homInv C.p (hiso C)
  have hcinv : Function.Bijective cinv.toLinearMap :=
    (LinearEquiv.ofBijective C.p.toLinearMap (hiso C)).symm.bijective
  refine ⟨D, homComp cinv (homComp iinv tr), ?_⟩
  exact hcinv.comp (hiinv.comp htr)

end VOA.C2Rigid
