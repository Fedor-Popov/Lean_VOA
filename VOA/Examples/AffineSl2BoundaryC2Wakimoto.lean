/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2BoundarySingularFamily
import VOA.Examples.AffineSl2BoundaryFreeFieldPrimitive
import VOA.Examples.AffineSl2WakimotoLiLeading

/-!
# Exact boundary affine C2 presentations from Wakimoto triangularity

This file is a small assembly layer.  The boundary singular-vector package supplies the exact
highest `C₂` symbol and maximal-ideal generation.  Wakimoto triangularity proves the needed
universal affine PBW theorem, hence injectivity of the universal affine symbol map at every
noncritical level.  Combining the two proves the full nonreduced boundary `C₂` presentation.

No classical-freeness or Hilbert-series assertion is used.  The only model-specific input is:

* representation-theoretic boundary singular-vector data;

the polynomial leading-term independence in the Wakimoto realization is a theorem imported
from `AffineSl2WakimotoLiLeading`.
-/

namespace VOA
namespace AffineSl2BoundaryC2Wakimoto

open AffineSl2BoundarySingularFamily
open AffineSl2WakimotoLiLeading

noncomputable section

universe u v w

/-- Exact boundary `C₂` presentation from the uniform singular-vector data.  The universal
symbol-map input is discharged by the proved affine PBW/Wakimoto triangularity theorem. -/
theorem exactPresentation_of_classicalData
    {k : ℂ} {n : ℕ} (D : ClassicalData k n) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal n)
      (AffineSl2BoundaryC2.quotientSymbol k D.noncritical
        (QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed k D.noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  D.exactPresentation

/-- The published Adamovic--Milas maximal-submodule package and an independently established
nonzero highest-symbol formula together imply the exact boundary `C₂` presentation. -/
theorem exactPresentation_of_adamovicMilas
    {k : ℂ} {n : ℕ} (D : AdamovicMilasData k n)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (hsymbol :
      mk₂ (AffineVOA.affineSl2VOA_closed k D.noncritical) D.vector =
        coefficient • Sl2Pres.symbolAlg k D.noncritical
          (QuasiLisseSl2.eSym * QuasiLisseSl2.casSym ^ n)) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal n)
      (AffineSl2BoundaryC2.quotientSymbol k D.noncritical
        (QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed k D.noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  exactPresentation_of_classicalData
    (D.toClassicalData coefficient hcoefficient hsymbol)

/-- The primitive-vector route needs only vacuum-line uniqueness in the singular quotient; the
existence of a primitive vector in every nonzero proper current submodule is proved
internally. -/
theorem exactPresentation_of_primitiveCriterion
    {k : ℂ} {n : ℕ} (D : PrimitiveCriterionData k n)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (hsymbol :
      mk₂ (AffineVOA.affineSl2VOA_closed k D.noncritical) D.vector =
        coefficient • Sl2Pres.symbolAlg k D.noncritical
          (QuasiLisseSl2.eSym * QuasiLisseSl2.casSym ^ n)) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal n)
      (AffineSl2BoundaryC2.quotientSymbol k D.noncritical
        (QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed k D.noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  exactPresentation_of_adamovicMilas D.toAdamovicMilasData
    coefficient hcoefficient hsymbol

/-- At `k=-4/3`, the explicit singular vector already supplies the highest-symbol formula; only
the published maximal-submodule equality remains visible. -/
theorem exactPresentation43_of_maximalGeneration
    (hmax : QuotVOA.maxGradedIdeal
        (AffineVOA.affineSl2VOA_closed (-4 / 3 : ℂ) AffineVOA.Inst.admLevel_noncritical) =
      SingVec.idealGen
        (AffineVOA.affineSl2VOA_closed (-4 / 3 : ℂ) AffineVOA.Inst.admLevel_noncritical)
        Sl2Sing.sl2Singular) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal 1)
      (AffineSl2BoundaryC2.quotientSymbol (-4 / 3 : ℂ) AffineVOA.Inst.admLevel_noncritical
        (QuotVOA.maxGradedIdeal
          (AffineVOA.affineSl2VOA_closed (-4 / 3 : ℂ) AffineVOA.Inst.admLevel_noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  exactPresentation_of_classicalData (classicalData43 hmax)

/-- At `k=-8/5`, the weight-five calculation likewise leaves exactly maximal generation. -/
theorem exactPresentation85_of_maximalGeneration
    (hmax : QuotVOA.maxGradedIdeal
        (AffineVOA.affineSl2VOA_closed (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical) =
      SingVec.idealGen
        (AffineVOA.affineSl2VOA_closed (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical)
        Sl2Sing85.sl2Singular85) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal 2)
      (AffineSl2BoundaryC2.quotientSymbol (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical
        (QuotVOA.maxGradedIdeal
          (AffineVOA.affineSl2VOA_closed (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  exactPresentation_of_classicalData (classicalData85 hmax)

/-- At `k=-4/3`, absence of non-vacuum affine primitives in the singular quotient is the sole
remaining exact-`C₂` representation-theory input. -/
theorem exactPresentation43_of_onlyVacuumAffinePrimitives
    (honly : AffineSl2BoundaryMaximalIdeal.OnlyVacuumAffinePrimitives
      (-4 / 3 : ℂ) AffineVOA.Inst.admLevel_noncritical Sl2Sing.sl2Singular) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal 1)
      (AffineSl2BoundaryC2.quotientSymbol (-4 / 3 : ℂ) AffineVOA.Inst.admLevel_noncritical
        (QuotVOA.maxGradedIdeal
          (AffineVOA.affineSl2VOA_closed (-4 / 3 : ℂ) AffineVOA.Inst.admLevel_noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  exactPresentation_of_classicalData (classicalData43_of_primitiveCriterion honly)

/-- At `k=-8/5`, the same vacuum-line primitive uniqueness statement suffices. -/
theorem exactPresentation85_of_onlyVacuumAffinePrimitives
    (honly : AffineSl2BoundaryMaximalIdeal.OnlyVacuumAffinePrimitives
      (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical Sl2Sing85.sl2Singular85) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal 2)
      (AffineSl2BoundaryC2.quotientSymbol (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical
        (QuotVOA.maxGradedIdeal
          (AffineVOA.affineSl2VOA_closed (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  exactPresentation_of_classicalData (classicalData85_of_primitiveCriterion honly)

/-! ## Uniform free-field character endpoint -/

/-- A source-faithful free-field realization turns a boundary candidate, its classical highest
symbol, and equality of source-quotient and free-field-image characters into the exact
nonreduced boundary `C₂` presentation.  This is uniform in the boundary index; all
model-dependent representation theory is explicit in the hypotheses. -/
theorem exactPresentation_of_freeFieldCharacter
    {k : ℂ} {n : ℕ} {E : Type u} [AddCommGroup E] [Module ℂ E]
    (C : Candidate k n)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (hsymbol :
      mk₂ (AffineVOA.affineSl2VOA_closed k C.noncritical) C.vector =
        coefficient • Sl2Pres.symbolAlg k C.noncritical
          (QuasiLisseSl2.eSym * QuasiLisseSl2.casSym ^ n))
    (R : AffineVOA.VacuumCurrentRealization k E)
    (hs : R.eval C.vector = 0)
    (hker : LinearMap.ker R.eval =
      QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed k C.noncritical))
    (hchar :
      AffineSl2BoundaryFreeFieldPrimitive.SingularQuotientHasFreeFieldImageCharacter
        C.noncritical R C.vector) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal n)
      (AffineSl2BoundaryC2.quotientSymbol k C.noncritical
        (QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed k C.noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) := by
  have hstrict :=
    AffineSl2BoundaryFreeFieldPrimitive.singularIdealIsFreeFieldKernel_of_character
      C.noncritical R hs hchar
  have hmax : QuotVOA.maxGradedIdeal
        (AffineVOA.affineSl2VOA_closed k C.noncritical) =
      SingVec.idealGen (AffineVOA.affineSl2VOA_closed k C.noncritical) C.vector := by
    rw [← hker]
    exact hstrict.symm
  exact exactPresentation_of_classicalData
    { toCandidate := C
      symbolCoefficient := coefficient
      symbolCoefficient_ne_zero := hcoefficient
      highestSymbol := hsymbol
      maximalGeneration := hmax }

/-! ## The `p=5` Adamović character endpoint -/

/-- **Exact `p=5` source endpoint from the Adamović character criterion.**  Proposition 2.1
together with equality of the displayed singular-quotient character and the simple/
screening-kernel character gives the full nonreduced boundary `C₂` presentation.  All
singular-vector, highest-symbol, horizontal-orbit, and universal-PBW inputs are already discharged
above. -/
theorem exactPresentation85_of_freeFieldSimpleCharacter
    {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    {ShiftedVirCarrier : Type v} [AddCommGroup ShiftedVirCarrier]
      [Module ℂ ShiftedVirCarrier]
    {ShiftedPiCarrier : Type w} [AddCommGroup ShiftedPiCarrier]
      [Module ℂ ShiftedPiCarrier]
    (D : InverseDS.HalfLattice.K85Prop21ScreeningData
      VirCarrier ShiftedVirCarrier ShiftedPiCarrier)
    (hchar :
      AffineSl2BoundaryFreeFieldPrimitive.K85.DisplayedSingularQuotientHasSimpleCharacter) :
    Presentation.IsExactPresentation (AffineSl2BoundaryC2.boundaryIdeal 2)
      (AffineSl2BoundaryC2.quotientSymbol (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical
        (QuotVOA.maxGradedIdeal
          (AffineVOA.affineSl2VOA_closed (-8 / 5 : ℂ) Sl2Symbol85.level85_noncritical))
        (QuotVOA.maxGradedIdeal_isIdeal _)
        (QuotVOA.maxGradedIdeal_isGradedIdeal _)) :=
  exactPresentation85_of_maximalGeneration
    (AffineSl2BoundaryFreeFieldPrimitive.K85.maximalGeneration_of_simpleCharacter D hchar)

end
end AffineSl2BoundaryC2Wakimoto
end VOA

section AxiomAudit
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation_of_classicalData
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation_of_adamovicMilas
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation_of_primitiveCriterion
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation43_of_maximalGeneration
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation85_of_maximalGeneration
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation43_of_onlyVacuumAffinePrimitives
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation85_of_onlyVacuumAffinePrimitives
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation_of_freeFieldCharacter
#print axioms VOA.AffineSl2BoundaryC2Wakimoto.exactPresentation85_of_freeFieldSimpleCharacter
end AxiomAudit
