/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteSimple
import VOA.Examples.Sl2CosetLeeYang
import VOA.Examples.AffineSl2BoundarySingularFamily

/-!
# The actual three affine factors in the Lee–Yang BRST construction

The first factor is the maximal-ideal quotient at `BoundarySingularFamily.level 1`,
the second is the maximal-ideal quotient at level one, and the auxiliary factor
is the universal affine VOA at level `-11/3`. All translation, parity, tensor
grading, positive-energy and nonzero-vacuum data are proved here.
-/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite
open scoped TensorProduct

noncomputable section

abbrev ALevel : ℂ := AffineSl2BoundarySingularFamily.level 1

theorem aLevel_eq : ALevel = (-4 / 3 : ℂ) :=
  AffineSl2BoundarySingularFamily.level_one

theorem aNoncritical : ALevel + 2 ≠ 0 :=
  AffineSl2BoundarySingularFamily.level_noncritical 1

theorem bNoncritical : (1 : ℂ) + 2 ≠ 0 := by norm_num

theorem uNoncritical : (-11 / 3 : ℂ) + 2 ≠ 0 := by norm_num

/-- The actual simple affine VOA at the first nonzero boundary level. -/
abbrev AVOA := AffineSl2GeneralRigidity.simple ALevel aNoncritical

/-- The actual level-one simple affine VOA. -/
abbrev BVOA := AffineSl2GeneralRigidity.simple 1 bNoncritical

/-- The universal auxiliary affine VOA. -/
abbrev UVOA := AffineSl2GeneralRigidity.universal (-11 / 3) uNoncritical

abbrev ASpace := AffineVOA.WakModule ALevel ⧸
  QuotVOA.maxGradedIdeal (AffineSl2GeneralRigidity.universal ALevel aNoncritical)

abbrev BSpace := AffineVOA.WakModule 1 ⧸
  QuotVOA.maxGradedIdeal (AffineSl2GeneralRigidity.universal 1 bNoncritical)

abbrev USpace := AffineVOA.WakModule (-11 / 3)

abbrev ASVA : SuperVertexAlgebra ASpace := simpleSVA ALevel aNoncritical
abbrev BSVA : SuperVertexAlgebra BSpace := simpleSVA 1 bNoncritical
abbrev USVA : SuperVertexAlgebra USpace := universalSVA (-11 / 3) uNoncritical

/-- Descended affine currents at the requested numerical boundary level. -/
def aAction : TranslatedAffineSl2Action ASVA (-4 / 3) where
  current := (simpleAction ALevel aNoncritical).current
  current_weight := (simpleAction ALevel aNoncritical).current_weight
  current_even := (simpleAction ALevel aNoncritical).current_even
  current_comm a b m n := by
    simpa only [aLevel_eq] using (simpleAction ALevel aNoncritical).current_comm a b m n
  translation := (simpleAction ALevel aNoncritical).translation

def bAction : TranslatedAffineSl2Action BSVA 1 := simpleAction 1 bNoncritical

def uAction : TranslatedAffineSl2Action USVA (-11 / 3) :=
  universalAction (-11 / 3) uNoncritical

theorem aParityCompatible : TensorVA.ParityCompatible ASVA :=
  simpleParityCompatible ALevel aNoncritical

theorem bParityCompatible : TensorVA.ParityCompatible BSVA :=
  simpleParityCompatible 1 bNoncritical

theorem uParityCompatible : TensorVA.ParityCompatible USVA :=
  universalParityCompatible (-11 / 3) uNoncritical

theorem aNatSupported : DSMor.NatSupported ASVA.grading :=
  simpleNatSupported ALevel aNoncritical

theorem bNatSupported : DSMor.NatSupported BSVA.grading :=
  simpleNatSupported 1 bNoncritical

theorem uNatSupported : DSMor.NatSupported USVA.grading :=
  universalNatSupported (-11 / 3) uNoncritical

theorem aVacuum_ne_zero : ASVA.vacuum ≠ 0 :=
  simpleVacuum_ne_zero ALevel aNoncritical

theorem bVacuum_ne_zero : BSVA.vacuum ≠ 0 :=
  simpleVacuum_ne_zero 1 bNoncritical

theorem uVacuum_ne_zero : USVA.vacuum ≠ 0 :=
  universalVacuum_ne_zero (-11 / 3) uNoncritical

theorem abTensorGrading : TensorVA.TensorGradingHyp ASVA BSVA :=
  DSMor.tensorGradingHyp_of_natSupported _ _ aNatSupported bNatSupported

def abSVA : SuperVertexAlgebra (ASpace ⊗[ℂ] BSpace) :=
  TensorVA.tensorSVA ASVA BSVA aParityCompatible bParityCompatible abTensorGrading

theorem abParityCompatible : TensorVA.ParityCompatible abSVA :=
  parityCompatible_tensorSVA _ _ aParityCompatible bParityCompatible abTensorGrading

theorem abNatSupported : DSMor.NatSupported abSVA.grading :=
  natSupported_tensorSVA _ _ aParityCompatible bParityCompatible abTensorGrading
    aNatSupported bNatSupported

theorem abVacuum_ne_zero : abSVA.vacuum ≠ 0 :=
  tensorSVA_vacuum_ne_zero _ _ aParityCompatible bParityCompatible abTensorGrading
    aVacuum_ne_zero bVacuum_ne_zero

theorem abuTensorGrading : TensorVA.TensorGradingHyp abSVA USVA :=
  DSMor.tensorGradingHyp_of_natSupported _ _ abNatSupported uNatSupported

/-- The diagonal current action in the first two concrete factors. -/
def diagonalAction : TranslatedAffineSl2Action abSVA ((-4 / 3 : ℂ) + 1) :=
  tensorTranslatedAffineAction aAction bAction aParityCompatible bParityCompatible
    abTensorGrading

theorem diagonalLevel_eq : (-4 / 3 : ℂ) + 1 = -1 / 3 := by norm_num

abbrev MatterSpace := (ASpace ⊗[ℂ] BSpace) ⊗[ℂ] USpace

/-- All three concrete affine factors, with the prescribed association. -/
def matterSVA : SuperVertexAlgebra MatterSpace :=
  tensorThreeSVA ASVA BSVA USVA aParityCompatible bParityCompatible uParityCompatible
    abTensorGrading abuTensorGrading

theorem matterParityCompatible : TensorVA.ParityCompatible matterSVA :=
  parityCompatible_tensorSVA _ _ abParityCompatible uParityCompatible abuTensorGrading

theorem matterNatSupported : DSMor.NatSupported matterSVA.grading :=
  natSupported_tensorSVA _ _ abParityCompatible uParityCompatible abuTensorGrading
    abNatSupported uNatSupported

theorem matterVacuum_ne_zero : matterSVA.vacuum ≠ 0 :=
  tensorSVA_vacuum_ne_zero _ _ abParityCompatible uParityCompatible abuTensorGrading
    abVacuum_ne_zero uVacuum_ne_zero

/-- The concrete Lee–Yang matter action at level minus four, with no input hypotheses. -/
def leeYangMatterAction : TranslatedAffineSl2Action matterSVA (-4) :=
  Sl2SemiInfinite.leeYangMatterAction aAction bAction uAction
    aParityCompatible bParityCompatible uParityCompatible abTensorGrading abuTensorGrading

theorem matterGhostTensorGrading : TensorVA.TensorGradingHyp matterSVA sl2GhostSVA :=
  DSMor.tensorGradingHyp_of_natSupported _ _ matterNatSupported natSupported_sl2GhostSVA

def brstSVA : SuperVertexAlgebra (MatterSpace ⊗[ℂ] Sl2GhostSpace) :=
  matterGhostSVA matterSVA matterParityCompatible matterGhostTensorGrading

/-- The actual residue differential, bundled on the concrete tensor algebra. -/
def leeYangBRSTComplex : BRST.BRSTComplex brstSVA :=
  semiInfiniteBRSTComplex leeYangMatterAction matterParityCompatible matterGhostTensorGrading

theorem leeYangBRSTComplex_Q :
    leeYangBRSTComplex.Q = semiInfiniteQ leeYangMatterAction.toAffineSl2Action := rfl

theorem leeYangBRSTComplex_Q_sq : leeYangBRSTComplex.Q * leeYangBRSTComplex.Q = 0 :=
  leeYangBRSTComplex.Q_sq

theorem leeYangBRSTComplex_vacuum_not_exact : brstSVA.vacuum ∉ leeYangBRSTComplex.imQ :=
  semiInfinite_vacuum_not_mem_imQ leeYangMatterAction matterParityCompatible
    matterGhostTensorGrading matterNatSupported matterVacuum_ne_zero

theorem leeYangBRSTComplex_cohomology_vacuum_ne_zero :
    leeYangBRSTComplex.cohomology.vacuum ≠ 0 :=
  semiInfinite_cohomology_vacuum_ne_zero leeYangMatterAction matterParityCompatible
    matterGhostTensorGrading matterNatSupported matterVacuum_ne_zero

end
end VOA.Sl2CosetConcrete
