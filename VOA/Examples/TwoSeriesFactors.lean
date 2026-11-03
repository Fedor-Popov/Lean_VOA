/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesLevels
import VOA.Examples.Sl2CosetConcreteFactors

/-!
# The three affine factors and the BRST complex, for any `CosetLevels`

This is `Sl2CosetConcreteFactors` with the numbers `level 1`, `-4/3`, `-11/3` replaced by the
fields of `L : CosetLevels`.  Every proof is the level-1 proof with the numerical rewrite
replaced by the corresponding field (`kAct_eq`, `sum`).  At `L = leeYangLevels` each
definition unfolds to the existing concrete one (`leeYangMatterAction_eq` below is `rfl`).

* `matterAction L` — the diagonal current action on `L_{kA} ⊗ L_1 ⊗ V^{kU}` at level `-4`;
* `brstComplex L` — the actual semi-infinite BRST complex, with nonzero vacuum class.
-/

namespace VOA.TwoSeries

open Sl2SemiInfinite VOA.Sl2CosetConcrete
open scoped TensorProduct

noncomputable section

variable (L : CosetLevels)

/-- The actual simple affine VOA at the boundary level. -/
abbrev AVOA := AffineSl2GeneralRigidity.simple L.kA L.aNoncritical

/-- The universal auxiliary affine VOA. -/
abbrev UVOA := AffineSl2GeneralRigidity.universal L.kU L.uNoncritical

abbrev ASpace := AffineVOA.WakModule L.kA ⧸
  QuotVOA.maxGradedIdeal (AffineSl2GeneralRigidity.universal L.kA L.aNoncritical)

abbrev USpace := AffineVOA.WakModule L.kU

abbrev ASVA : SuperVertexAlgebra (ASpace L) := simpleSVA L.kA L.aNoncritical
abbrev USVA : SuperVertexAlgebra (USpace L) := universalSVA L.kU L.uNoncritical

/-- Descended affine currents, indexed by `kAct`. -/
def aAction : TranslatedAffineSl2Action (ASVA L) L.kAct where
  current := (simpleAction L.kA L.aNoncritical).current
  current_weight := (simpleAction L.kA L.aNoncritical).current_weight
  current_even := (simpleAction L.kA L.aNoncritical).current_even
  current_comm a b m n := by
    simpa only [L.kAct_eq] using (simpleAction L.kA L.aNoncritical).current_comm a b m n
  translation := (simpleAction L.kA L.aNoncritical).translation

def uAction : TranslatedAffineSl2Action (USVA L) L.kU :=
  universalAction L.kU L.uNoncritical

theorem aParityCompatible : TensorVA.ParityCompatible (ASVA L) :=
  simpleParityCompatible L.kA L.aNoncritical

theorem uParityCompatible : TensorVA.ParityCompatible (USVA L) :=
  universalParityCompatible L.kU L.uNoncritical

theorem aNatSupported : DSMor.NatSupported (ASVA L).grading :=
  simpleNatSupported L.kA L.aNoncritical

theorem uNatSupported : DSMor.NatSupported (USVA L).grading :=
  universalNatSupported L.kU L.uNoncritical

theorem aVacuum_ne_zero : (ASVA L).vacuum ≠ 0 :=
  simpleVacuum_ne_zero L.kA L.aNoncritical

theorem uVacuum_ne_zero : (USVA L).vacuum ≠ 0 :=
  universalVacuum_ne_zero L.kU L.uNoncritical

theorem abTensorGrading : TensorVA.TensorGradingHyp (ASVA L) BSVA :=
  DSMor.tensorGradingHyp_of_natSupported _ _ (aNatSupported L) bNatSupported

def abSVA : SuperVertexAlgebra (ASpace L ⊗[ℂ] BSpace) :=
  TensorVA.tensorSVA (ASVA L) BSVA (aParityCompatible L) bParityCompatible (abTensorGrading L)

theorem abParityCompatible : TensorVA.ParityCompatible (abSVA L) :=
  parityCompatible_tensorSVA _ _ (aParityCompatible L) bParityCompatible (abTensorGrading L)

theorem abNatSupported : DSMor.NatSupported (abSVA L).grading :=
  natSupported_tensorSVA _ _ (aParityCompatible L) bParityCompatible (abTensorGrading L)
    (aNatSupported L) bNatSupported

theorem abVacuum_ne_zero : (abSVA L).vacuum ≠ 0 :=
  tensorSVA_vacuum_ne_zero _ _ (aParityCompatible L) bParityCompatible (abTensorGrading L)
    (aVacuum_ne_zero L) bVacuum_ne_zero

theorem abuTensorGrading : TensorVA.TensorGradingHyp (abSVA L) (USVA L) :=
  DSMor.tensorGradingHyp_of_natSupported _ _ (abNatSupported L) (uNatSupported L)

/-- The diagonal current action in the first two factors, at level `kAct + 1`. -/
def diagonalAction : TranslatedAffineSl2Action (abSVA L) (L.kAct + 1) :=
  tensorTranslatedAffineAction (aAction L) bAction (aParityCompatible L) bParityCompatible
    (abTensorGrading L)

abbrev MatterSpace := (ASpace L ⊗[ℂ] BSpace) ⊗[ℂ] USpace L

/-- All three factors, with the prescribed association. -/
def matterSVA : SuperVertexAlgebra (MatterSpace L) :=
  tensorThreeSVA (ASVA L) BSVA (USVA L) (aParityCompatible L) bParityCompatible
    (uParityCompatible L) (abTensorGrading L) (abuTensorGrading L)

theorem matterParityCompatible : TensorVA.ParityCompatible (matterSVA L) :=
  parityCompatible_tensorSVA _ _ (abParityCompatible L) (uParityCompatible L)
    (abuTensorGrading L)

theorem matterNatSupported : DSMor.NatSupported (matterSVA L).grading :=
  natSupported_tensorSVA _ _ (abParityCompatible L) (uParityCompatible L) (abuTensorGrading L)
    (abNatSupported L) (uNatSupported L)

theorem matterVacuum_ne_zero : (matterSVA L).vacuum ≠ 0 :=
  tensorSVA_vacuum_ne_zero _ _ (abParityCompatible L) (uParityCompatible L) (abuTensorGrading L)
    (abVacuum_ne_zero L) (uVacuum_ne_zero L)

/-- The matter action at level `-4`: the field-by-field generalization of
`Sl2SemiInfinite.leeYangMatterAction`, with `L.sum` in place of `leeYangMatter_level`. -/
def matterAction : TranslatedAffineSl2Action (matterSVA L) (-4) where
  current := (tensorThreeTranslatedAffineAction (aAction L) bAction (uAction L)
    (aParityCompatible L) bParityCompatible (uParityCompatible L) (abTensorGrading L)
    (abuTensorGrading L)).current
  current_weight := (tensorThreeTranslatedAffineAction (aAction L) bAction (uAction L)
    (aParityCompatible L) bParityCompatible (uParityCompatible L) (abTensorGrading L)
    (abuTensorGrading L)).current_weight
  current_even := (tensorThreeTranslatedAffineAction (aAction L) bAction (uAction L)
    (aParityCompatible L) bParityCompatible (uParityCompatible L) (abTensorGrading L)
    (abuTensorGrading L)).current_even
  current_comm a b m n := by
    simpa only [L.sum] using
      (tensorThreeTranslatedAffineAction (aAction L) bAction (uAction L)
        (aParityCompatible L) bParityCompatible (uParityCompatible L) (abTensorGrading L)
        (abuTensorGrading L)).current_comm a b m n
  translation := (tensorThreeTranslatedAffineAction (aAction L) bAction (uAction L)
    (aParityCompatible L) bParityCompatible (uParityCompatible L) (abTensorGrading L)
    (abuTensorGrading L)).translation

theorem matterGhostTensorGrading : TensorVA.TensorGradingHyp (matterSVA L) sl2GhostSVA :=
  DSMor.tensorGradingHyp_of_natSupported _ _ (matterNatSupported L) natSupported_sl2GhostSVA

def brstSVA : SuperVertexAlgebra (MatterSpace L ⊗[ℂ] Sl2GhostSpace) :=
  matterGhostSVA (matterSVA L) (matterParityCompatible L) (matterGhostTensorGrading L)

/-- The actual semi-infinite BRST complex of the level-`L` coset construction. -/
def brstComplex : BRST.BRSTComplex (brstSVA L) :=
  semiInfiniteBRSTComplex (matterAction L) (matterParityCompatible L)
    (matterGhostTensorGrading L)

theorem brstComplex_Q : (brstComplex L).Q = semiInfiniteQ (matterAction L).toAffineSl2Action :=
  rfl

theorem brstComplex_vacuum_not_exact : (brstSVA L).vacuum ∉ (brstComplex L).imQ :=
  semiInfinite_vacuum_not_mem_imQ (matterAction L) (matterParityCompatible L)
    (matterGhostTensorGrading L) (matterNatSupported L) (matterVacuum_ne_zero L)

theorem brstComplex_cohomology_vacuum_ne_zero : (brstComplex L).cohomology.vacuum ≠ 0 :=
  semiInfinite_cohomology_vacuum_ne_zero (matterAction L) (matterParityCompatible L)
    (matterGhostTensorGrading L) (matterNatSupported L) (matterVacuum_ne_zero L)

/-! ### At Lee–Yang the generic objects are the existing ones, definitionally -/

theorem aVOA_leeYang : AVOA leeYangLevels = Sl2CosetConcrete.AVOA := rfl

theorem aAction_leeYang : aAction leeYangLevels = Sl2CosetConcrete.aAction := rfl

theorem uAction_leeYang : uAction leeYangLevels = Sl2CosetConcrete.uAction := rfl

theorem matterSVA_leeYang : matterSVA leeYangLevels = Sl2CosetConcrete.matterSVA := rfl

theorem matterAction_leeYang :
    matterAction leeYangLevels = Sl2CosetConcrete.leeYangMatterAction := rfl

theorem brstComplex_leeYang :
    brstComplex leeYangLevels = Sl2CosetConcrete.leeYangBRSTComplex := rfl

end

end VOA.TwoSeries
