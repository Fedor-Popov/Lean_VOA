/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesAssembly
import VOA.Examples.AdamovicDescCyclic

/-!
# Sanity check: the general theorem at `n = 1` is the proved Lee–Yang theorem

Every hypothesis of `twoSeries_gradedUnitary_of_affine 1` other than `hA` is derived here from
the existing Lee–Yang chain:

* `leeYangHodgeInputs hA : BRSTHodgeInputs (twoSeriesLevels 1)` — from the concrete endpoint
  geometry `ConcreteHodge.endpointKahler hA`, its `GUData`, the generator tests, and the three
  proved harmonic-metric bridges;
* `twoSeriesSqueezeInput_one hA : SqueezeInput (twoSeriesLevels 1) _` — with
  `coeff = gapTwoCoefficient`; (I) is the proved invariant-symbol bound (jet ring, cyclic
  evaluation, Heisenberg separation), (II) is the proved Lee–Yang PBW character.

All transfers between the generic level-`L` objects and the concrete Lee–Yang objects are
definitional (`twoSeriesLevels 1 = leeYangLevels` is `rfl`, and every generic construction was
built field by field from the concrete one).

* `leeYang_gradedUnitary_of_affine_viaTwoSeries` — Lee–Yang GU recovered from the general
  theorem, conditional only on `hA`.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.LeeYangTransferAssembly VOA.LeeYangShortcut
open VOA.SymbolModel VOA.KoszulResidual VOA.KoszulConcrete VOA.CyclicEval VOA.LevelOneHeis
open VOA.AdamovicSymbol GradedUnitaryCohomology

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 20000

noncomputable section

variable (hA : GradedUnitary LeeYangTransferAssembly.affineForm
  LeeYangTransferAssembly.affineRealStructure LeeYangTransferAssembly.affineFlag)

/-- The proved Lee–Yang invariant-symbol bound, assembled from the existing chain. -/
theorem leeYang_symbolBound : LeadingInvariantSymbolBound (endpointKahler hA) := by
  have desc : ∀ r : ℕ, WordSymbolDescends (r + 2) := fun r => Desc.wordSymbolDescends (r + 2)
  have chi := VOA.JetProduct.jetProductBound_of_lower VOA.JetFermionic.jetFermionicLower
  have strict := grJetStrict_of_leadingSymbol_product (jetLeadingSymbols_of_descends desc) chi
  have koszul := endpointGrLeadKoszul_of_residual hA
    (koszulResidual_of_symbols hA (symbolResidual_endpoint hA))
  have models := endpointSymbolModels_of_gr hA (fun r => (strict r).toGrCyclicVector)
    (fun n hp r => (koszul n hp r).toGrKoszulEmbedding)
  exact leadingInvariantSymbolBound_of_heisenberg _ (endpoint_oddZero hA) (endpoint_negZero hA)
    models (levelOneHeisenbergSeparation_of_singular levelOneBottomDetected
      levelOneHeisenbergSingular).toSep

/-- The concrete endpoint geometry, read as a level-`(twoSeriesLevels 1)` geometry. -/
def leeYangBRSTKahler : BRSTKahlerGeometry (twoSeriesLevels 1) where
  geometry := (endpointKahler hA).geometry
  differential := (endpointKahler hA).differential
  ghost := (endpointKahler hA).ghost

private abbrev endpointPkg :=
  (bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg LevelOneUnitary.bUnitary

/-- The BRST/Hodge package at `n = 1`, from the existing proofs. -/
def leeYangHodgeInputs : BRSTHodgeInputs (twoSeriesLevels 1) where
  kahler := leeYangBRSTKahler hA
  weakGU := concreteKahler_weakGU LevelOneUnitary.bUnitary bgPG_pos _
  gu := ⟨(sp2GUData0 hA LevelOneUnitary.bUnitary bgPG_pos bgGh bgGh_isStd
    (endpointPkg hA).sp2 (endpointPkg hA).conj0).data⟩
  generators hp :=
    have h := interpretedGenerators_std bgGh hA LevelOneUnitary.bUnitary bgPG_pos _ _ _
      bgGh_isStd hp
    ⟨h.vacuum, h.creation⟩
  vacuumNormalized hp := harmonicVacuumNormalized_proved hA LevelOneUnitary.bUnitary hp
  creationAdjoint i n m hpn hpm x y hx hy :=
    harmonicCreationAdjoint_proved hA LevelOneUnitary.bUnitary i n m hpn hpm x y hx hy
  wordsReal n hp w hw := harmonicWordsReal_proved hA LevelOneUnitary.bUnitary n hp w hw

/-- `TwoSeriesSqueezeInput 1`: the squeeze input at `n = 1`, from the existing proofs, with
`coeff = gapTwoCoefficient` (the coefficient of `z^{r(r+1)}/(z)_r`). -/
def twoSeriesSqueezeInput_one : SqueezeInput (twoSeriesLevels 1) (leeYangHodgeInputs hA).kahler where
  coeff := gapTwoCoefficient
  invariantBound := leeYang_symbolBound hA
  pbwLower n p :=
    ((LeeYangCharacter.leeYangPBWCharacter_iff_lowerBound.mpr
      VOA.RRLower.leeYangRRLowerBound_holds) n p).ge

/-- **Sanity check.** The general `(2, 2n+3)` theorem at `n = 1`, with the Hodge package and
the squeeze input supplied by the existing proofs, is the Lee–Yang theorem: conditional only on
`hA`. -/
theorem leeYang_gradedUnitary_of_affine_viaTwoSeries
    (hA : GradedUnitary LeeYangTransferAssembly.affineForm
      LeeYangTransferAssembly.affineRealStructure LeeYangTransferAssembly.affineFlag) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  twoSeries_gradedUnitary_of_affine 1 hA (leeYangHodgeInputs hA) (twoSeriesSqueezeInput_one hA)

end

end VOA.TwoSeries
