/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperBlockBoundC2
import VOA.Examples.SympFermSuperC2
import VOA.Examples.SympFermSuperZhu

/-!
# The sharp super block bound for symplectic fermions

The ambient rank-one symplectic-fermion super VOA is integral and `C₂`-cofinite, while its super
Zhu algebra has dimension at most four.  The super Arike--Nagatomo bound therefore makes its
untwisted supertrace block space finite-dimensional of dimension at most four.  Rationality is
not assumed; indeed the same development proves that its super Zhu algebra is not semisimple.
-/

namespace VOA.SympFerm

open Module (finrank)

/-- The untwisted integral-weight supertrace block space of rank-one symplectic fermions has
dimension at most four. -/
theorem finrank_sympFerm_superAnalyticBlocks_le_four :
    finrank ℂ (Submodule.map restrictImGT
      sympFermSVOA.toSuperNearVOA.superAnalyticBlocks) ≤ 4 := by
  let hZ := sympFermSVOA.superZhuRingData sympFerm_integralWeights
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  haveI : FiniteDimensional ℂ ASF := ASF_finiteDimensional
  calc
    finrank ℂ (Submodule.map restrictImGT
        sympFermSVOA.toSuperNearVOA.superAnalyticBlocks)
        ≤ finrank ℂ (ASF ⧸ hZ.superZhuCommSpan) :=
          (SuperNearVOA.finrank_superAnalyticBlocks_le_finrank_quot_superZhuCommSpan
            sympFermSVOA sympFerm_integralWeights sympFerm_superC2Cofinite).2
    _ ≤ finrank ℂ ASF := Submodule.finrank_quotient_le hZ.superZhuCommSpan
    _ ≤ 4 := finrank_ASF_le_four

/-- In particular, the symplectic-fermion untwisted supertrace block space is
finite-dimensional. -/
theorem finiteDimensional_sympFerm_superAnalyticBlocks :
    FiniteDimensional ℂ (Submodule.map restrictImGT
      sympFermSVOA.toSuperNearVOA.superAnalyticBlocks) :=
  SuperNearVOA.finiteDimensional_superAnalyticBlocks_of_superC2
    sympFermSVOA sympFerm_integralWeights sympFerm_superC2Cofinite

end VOA.SympFerm
