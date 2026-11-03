/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.SympFermC2
import VOA.Modularity.SuperZhuAlgebraFinite

/-!
# The hand-computed symplectic-fermion `C₂` quotient is the generic super quotient

`Examples.SympFermC2` predates the generic definitions `superO₂` and `SuperC2Cofinite`, so it
spells out the same mode span as `SympFerm.O₂SF`.  This file records the definitional bridge and
packages the existing four-generator computation as `SuperC2Cofinite sympFermSVOA`.
-/

namespace VOA.SympFerm

open GammaThetaStmt

/-- The hand-written `O₂SF` is definitionally the generic super `O₂`. -/
theorem O₂SF_eq_superO₂ : O₂SF = superO₂ sympFermSVOA := rfl

/-- The ambient symplectic-fermion super VOA is `C₂`-cofinite. -/
theorem sympFerm_superC2Cofinite : SuperC2Cofinite sympFermSVOA := by
  rw [SuperC2Cofinite, ← O₂SF_eq_superO₂]
  exact A₂SF_finiteDimensional

/-- The generic super `C₂` quotient of `SF` has dimension at most four. -/
theorem finrank_superC2Quotient_le_four :
    Module.finrank ℂ (FockSF ⧸ superO₂ sympFermSVOA) ≤ 4 := by
  rw [← O₂SF_eq_superO₂]
  exact finrank_A₂SF_le_four

/-- The Dong–Zhao super Zhu algebra of symplectic fermions is finite-dimensional. -/
theorem sympFerm_superA_finiteDimensional :
    FiniteDimensional ℂ
      (sympFermSVOA.toSuperNearVOA.superA sympFerm_integralWeights) :=
  SuperNearVOA.finiteDimensional_superA_of_superC2Cofinite
    sympFermSVOA sympFerm_integralWeights sympFerm_superC2Cofinite

end VOA.SympFerm
