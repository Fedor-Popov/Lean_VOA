/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LevelOneHeisBottom

/-!
# The endpoint with the level-one Heisenberg inputs discharged

Both structural statements about `L_1(sl₂)` used by the cyclic-evaluation bound are proved:

* `levelOneBottomDetected : LevelOneBottomDetected` (`LevelOneHeisBottom`);
* `levelOneHeisenbergSingular : LevelOneHeisenbergSingular` (`LevelOneHeisSingular`).

Hence:

* `levelOneHeisenbergSeparation : LevelOneHeisenbergSeparation` — **proved outright**;
* `leeYang_gradedUnitary_of_affine_symbolModels` — **Affine GU ⇒ Lee–Yang GU**,
  `#print axioms`-clean, conditional on `hA` (the hypothesis), `models` (the endpoint symbol
  models), and `lower` (the classical Rogers–Ramanujan lower bound).
-/

namespace VOA.LevelOneHeis

open VOA.CyclicEval VOA.GradedUnitaryCohomology VOA.LeeYangTransferAssembly VOA.ConcreteHodge

/-- **Heisenberg separation of the charge sectors of `L_1(sl₂)`**, proved outright. -/
theorem levelOneHeisenbergSeparation : LevelOneHeisenbergSeparation :=
  levelOneHeisenbergSeparation_of_singular levelOneBottomDetected levelOneHeisenbergSingular

/-- **Affine GU ⇒ Lee–Yang GU**, with every level-one input proved.
`#print axioms`-clean, conditional on `hA` (the hypothesis), `models`, `lower`. -/
theorem leeYang_gradedUnitary_of_affine_symbolModels
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (models : EndpointSymbolModels hA)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_heisenbergSingular hA models levelOneBottomDetected
    levelOneHeisenbergSingular lower

end VOA.LevelOneHeis
