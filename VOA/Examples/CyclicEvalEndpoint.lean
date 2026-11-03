/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.CyclicEvalParity

/-!
# The endpoint with the cyclic evaluation split into its mathematical inputs

The current endpoint `leeYang_gradedUnitary_of_affine_cyclicEvaluation` takes
`E : LeadingCyclicEvaluation (endpointKahler hA)`. Here `E` is constructed from:

* `endpoint_negZero` — **proved**: the leading cohomology vanishes at negative `2R`
  (the interpreted grading has no pieces at negative `2R`, `brstDeg_nonnegR_std`);
* `endpoint_oddZero` (`CyclicEvalParity`) — **proved**: the leading cohomology vanishes at odd
  `2R` (relative states are fixed by the three `c₀`-parities, which act by `-1` there);
* `EndpointSymbolModels hA` — for every weight `n` and degree `r`, a `SymbolCyclicModel` for the
  **actual** level-one module `B = L_1(sl₂)` (`BSpace`) with its **actual** nonnegative current
  modes `J^a_m` (`bMode`) and conformal grading (`bWeight`): the symbol module with cyclic dual
  vector and relation (A1) (input (A) of the coset note), and the injective leading Koszul
  embedding into `(M ⊗ L_1)^{g[t]}_n`;
* `LevelOneFockCoordinates` — the Frenkel–Kac Fock coordinates of the charge-`r` sectors of the
  actual `L_1(sl₂)`: an injective map of each `(L₀ = E, h₀ = 2r)` space into `C[a_1, a_2, …]`,
  of weighted degree `E - r²`, intertwining `J^h_{i+1}` with `2(i+1)∂_{a_i}`.

`leeYang_gradedUnitary_of_affine_symbolCyclic` — **Affine GU ⇒ Lee–Yang GU**,
`#print axioms`-clean, conditional on `hA` (the hypothesis), `models`, `fock`, and the
classical Rogers–Ramanujan lower bound `lower`.
-/

namespace VOA.CyclicEval

open VOA.InvariantSymbol VOA.GradedUnitaryCohomology VOA.LeeYangTransferAssembly
open VOA.ConcreteHodge TensorProduct Sl2CosetConcrete
open Module (finrank)

noncomputable section
set_option synthInstance.maxHeartbeats 200000

/-- The actual nonnegative current modes of `L_1(sl₂)`: `(a, m) ↦ J^a_m`
(`a = 0, 1, 2` for `e, f, h`). -/
def bMode (k : Fin 3 × ℕ) : Module.End ℂ BSpace :=
  mode (BSVA.Y (bAction.current k.1)) (k.2 : ℤ)

/-- The index of `h₀`. -/
abbrev bHZero : Fin 3 × ℕ := (2, 0)

/-- The index of `h_{i+1}`. -/
abbrev bHPos (i : ℕ) : Fin 3 × ℕ := (2, i + 1)

/-- The conformal grading of `L_1(sl₂)`. -/
def bWeight (E : ℤ) : Submodule ℂ BSpace := BSVA.grading (E : ℂ)

/-- OPEN (standard; Frenkel–Kac): **the Fock coordinates of the charge sectors of `L_1(sl₂)`.** -/
abbrev LevelOneFockCoordinates : Type :=
  ∀ r : ℕ, FockCoordinates bMode bHZero bHPos bWeight r

/-- OPEN (leading Koszul embedding + input (A)): the symbol models for the endpoint geometry. -/
abbrev EndpointSymbolModels (hA : GradedUnitary affineForm affineRealStructure affineFlag) :=
  ∀ n (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ),
    SymbolCyclicModel bMode bHZero bHPos bWeight ((endpointKahler hA).model n hp) n r

/-- **No leading cohomology at negative `2R`** (proved). -/
theorem endpoint_negZero (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ∀ n (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (j : ℤ), j < 0 →
      finrank ℂ (((endpointKahler hA).model n hp).leadCohom (j, 0)) = 0 := by
  intro n hp j hj
  apply finrank_leadCohom_eq_zero_of_deg
  change (brstDeg bgGh (((j, 0) : ℤ × ℤ), (n : ℂ))).comap (relativeWeight n).subtype = ⊥
  rw [brstDeg_nonnegR_std bgGh_isStd ((j, 0), (n : ℂ)) hj, Submodule.comap_bot,
    Submodule.ker_subtype]

/-- The endpoint's `LeadingCyclicEvaluation`, from the symbol models and the Fock
coordinates (odd and negative `2R` vanishing proved). -/
def endpointCyclicEvaluation (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (models : EndpointSymbolModels hA) (fock : LevelOneFockCoordinates) :
    LeadingCyclicEvaluation (endpointKahler hA) :=
  leadingCyclicEvaluation_of_models _ (endpoint_oddZero hA) (endpoint_negZero hA) models fock

/-- **Affine GU ⇒ Lee–Yang GU**, with the cyclic evaluation constructed from the symbol
models and the level-one Fock coordinates. `#print axioms`-clean, conditional on `hA` (the
hypothesis), `models`, `fock`, `lower`. -/
theorem leeYang_gradedUnitary_of_affine_symbolCyclic
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (models : EndpointSymbolModels hA)
    (fock : LevelOneFockCoordinates)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_cyclicEvaluation hA
    (endpointCyclicEvaluation hA models fock) lower

end

end VOA.CyclicEval
