/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.RealizationAssembly
import VOA.Modularity.Anm0FiniteDim

/-!
# Residual **(b)** reduced to `C_{n+2}`-cofiniteness, conditional on `Pr`

Chaining the pieces:

| step | status |
|---|---|
| `SimpleAModsRealized` ⟸ `hfin` | `simpleAModsRealized_of_finiteWeights` |
| `hfin` ⟸ `∀ n, dim (DJPiece W U n) < ∞` | `finiteWeights_djLU` (this file) |
| `dim DJPiece < ∞` ⟸ `dim A_{n,0}(𝒱) < ∞` and `dim U < ∞` | `finiteDimensional_DJPiece` |
| `dim A_{n,0}(𝒱) < ∞` ⟸ `C_{n+2}`-cofinite | `finiteDimensional_AnmFull_of_cofinite` |
| `C_{n+2}`-cofinite ⟸ `C₂`-cofinite | not used on this route (see below) |

**Superseded.**  Gaberdiel–Neitzke Prop. 8 is built (`gnProp8_GNReach`,
`strictSpanning_of_C2Cofinite`, `Modularity/GNProp8Closure.lean`), and residual **(b)** is
discharged, given `C₂`-cofiniteness and the explicit `Pr`, by `simpleAModsRealized_of_C2Cofinite`
via strict-decrease spanning — not through the last row of this table, which this file does not
supply.

## Main results

* `finiteWeights_djLU` — the `OrdVModule.finrank` obligation from the graded pieces;
* `simpleAModsRealized_of_cofinite` — **(b) from `C_{n+2}`-cofiniteness for all `n`**.

## Status
Proof-term `#print axioms`-clean and `pbw`-free, no `sorry`. The cofiniteness family and the explicit
`BottomProjection` assumption `Pr` are named hypotheses. The project-level witness is supplied by
`voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`. This is a reduction of (b), *not* an
unconditional discharge.
-/

namespace VOA

open scoped BigOperators TensorProduct
open VHat VHat.DLM3 GradedLWWeakModule

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The `OrdVModule.finrank` obligation from the graded pieces.**  `L(U)`'s weight space at `α`
is the image of `M(U)`'s, which is `M(U)(m) ≅ DJPiece W U m` when `α = h + m` and `⊥` otherwise. -/
theorem finiteWeights_djLU {W : VertexOperatorAlgebra 𝒱}
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    (hU : Nontrivial U.carrier) (hval : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (hval + (n : ℂ)) • x)
    (hpiece : ∀ n : ℕ, FiniteDimensional ℂ (DJPiece W U n)) :
    (djLU Pr U hU hval hL0).FiniteWeights := by
  classical
  intro α
  have hsrc : FiniteDimensional ℂ (djCWeight W U hval α) := by
    by_cases hcase : ∃ m : ℕ, hval + (m : ℂ) = α
    · obtain ⟨m, rfl⟩ := hcase
      rw [djCWeight_cast]
      haveI := hpiece m
      exact (DJCarrier.degEquivPiece W U m).symm.finiteDimensional
    · have hbot : djCWeight W U hval α = ⊥ := by
        rw [djCWeight]
        exact le_antisymm (iSup_le fun n => iSup_le fun hn => absurd ⟨n, hn⟩ hcase) bot_le
      rw [hbot]
      infer_instance
  haveI := hsrc
  show FiniteDimensional ℂ
    ((djCWeight W U hval α).map
      (maxJ (djGradedLW_of_pbwDatum Pr U hU hval hL0)).carrier.mkQ)
  infer_instance

/-- **Residual (b) from `C_{n+2}`-cofiniteness.**  Every simple `A(𝒱)`-module is the bottom
of an irreducible lowest-weight `𝒱`-module, provided `𝒱/C_{n+2}(𝒱)` is finite-dimensional for every
`n` — which is what Gaberdiel–Neitzke Prop. 8 would deduce from `C₂`-cofiniteness. -/
theorem simpleAModsRealized_of_cofinite {W : VertexOperatorAlgebra 𝒱}
    (hC2 : C2Cofinite W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcof : ∀ n : ℕ, ∃ S : Finset 𝒱, (∀ s ∈ (S : Set 𝒱), IsHomog W s) ∧
      (⊤ : Submodule ℂ 𝒱)
        = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-((n : ℤ) + 2))) :
    SimpleAModsRealized W := by
  refine simpleAModsRealized_of_finiteWeights_of_C2 hC2 Pr (fun U hs hval hL0 => ?_)
  haveI hUfin : FiniteDimensional ℂ U.carrier :=
    finiteDimensional_of_isSimpleAMod (finiteDimensional_A_of_C2Cofinite W hC2) U hs
  refine finiteWeights_djLU Pr U.toAmModZero hs.1 hval hL0 (fun n => ?_)
  obtain ⟨S, hShom, htop⟩ := hcof n
  exact finiteDimensional_DJPiece U.toAmModZero n
    (finiteDimensional_AnmFull_of_cofinite W n S hShom htop).1 hUfin

/-! ## Non-vacuity: the `n = 0` member of `hcof` is free -/

/-- **Sanity check on the indexing.**  At `n = 0` the required cofiniteness is `C₂` itself
(`CGen W (-(0+2)) = CGen W (-2) = O₂ W`), so the `n = 0` member of `hcof` follows from
`C2Cofinite` — the family is correctly indexed and is not vacuous. -/
theorem hcof_zero_of_C2Cofinite {W : VertexOperatorAlgebra 𝒱} (hC2 : C2Cofinite W) :
    ∃ S : Finset 𝒱, (∀ s ∈ (S : Set 𝒱), IsHomog W s) ∧
      (⊤ : Submodule ℂ 𝒱)
        = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-(((0 : ℕ) : ℤ) + 2)) := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨(Finset.univ.image gen) ∪ {W.vacuum}, ?_, ?_⟩
  · intro s hs
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Finset.coe_singleton, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hs
    rcases hs with ⟨i, rfl⟩ | rfl
    · exact ⟨(wt i : ℤ), hgen i⟩
    · exact ⟨0, W.vacuum_mem_grading_zero⟩
  · have hset : (((Finset.univ.image gen) ∪ {W.vacuum} : Finset 𝒱) : Set 𝒱)
        = Set.range gen ∪ {W.vacuum} := by
      ext x; simp [Set.mem_range]
    rw [hset, show (-(((0 : ℕ) : ℤ) + 2)) = (-2 : ℤ) by norm_num, CGen_neg_two]
    exact hdec

end VOA
