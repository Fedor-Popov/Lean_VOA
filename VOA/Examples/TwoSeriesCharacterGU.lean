/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterAGIdentity
import VOA.Examples.TwoSeriesKoszulInvariants
import VOA.Examples.LYGramRankCharacter

/-!
# Affine GU ⇒ GU of `M(2, 2n+3)`, with the PBW input discharged

* `twoSeries_gradedUnitary_of_affine_invariants_gordon` — **Affine GU ⇒ GU of
  `M(2,2n+3)`**, given (I) the affine invariant count bounded by the Andrews–Gordon coefficient,
  and the **total** Andrews–Gordon lower bound `GordonLowerBound c_{2,2n+3} n`
  (`Σ_r gordonCoeff n N r ≤ dim L(c)_N`).  The length-refined `hpbw` is discharged
  (`twoSeries_hpbw_of_gordonLowerBound`, `TwoSeriesCharacterEndpoint`).
* `twoSeries_gradedUnitary_of_affine_invariants_gordon_final` — the same with the total
  lower bound proved (`gordonLowerBound_twoSeries`, `TwoSeriesCharacterAGIdentity`): only `hA`
  and the affine invariant count `hinv` remain.

`#print axioms`-clean, conditional on the displayed hypotheses (`hA`, `hinv`, and `hlow` for the
first).  Both theorems are kept here, apart from `TwoSeriesCharacterEndpoint.lean`
and `TwoSeriesCharacterAGIdentity.lean`, which are used by the Virasoro classical-freeness theorem
and must not import the graded-unitarity files.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.SymbolModel VOA.GradedUnitaryCohomology VirGradedUnitarity
open Sl2CosetConcrete VirGoodFil
open scoped BigOperators

noncomputable section

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`, with the refined PBW character discharged.**
For `k = -2 + 2/(2n+1)`: graded unitarity of `L_k(sl₂)`, the affine invariant count
`rank (g[t]-invariants of weight N in gr_r L_k(sl₂) ⊗ L_1(sl₂)) ≤ gordonCoeff n N r`, and the total
Andrews–Gordon lower bound `Σ_r gordonCoeff n N r ≤ dim L(c_{2,2n+3})_N` imply graded unitarity
of `M(2, 2n+3)`. -/
theorem twoSeries_gradedUnitary_of_affine_invariants_gordon (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (hinv : ∀ (N : ℤ) (r : ℕ), Module.rank ℂ (affineInvariants (twoSeriesLevels n) r N) ≤
      VOA.TwoSeriesCharacter.gordonCoeff n N r)
    (hlow : VOA.TwoSeriesCharacter.GordonLowerBound (twoSeriesLevels n).c n) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_affine_invariants n hA (VOA.TwoSeriesCharacter.gordonCoeff n) hinv
    (twoSeries_hpbw_of_gordonLowerBound n hlow)

end

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`, with the PBW input discharged.**  For
`k = -2 + 2/(2n+1)`: graded unitarity of `L_k(sl₂)` and the affine invariant count
`rank (g[t]-invariants of weight N in gr_r L_k(sl₂) ⊗ L_1(sl₂)) ≤ gordonCoeff n N r`
imply graded unitarity of `M(2, 2n+3)`. -/
theorem twoSeries_gradedUnitary_of_affine_invariants_gordon_final (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (hinv : ∀ (N : ℤ) (r : ℕ), Module.rank ℂ (affineInvariants (twoSeriesLevels n) r N) ≤
      VOA.TwoSeriesCharacter.gordonCoeff n N r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_affine_invariants_gordon n hA hinv (gordonLowerBound_twoSeries n)

end VOA.TwoSeries
