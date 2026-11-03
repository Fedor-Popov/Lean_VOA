/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaUnconditional
import VOA.Examples.TwoSeriesJetPoincareArr

/-!
# Affine GU ⇒ GU of `M(2, 7)` and `M(2, 5)`, conditional only on the affine input

The jet-ideal Poincaré input `JetPoincareCoreT0 (m + 1)` of
`SliceMap.twoSeries_gradedUnitary_of_affine` is proved for `m + 1 = 2`
(`JetPoincareTwo.jetPoincareCoreT0_two`) and `m + 1 = 1` (`J_1` contains every generator).

* `twoSeries_gradedUnitary_M27_of_affine` — **affine GU at `twoSeriesLevels 2` ⇒ GU of
  `M(2, 7)`**, `#print axioms`-clean, conditional only on `hA`;
* `twoSeries_gradedUnitary_M25_of_affine` — the same at `twoSeriesLevels 1` (`M(2, 5)`);
* `twoSeries_gradedUnitary_of_affine_arrangement` — **affine GU ⇒ GU of `M(2, 2m+5)` for
  every `m`**, conditional only on `hA` and the pure commutative-algebra input
  `JetPoincareArr.ArrangementInclusion (m + 1)` (proved for `m + 1 = 2`:
  `JetPoincareArr.arrangementInclusion_two`).
-/

namespace VOA.TwoSeries.JetPoincareTwo

open VOA.GradedUnitaryCohomology VirGradedUnitarity VOA.TwoSeries.StrictModel
open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong
open VOA.VirModule VOA.TwoSeries.DSSlice VOA.VirSimple VOA.LeeYangCharacter
open VOA.SymbolModel VOA.AffineVOA.Inst Sl2CosetConcrete VOA.AffineSl2BoundaryMaximalIdeal

/-- **Affine GU ⇒ GU of `M(2, 7)`**, conditional only on `hA`. -/
theorem twoSeries_gradedUnitary_M27_of_affine
    (hA : GradedUnitary (affineForm (twoSeriesLevels 2))
      (affineRealStructure (twoSeriesLevels 2)) (affineFlag (twoSeriesLevels 2))) :
    VirGradedUnitary (twoSeriesLevels 2).c (targetRealStructure (twoSeriesLevels 2)) :=
  SliceMap.twoSeries_gradedUnitary_of_affine 1 hA jetPoincareCoreT0_two

/-- **Affine GU ⇒ GU of `M(2, 5)`**, conditional only on `hA`. -/
theorem twoSeries_gradedUnitary_M25_of_affine
    (hA : GradedUnitary (affineForm (twoSeriesLevels 1))
      (affineRealStructure (twoSeriesLevels 1)) (affineFlag (twoSeriesLevels 1))) :
    VirGradedUnitary (twoSeriesLevels 1).c (targetRealStructure (twoSeriesLevels 1)) :=
  SliceMap.twoSeries_gradedUnitary_of_affine 0 hA jetPoincareCoreT0_one

/-- **Affine GU ⇒ GU of `M(2, 2m+5)`**, conditional only on `hA` and the arrangement
inclusion `ArrangementInclusion (m + 1)`. -/
theorem twoSeries_gradedUnitary_of_affine_arrangement (m : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels (m + 1)))
      (affineRealStructure (twoSeriesLevels (m + 1))) (affineFlag (twoSeriesLevels (m + 1))))
    (hArr : JetPoincareArr.ArrangementInclusion (m + 1)) :
    VirGradedUnitary (twoSeriesLevels (m + 1)).c (targetRealStructure (twoSeriesLevels (m + 1))) :=
  SliceMap.twoSeries_gradedUnitary_of_affine m hA
    (JetPoincareArr.jetPoincareCoreT0_of_arrangement (by omega) hArr)

end VOA.TwoSeries.JetPoincareTwo
