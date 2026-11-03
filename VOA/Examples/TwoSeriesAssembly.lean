/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodge

/-!
# `GU(L_k(sl₂)) ⇒ GU(L(c))` for every coset level datum, and the `(2, 2n+3)` series

The generalization of `LeeYangShortcutAssembly.leeYang_gradedUnitary_of_affine'` and of the
character bridge `ConcreteHodge.leadingInvariantSymbolDimension_of_bound` to an arbitrary
`L : CosetLevels`, with the two `q`-specific inputs isolated in one structure:

* `BRSTHodgeInputs L` — the level-generic Beem–Garner/Hodge package on the **actual**
  level-`L` relative BRST complexes: Kähler data whose differential is the actual BRST residue,
  positivity derived from `hA` and the (proved) auxiliary GU, `GUData`, the class-filtration
  generator tests, and the three harmonic-metric bridges on the actual universal Virasoro
  classes.  Mathematically independent of `q`; in Lean constructed at every level from `hA`
  alone: `TwoSeries.brstHodgeInputs L hA` (`TwoSeriesHodgeInputs.lean`).  It asserts no positivity,
  nondegeneracy, injectivity or filtered
  isomorphism on the target.
* `SqueezeInput L S` — the purely dimensional, `q`-specific input: an explicit coefficient
  `coeff n r` with
  (I) `dim H(Q⁻)_{(j,0)} ≤ coeff n (j/2)` (zero at odd `j`) for the leading cohomology, and
  (II) `Σ_{r ≤ p} coeff n r ≤ dim F_p L(c)_n` for the PBW filtration of the target.
  At Lee–Yang, `coeff = gapTwoCoefficient` (`z^{r(r+1)}/(z)_r`).

* `cosetLevels_gradedUnitary_of_affine` — for every `L`: `hA ∧ BRSTHodgeInputs ∧ SqueezeInput
  ⇒ VirGradedUnitary L.c`.
* `twoSeries_gradedUnitary_of_affine` — the `(2, 2n+3)` specialization.
-/

namespace VOA.TwoSeries

open VirModule VirSimple VirGoodFil VirQuotForm VirGradedUnitarity Sl2SemiInfinite
open LeeYangShortcut LeeYangTransferAssembly LeeYangCosetTransfer GradedUnitaryCohomology
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

/-- The level-generic BRST/Hodge package on the actual level-`L` relative complexes. -/
structure BRSTHodgeInputs where
  kahler : BRSTKahlerGeometry L
  weakGU : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L) →
    GradedUnitary (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L) →
    ∀ n, IsPosOn (kahler.geometry n).P ⊤
  gu : BRSTGUData L kahler
  generators : ∀ hp : (∀ n, IsPosOn (kahler.geometry n).P ⊤),
    ClassGeneratorFiltration L kahler hp
  vacuumNormalized : HarmonicVacuumNormalized L kahler gu
  creationAdjoint : HarmonicCreationAdjoint L kahler gu
  wordsReal : HarmonicWordsReal L kahler gu

/-- A PBW-length coefficient written in the Kähler coordinate `j = 2R` (zero at odd or negative
`j`). -/
def evenCoeff (a : ℤ → ℕ → ℕ) (n j : ℤ) : ℕ :=
  if 0 ≤ j ∧ j % 2 = 0 then a n (j.toNat / 2) else 0

theorem evenCoeff_odd (a : ℤ → ℕ → ℕ) (n : ℤ) (p : ℕ) : evenCoeff a n (2 * (p : ℤ) + 1) = 0 := by
  unfold evenCoeff
  rw [if_neg]
  omega

/-- The `q`-specific dimension input: an explicit coefficient bounding the leading
(invariant-symbol) cohomology from above and the PBW filtration of `L(c)` from below. -/
structure SqueezeInput (S : BRSTKahlerGeometry L) where
  /-- `coeff n r`: the expected dimension of the PBW-length-`r` layer at weight `n`. -/
  coeff : ℤ → ℕ → ℕ
  /-- (I) leading-cohomology / invariant-symbol upper bound. -/
  invariantBound : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) j,
    Module.finrank ℂ ((S.model n hp).leadCohom (j, 0)) ≤ evenCoeff coeff n j
  /-- (II) PBW lower bound for the simple target. -/
  pbwLower : ∀ (n : ℤ) (p : ℕ),
    (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), evenCoeff coeff n j) ≤
      Module.finrank ℂ ((virGradedFlag L.c).pieceIn p n)

/-- Target conjugation at one weight. -/
def targetRhoWeight (n : ℤ) : TargetWeight L n →ₛₗ[starRingEnd ℂ] TargetWeight L n where
  toFun x := ⟨(targetRealStructure L).rho x, realStructure_mem_grading _ x.property⟩
  map_add' x y := Subtype.ext ((targetRealStructure L).map_add x y)
  map_smul' c x := Subtype.ext ((targetRealStructure L).antilinear c x)

theorem simpleWeightProjection_conj (n : ℤ) (x : UniversalWeight L n) :
    simpleWeightProjection L n (universalConjWeight L n x) =
      targetRhoWeight L n (simpleWeightProjection L n x) :=
  Subtype.ext rfl

theorem universalImage_sesq (S : BRSTKahlerGeometry L) (G : BRSTGUData L S)
    (hm : UniversalImageMetric L S G) (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤)
    (x y : UniversalWeight L n) :
    gradedSesq (Bsimp L.c) (targetRealStructure L) n
        (simpleWeightProjection L n x) (simpleWeightProjection L n y) =
      (G.data n hp).h (S.universalHarmonic n hp x) (S.universalHarmonic n hp y) := by
  rw [(G.data n hp).h_eq, ← hm.rho n hp x, ← hm.form n hp]
  change (Bsimp L.c).form ((targetRealStructure L).rho _) _ =
    (Bsimp L.c).form ((simpleWeightProjection L n (universalConjWeight L n x) :
      VirUniv L.c ⧸ maxIdealVir L.c)) _
  rw [simpleWeightProjection_conj]
  rfl

/-- Lower half of the squeeze (copy of `pieceFinrank_le_cohomFilt`, which lives
downstream of the Lee–Yang-specific chain). -/
theorem pieceFinrank_le_cohomFilt {K : Type*} [AddCommGroup K] [Module ℂ K]
    [FiniteDimensional ℂ K] {U T : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup T] [Module ℂ T]
    (C : KahlerComplex K) (f : U →ₗ[ℂ] cycleQuotient C.D) (g : U →ₗ[ℂ] T)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) (P : Submodule ℂ U) (Q : Submodule ℂ T)
    (hquotient : P.map g = Q) (F : Submodule ℂ (cycleQuotient C.D))
    (hfiltered : P.map f ≤ F) :
    Module.finrank ℂ Q ≤ Module.finrank ℂ F := by
  have hQ : (P.map f.rangeRestrict).map (rangeFactor f g hker) = Q :=
    rangeFactor_prefix f g hker P Q hquotient
  have hsub : (P.map f.rangeRestrict).map (LinearMap.range f).subtype = P.map f := by
    rw [← Submodule.map_comp]
    rfl
  calc Module.finrank ℂ Q
      = Module.finrank ℂ ((P.map f.rangeRestrict).map (rangeFactor f g hker)) := by rw [hQ]
    _ ≤ Module.finrank ℂ (P.map f.rangeRestrict) := Submodule.finrank_map_le _ _
    _ ≤ Module.finrank ℂ F :=
        finrank_le_of_filtered_injective (LinearMap.range f).subtype Subtype.val_injective
          _ F (by rw [hsub]; exact hfiltered)

/-- The squeeze: with the (proved) lower half, the input gives the exact leading character. -/
theorem squeeze_character (S : BRSTKahlerGeometry L) (hsq : SqueezeInput L S)
    (hf : S.UniversalClassFiltered) (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) (p : ℕ) :
    (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)),
        Module.finrank ℂ ((S.model n hp).leadCohom (j, 0))) =
      Module.finrank ℂ ((virGradedFlag L.c).pieceIn p n) := by
  apply le_antisymm
  · exact (Finset.sum_le_sum fun j _ => hsq.invariantBound n hp j).trans (hsq.pbwLower n p)
  · calc Module.finrank ℂ ((virGradedFlag L.c).pieceIn p n)
        ≤ Module.finrank ℂ ((S.model n hp).cohomFilt
            (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)) :=
          pieceFinrank_le_cohomFilt (S.model n hp) (S.modelUniversalClass n hp)
            (simpleWeightProjection L n) (S.modelUniversalClass_ker_le n hp)
            (universalPrefix L p n) _ (simpleWeightProjection_prefix L p n) _ (hf n hp p)
      _ ≤ _ := (S.model n hp).finrank_cohomFilt_row_le_lead _ 0

/-- Odd harmonic degrees vanish because the coefficient is zero there. -/
theorem integralHarmonicSupport_of_squeeze (S : BRSTKahlerGeometry L) (hsq : SqueezeInput L S)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) : IntegralHarmonicSupport (S.model n hp) := by
  intro p
  have hdim := (S.model n hp).finrank_harmDeg_le_lead (2 * (p : ℤ) + 1, 0)
  have hb := hsq.invariantBound n hp (2 * (p : ℤ) + 1)
  rw [evenCoeff_odd] at hb
  exact harmonicDegree_eq_bot (K := relativeWeight L n) (S.model n hp)
    (2 * (p : ℤ) + 1, 0) (Nat.eq_zero_of_le_zero (hdim.trans hb))

/-- **Coset transfer for any level datum.** Graded unitarity of the simple `L_{kA}(sl₂)`
(canonical form, compact conjugation, corrected flag), the level-generic BRST/Hodge package,
and the dimension squeeze input imply graded unitarity of the simple Virasoro VOA `L(c)` with
its partition-basis real structure. -/
theorem cosetLevels_gradedUnitary_of_affine
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hodge : BRSTHodgeInputs L) (hsq : SqueezeInput L hodge.kahler) :
    VirGradedUnitary L.c (targetRealStructure L) := by
  have hpAll := hodge.weakGU hA (auxiliaryGradedUnitary L)
  have hf : hodge.kahler.UniversalClassFiltered :=
    universalClassFiltered_of_generators L hodge.kahler hpAll (hodge.generators hpAll)
  have hm : UniversalImageMetric L hodge.kahler hodge.gu :=
    universalImageMetric_of_invariance L hodge.kahler hodge.gu hpAll
      hodge.vacuumNormalized hodge.creationAdjoint hodge.wordsReal
  intro n
  exact gradedUnitaryAt_of_class_family (K := relativeWeight L n)
    (hodge.kahler.model n (hpAll n)) (hodge.gu.data n (hpAll n)) (virGradedFlag L.c) n
    (LiRadical.gradedForm (Bsimp L.c) n)
    (gradedSesq (Bsimp L.c) (targetRealStructure L) n)
    (hodge.kahler.modelUniversalClass n (hpAll n)) (simpleWeightProjection L n)
    (simpleWeightProjection_surjective L n) (hodge.kahler.modelUniversalClass_ker_le n (hpAll n))
    (fun p => universalPrefix L p n) (fun p => simpleWeightProjection_prefix L p n)
    (universalPrefix_exhaustive L n) (hf n (hpAll n))
    (squeeze_character L hodge.kahler hsq hf n (hpAll n)) (hm.form n (hpAll n))
    (universalImage_sesq L hodge.kahler hodge.gu hm n (hpAll n))
    (integralHarmonicSupport_of_squeeze L hodge.kahler hsq n (hpAll n))

/-- **The `(2, 2n+3)` series.** For `k = -2 + 2/(2n+1)`: graded unitarity of `L_k(sl₂)`, the
level-generic BRST/Hodge package on the actual level-`k` coset complex, and the dimension squeeze
input imply graded unitarity of the minimal model `M(2, 2n+3)`; its central charge is
`(twoSeriesLevels n).c = boundaryCharge (n+1) = 1 - 3(2n+1)²/(2n+3)` (`twoSeriesLevels_c`). -/
theorem twoSeries_gradedUnitary_of_affine (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (hodge : BRSTHodgeInputs (twoSeriesLevels n))
    (hsq : SqueezeInput (twoSeriesLevels n) hodge.kahler) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  cosetLevels_gradedUnitary_of_affine (twoSeriesLevels n) hA hodge hsq

end

end VOA.TwoSeries
