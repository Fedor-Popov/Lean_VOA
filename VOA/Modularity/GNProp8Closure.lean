/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNLevelOne
import VOA.Modularity.GNGradeZero
import VOA.Modularity.ZhuModularityPinned

/-!
# Gaberdiel--Neitzke Proposition 8 and the pinned modularity theorem

The bounded GN invariant retains the word-grade information needed by the outer induction.  Its
lexicographic closure has four cases: grade zero, cutoff zero, the exceptional successor `0 → 1`,
and the uniform positive-cutoff successor.  Forgetting the grade bound gives the original
`GNReach`, and the independently proved Link 0 converts universal reach into strict-decrease
spanning.

The final modularity theorem in this file keeps the regular-bottom projection `Pr` explicit.  A
separate leaf module supplies that projection from the project's canonical PBW principle.

## Main results

* `gnProp8_GNReachBounded` and `gnProp8_GNReach`;
* `strictSpanning_of_C2Cofinite`;
* `simpleAModsRealized_of_C2Cofinite`;
* `zhuModularity_pinned_of_C2Cofinite`, with its family and conformal weights pinned in the
  conclusion.
-/

namespace VOA

open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Gaberdiel--Neitzke Proposition 8, strengthened induction form.**  Every grade filtration is
contained in the grade-bounded ordered generator span at every repetition cutoff. -/
theorem gnProp8_GNReachBounded (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W) :
    ∀ G N, GNReachBounded W gen wt G N := by
  apply gnLexInduction
  intro G N hOuter hInner
  by_cases hG0 : G = 0
  · subst G
    exact gnReachBounded_grade_zero W gen wt hgen hwt hdec N
  · cases N with
    | zero =>
        exact gnLink2_GNReachBounded_zero W gen wt hgen hwt hdec G
          (fun G' hG' => hOuter G' 0 hG')
    | succ N =>
        have hR : GNReachBounded W gen wt G N := hInner N (by omega)
        cases N with
        | zero =>
            exact gnLevelOne_GNReachBounded_succ W hgen hwt hdec hR
              (fun G' hG' => hOuter G' 1 hG')
        | succ N =>
            exact gnLink4_GNReachBounded_succ_of_repeatedHead_pos W hgen hwt hdec
              (N := N + 1) (by omega) hR
              (fun G' hG' => hOuter G' (N + 1 + 1) hG')

/-- The original, unbounded formulation of Gaberdiel--Neitzke Proposition 8. -/
theorem gnProp8_GNReach (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W) :
    ∀ G N, GNReach W gen wt G N :=
  fun G N => (gnProp8_GNReachBounded W gen wt hgen hwt hdec G N).toGNReach

/-- `C₂`-cofiniteness supplies a nonempty strict-decrease spanning package.  The intermediate
`Nonempty` is necessary because `StrictSpanning W` is data in `Type`, while the finite homogeneous
generator extraction is existential data in `Prop`. -/
theorem nonempty_strictSpanning_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) : Nonempty (StrictSpanning W) := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  exact ⟨strictSpanning_of_GNReachBounded W gen wt hgen hwt
    (gnProp8_GNReachBounded W gen wt hgen hwt hdec)⟩

/-- **GN Proposition 8 from `C₂`-cofiniteness.** -/
noncomputable def strictSpanning_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) : StrictSpanning W :=
  Classical.choice (nonempty_strictSpanning_of_C2Cofinite W hC2)

/-- Every simple Zhu-algebra module is realized by a lowest-weight module under `C₂`-cofiniteness
and the displayed regular-bottom projection. -/
theorem simpleAModsRealized_of_C2Cofinite {W : VertexOperatorAlgebra 𝒱}
    (hC2 : C2Cofinite W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    SimpleAModsRealized W :=
  simpleAModsRealized_of_strictSpanning hC2 Pr
    (strictSpanning_of_C2Cofinite W hC2)

section Pinned

variable {W : VertexOperatorAlgebra 𝒱}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pinned Zhu modularity from `C₂`-cofiniteness.**  The explicit projection form is independent
of the PBW theorem `VOA.pbw`: `Pr` is ordinary carried data, and
the conclusion identifies the resulting modular datum with the supplied module family and conformal
weights.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem zhuModularity_pinned_of_C2Cofinite [Finite (Φ W)]
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ D : ModularData W ι, D.Mfam = Mfam ∧ D.h = h ∧ ZhuModularityAnalytic D :=
  zhuModularity_pinned_of_strictSpanning Mfam h hC2 hss Pr
    (strictSpanning_of_C2Cofinite W hC2) hcard hcw hsep

end Pinned

end VOA
