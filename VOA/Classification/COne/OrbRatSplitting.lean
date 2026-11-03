import VOA.Classification.COne.PlusSplitIntervals
import VOA.Classification.COne.PlusSplitResidual
import VOA.Classification.COne.PlusSplitGeneralized

/-!
# Rationality of a `C₂`-cofinite VOA with semisimple Zhu algebra = resonant splitting

For ANY `C₂`-cofinite VOA `W` whose Zhu algebra `A(W)` is semisimple:

  `AdmissiblyRational W ↔ ResonantWholeSplitting W`

(`admissiblyRational_iff_resonantWholeSplitting`), where `ResonantWholeSplitting W` asks only that
every weak `W`-module of length two whose simple factors have intrinsic lowest generalized weights
`h` (sub) and `k` (quotient) with `k − h` a NONZERO INTEGER splits.

The library's `V_{2m}⁺` machinery proves every ingredient for general `W`:
finite length of cyclic weak modules (`cyclicFiniteLength_of_c2Cofinite`), splitting across
distinct cosets (`relativeComplement_of_nonintegral_factorWeights`), equal-bottom splitting from
Zhu semisimplicity (`relativeComplement_of_semisimpleZhu_equalBottom`), and transport from whole
extensions to arbitrary intervals (`relativeComplement_of_whole_factorBottoms`).  This file only
assembles them uniformly in `W`, and proves the converse direction, so that the residual is an
exact reformulation and not a strengthening.

This is precisely the gap McRae (arXiv:2108.01898v3, §1.3) describes: "a semisimple Zhu algebra does
not directly rule out non-split extensions when the difference between lowest conformal weights is
a non-zero integer".
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat

open VOA VertexOperatorAlgebra
open PlusRational PlusSplitting ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Resonant whole splitting**: every weak `W`-module `X ⊋ P ⊋ 0` with `P` simple and `X/P`
simple, whose intrinsic factor bottoms differ by a nonzero integer, splits.  Both orientations of
the gap are included. -/
def ResonantWholeSplitting (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X)
    (P : Submodule (modeAlg B) X) (h k : ℂ),
    IsAtom P → P ⋖ ⊤ → FactorBottom B ⊥ P h → FactorBottom B P ⊤ k →
    (∃ z : ℤ, z ≠ 0 ∧ k = h + (z : ℂ)) → ∃ Q : Submodule (modeAlg B) X, IsCompl P Q

/-- Every two-step interval in every weak module splits, from the resonant case alone. -/
theorem twoStepSplitting_of_resonantWholeSplitting (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) (hres : ResonantWholeSplitting W)
    {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) :
    TwoStepSplitting (Submodule (modeAlg A) M) := by
  intro a b c hab hbc
  obtain ⟨h, hh⟩ := exists_factorBottom hC2 A hab.lt
  obtain ⟨k, hk⟩ := exists_factorBottom hC2 A hbc.lt
  by_cases hcos : SameCoset h k
  · obtain ⟨z, hz⟩ := hcos
    by_cases hz0 : z = 0
    · have hkh : k = h := by simpa [hz0] using hz
      rw [hkh] at hk
      exact relativeComplement_of_semisimpleZhu_equalBottom hC2 hss A hab hbc h hh hk
    · exact relativeComplement_of_whole_factorBottoms hC2 A hab hbc h k hh hk
        (fun B P hP hQ hb ht => hres B P h k hP hQ hb ht ⟨z, hz0, hz⟩)
  · exact relativeComplement_of_nonintegral_factorWeights A (weakL0LocallyFinite hC2 A)
      hab hbc hh.1 hk.1 hcos

/-- Sufficiency: `C₂` + semisimple Zhu + resonant splitting ⟹ admissibly rational. -/
theorem admissiblyRational_of_resonantWholeSplitting (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) (hres : ResonantWholeSplitting W) :
    AdmissiblyRational W := by
  intro M _ _ N
  apply (isSemisimpleModule_modeAlg_iff N).mp
  have hs := twoStepSplitting_of_resonantWholeSplitting hC2 hss hres N.toWeakModule
  exact semisimple_of_generalized_cyclic_splitting hC2 N.toWeakModule
    (fun _ x _ => twoStepSplitting_submodule hs (cyclic N.toWeakModule x))

/-- Necessity: for `C₂`-cofinite `W`, rationality splits EVERY length-two weak module with
intrinsic factor bottoms (the weak module is regraded as an admissible one at its spectral
bottom). -/
theorem wholeSplitting_of_admissiblyRational (hC2 : C2Cofinite W) (hR : AdmissiblyRational W)
    {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X)
    (P : Submodule (modeAlg B) X) (h k : ℂ)
    (hb : FactorBottom B ⊥ P h) (ht : FactorBottom B P ⊤ k) :
    ∃ Q : Submodule (modeAlg B) X, IsCompl P Q := by
  have hbound : ∀ a, (L0 B).maxGenEigenspace a ≠ ⊥ → min h.re k.re ≤ a.re := by
    intro a ha
    by_cases hp : (L0 B).maxGenEigenspace a ≤ P.restrictScalars ℂ
    · refine min_le_of_left_le (hb.2 a ?_)
      intro he
      apply ha
      apply bot_unique
      intro x hx
      exact he ⟨hp hx, hx⟩
    · refine min_le_of_right_le (ht.2 a ?_)
      simpa only [FactorWeight, Submodule.restrictScalars_top, top_inf_eq] using hp
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, μ.re = min h.re k.re := by
    rcases le_total h.re k.re with hle | hle
    · exact ⟨h, (min_eq_left hle).symm⟩
    · exact ⟨k, (min_eq_right hle).symm⟩
  obtain ⟨N, he, -⟩ := exists_admissible_at_spectral_bottom B
    (weak_spectral_decomposition B (weakL0LocallyFinite hC2 B)) μ
    (fun a ha => hμ ▸ hbound a ha)
  subst he
  letI := (isSemisimpleModule_modeAlg_iff N).mpr (hR N)
  exact exists_isCompl P

theorem resonantWholeSplitting_of_admissiblyRational (hC2 : C2Cofinite W)
    (hR : AdmissiblyRational W) : ResonantWholeSplitting W :=
  fun B P h k _ _ hb ht _ => wholeSplitting_of_admissiblyRational hC2 hR B P h k hb ht

/-- **For every `C₂`-cofinite VOA with semisimple Zhu algebra, admissible rationality is
EXACTLY resonant whole splitting.** -/
theorem admissiblyRational_iff_resonantWholeSplitting (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) :
    AdmissiblyRational W ↔ ResonantWholeSplitting W :=
  ⟨resonantWholeSplitting_of_admissiblyRational hC2,
    admissiblyRational_of_resonantWholeSplitting hC2 hss⟩

end VOA.Classification.COne.OrbRat
