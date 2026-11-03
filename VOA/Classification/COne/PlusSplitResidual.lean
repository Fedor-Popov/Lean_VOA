import VOA.Classification.COne.PlusSplitBottom
import VOA.Classification.COne.PlusSplitOrdinary

/-!
# Exact remaining equal-bottom and resonant extension inputs

These are unproved propositions, not axioms or theorems. The conditional
assembly retains arbitrary mode submodules and all Jordan blocks.

References: Abe, https://arxiv.org/html/math/0311210, Theorem 7.1(1)
(Dong--Nagatomo, proof of Theorem 5.13), Proposition 7.2 (equal bottoms),
Propositions 7.3--7.4 and Lemma 7.5 (nonzero integral differences).
Zhu semisimplicity alone is not asserted to settle distinct resonant bottoms.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusSplitting
open PlusRational

/-- Two-step splitting passes to every submodule, including an ungraded one. -/
theorem twoStepSplitting_submodule {R X : Type*} [Ring R] [AddCommGroup X] [Module R X]
    (hs : TwoStepSplitting (Submodule R X)) (P : Submodule R X) :
    TwoStepSplitting (Submodule R P) := by
  intro a b c hab hbc
  obtain ⟨d, had, hdc, hi, hu⟩ := hs _ _ _
    (Submodule.map_covBy_of_injective P.injective_subtype hab)
    (Submodule.map_covBy_of_injective P.injective_subtype hbc)
  have hd : (d.comap P.subtype).map P.subtype = d :=
    Submodule.map_comap_eq_of_le (hdc.trans (by rintro y ⟨x, _, rfl⟩; exact ⟨x, rfl⟩))
  refine ⟨d.comap P.subtype, ?_, ?_, ?_, ?_⟩
  · exact Submodule.map_le_iff_le_comap.mp had
  · have := Submodule.comap_mono (f := P.subtype) hdc
    simpa only [Submodule.comap_map_eq_of_injective P.injective_subtype] using this
  · apply Submodule.map_injective_of_injective P.injective_subtype
    rw [Submodule.map_inf _ P.injective_subtype, hd, hi]
  · apply Submodule.map_injective_of_injective P.injective_subtype
    rw [Submodule.map_sup, hd, hu]

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusRational PlusSplitting ABDWeakAdmissible

/-- OPEN: equal-bottom simple extensions split, including self-extensions and
nonisomorphic simples with coincident numerical weights (Abe Proposition 7.2).
The extension itself is not assumed ordinary. -/
def V2mPlusEqualBottomSplitting : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (N : AdmissibleModule (V2mPlus m hm) M)
      (a b c : Submodule (modeAlg N.toWeakModule) M) (h : ℂ),
      a ⋖ b → b ⋖ c → FactorBottom N.toWeakModule a b h →
      FactorBottom N.toWeakModule b c h →
      ∃ d : Submodule (modeAlg N.toWeakModule) M,
        a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c

/-- OPEN: the distinct integrally resonant case, retaining both orientations.
This includes the vacuum/sign pair (Abe Proposition 7.3) and the remaining
pairs requiring Heisenberg extensions and fusion (Proposition 7.4, Lemma 7.5). -/
def V2mPlusResonantBottomSplitting : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (N : AdmissibleModule (V2mPlus m hm) M)
      (a b c : Submodule (modeAlg N.toWeakModule) M) (h k : ℂ),
      a ⋖ b → b ⋖ c → FactorBottom N.toWeakModule a b h →
      FactorBottom N.toWeakModule b c k →
      (∃ z : ℤ, z ≠ 0 ∧ k = h + (z : ℂ)) →
      ∃ d : Submodule (modeAlg N.toWeakModule) M,
        a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c

/-- The two remaining cases suffice. Bottom existence and the different-coset
case are proved; no classification or ordinary-extension assumption is hidden. -/
theorem generalizedGeneratorSplitting_of_equalBottom_and_resonant
    (heq : V2mPlusEqualBottomSplitting) (hres : V2mPlusResonantBottomSplitting) :
    V2mPlusGeneralizedGeneratorSplittingFactGe2 := by
  intro m hm hm2 M _ _ N α x hx
  apply twoStepSplitting_submodule
  intro a b c hab hbc
  obtain ⟨h, hh⟩ := exists_factorBottom (V2mPlus_c2Cofinite m hm) N.toWeakModule hab.lt
  obtain ⟨k, hk⟩ := exists_factorBottom (V2mPlus_c2Cofinite m hm) N.toWeakModule hbc.lt
  by_cases hcos : SameCoset h k
  · obtain ⟨z, hz⟩ := hcos
    by_cases hz0 : z = 0
    · have hkh : k = h := by simpa [hz0] using hz
      rw [hkh] at hk
      exact heq m hm hm2 N a b c h hab hbc hh hk
    · exact hres m hm hm2 N a b c h k hab hbc hh hk ⟨z, hz0, hz⟩
  · exact relativeComplement_of_nonintegral_factorWeights N.toWeakModule
      (weakL0LocallyFinite (V2mPlus_c2Cofinite m hm) N.toWeakModule)
      hab hbc hh.1 hk.1 hcos

/-- Necessity as well as sufficiency: the residuals lose none of the goal. -/
theorem generalizedGeneratorSplitting_iff_equalBottom_and_resonant :
    V2mPlusGeneralizedGeneratorSplittingFactGe2 ↔
      V2mPlusEqualBottomSplitting ∧ V2mPlusResonantBottomSplitting := by
  refine ⟨?_, fun h => generalizedGeneratorSplitting_of_equalBottom_and_resonant h.1 h.2⟩
  intro hs
  have hall : ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
      ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
        (N : AdmissibleModule (V2mPlus m hm) M),
        TwoStepSplitting (Submodule (modeAlg N.toWeakModule) M) := by
    intro m hm hm2 M _ _ N
    letI := semisimple_of_generalized_cyclic_splitting (V2mPlus_c2Cofinite m hm)
      N.toWeakModule (hs m hm hm2 N)
    exact twoStepSplitting_of_complementedLattice
  constructor
  · intro m hm hm2 M _ _ N a b c h hab hbc _ _
    exact hall m hm hm2 N a b c hab hbc
  · intro m hm hm2 M _ _ N a b c h k hab hbc _ _ _
    exact hall m hm hm2 N a b c hab hbc

/-- OPEN classical algebra input, exactly semisimplicity of the existing Zhu
algebra. Abe Theorem 7.1(1), citing Dong--Nagatomo Theorem 5.13's proof. -/
def ZhuV2mPlusSemisimple : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    letI := instRingA (V2mPlus m hm)
    IsSemisimpleRing (VOA.A (V2mPlus m hm))

/-- OPEN formalization of the equal-bottom lifting argument in Abe 7.2.
It includes control of the bottom of the generated lift. This bridge is
explicitly separate from semisimplicity of the finite-dimensional Zhu algebra. -/
def V2mPlusEqualBottomZhuLifting : Prop :=
  ZhuV2mPlusSemisimple → V2mPlusEqualBottomSplitting

/-- Assembly from the actual Zhu input, its still-unproved equal-bottom
lifting bridge, and the separate resonant extension input. -/
theorem generalizedGeneratorSplitting_of_zhu_lifting_resonant
    (hzhu : ZhuV2mPlusSemisimple) (hlift : V2mPlusEqualBottomZhuLifting)
    (hres : V2mPlusResonantBottomSplitting) :
    V2mPlusGeneralizedGeneratorSplittingFactGe2 :=
  generalizedGeneratorSplitting_of_equalBottom_and_resonant (hlift hzhu) hres

end VOA.Classification.COne
