import VOA.Classification.COne.PlusSplitResonantPairs
import VOA.Classification.COne.PlusTwistCharacters

/-! Exact pairwise obligations for the remaining resonant splitting problem.
The propositions below are OPEN. No pairwise extension vanishing is assumed
or asserted as a theorem. Abe, https://arxiv.org/html/math/0311210#S7,
Proposition 7.3 treats vacuum/sign, and Proposition 7.4 and Lemma 7.5 treat
the other resonant modules. Numerical labels here do not identify modules:
each obligation covers every simple factor with the indicated bottom. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusResonantPairs
open PlusCharacterTable PlusSplitting PlusRational
open VOA.Huang.LogRemovalAdmissible

/-- OPEN: splitting for the specified ordered pair of numerical bottoms.
This is a true restriction of whole-extension splitting; it retains all
weak middle modules and does not assume irreducible model identifications. -/
def PairSplitting (m : ℕ) (hm : 1 ≤ m) (i j : Label m) : Prop :=
  ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M),
    IsAtom P → P ⋖ ⊤ →
    FactorBottom A ⊥ P (weight m i : ℂ) →
    FactorBottom A P ⊤ (weight m j : ℂ) →
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q

/-- One named TRUE open proposition for each entry in the computed list.
Both extension orientations are explicitly required. -/
def PairObligation (m : ℕ) (hm : 1 ≤ m)
    (p : {p : Label m × Label m // p ∈ positivePairs m}) : Prop :=
  PairSplitting m hm p.val.1 p.val.2 ∧ PairSplitting m hm p.val.2 p.val.1

/-- The finite family of open obligations, uniformly for m >= 2. -/
def AllPairObligations : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ p : {p : Label m × Label m // p ∈ positivePairs m}, PairObligation m hm p

theorem allPairObligations_iff_cyclicLifts :
    AllPairObligations ↔ V2mPlusResonantCyclicLifts := by
  constructor
  · intro hall m hm hm2 M _ _ A P h k hP hQ hb ht hz
    obtain ⟨i, rfl⟩ := label_of_factorBottom m hm hm2 A ⊥ P bot_le h hb
    obtain ⟨j, rfl⟩ := label_of_factorBottom m hm hm2 A P ⊤ le_top k ht
    apply (exists_cyclic_lift_iff_complement A P hQ _ ht).mpr
    rcases (nonzero_gap_iff m i j).mp hz with hij | hji
    · exact (hall m hm hm2 ⟨(i, j), hij⟩).1 A P hP hQ hb ht
    · exact (hall m hm hm2 ⟨(j, i), hji⟩).2 A P hP hQ hb ht
  · intro hl m hm hm2 p
    have hz := (mem_positivePairs_iff m p.val.1 p.val.2).mp p.property
    obtain ⟨z, hz, he⟩ := hz
    constructor
    · intro M _ _ A P hP hQ hb ht
      apply (exists_cyclic_lift_iff_complement A P hQ _ ht).mp
      exact hl m hm hm2 A P _ _ hP hQ hb ht ⟨z, ne_of_gt hz, he⟩
    · intro M _ _ A P hP hQ hb ht
      apply (exists_cyclic_lift_iff_complement A P hQ _ ht).mp
      exact hl m hm hm2 A P _ _ hP hQ hb ht
        ⟨-z, (reverse_gap (ne_of_gt hz) he).1, (reverse_gap (ne_of_gt hz) he).2⟩

/-- Exact equivalence with the original target, without any unproved
coverage/classification hypothesis or restriction on the gap orientation. -/
theorem allPairObligations_iff_degreeAvoidance :
    AllPairObligations ↔ V2mPlusResonantDegreeAvoidance := by
  rw [allPairObligations_iff_cyclicLifts, resonantDegreeAvoidance_iff_bottomAvoidance,
    resonantCyclicLifts_iff_bottomAvoidance]

theorem rationality_of_allPairObligations (hp : AllPairObligations) :
    V2mPlusRationalFactGe2 :=
  rationality_of_resonantDegreeAvoidance (allPairObligations_iff_degreeAvoidance.mp hp)

/-- Equal numerical rows are already discharged, including both half-lattice signs. -/
theorem pairSplitting_of_equal_weight (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (i j : Label m) (he : weight m i = weight m j) : PairSplitting m hm i j := by
  intro M _ _ A P hP hQ hb ht
  rw [← he] at ht
  exact exists_isCompl_of_semisimpleZhu_equalBottom (V2mPlus_c2Cofinite m hm)
    (V2mPlus_zhuSemisimple m hm hm2) A P hP hQ _ hb ht

theorem half_signs_split (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    PairSplitting m hm (.inr 2) (.inr 3) ∧
      PairSplitting m hm (.inr 3) (.inr 2) := by
  constructor <;> apply pairSplitting_of_equal_weight m hm hm2 <;> rfl

end VOA.Classification.COne.PlusResonantPairs
