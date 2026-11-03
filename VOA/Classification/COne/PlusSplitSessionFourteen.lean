import VOA.Classification.COne.PlusSplitVacuumPairs
import VOA.Classification.COne.PlusSplitRelationObstruction

/-! Exact remaining ordered obligations after the vacuum-quotient family.
The finite filter removes only the ordered statements proved in this file.
Neither vacuum/sign nor a two-sided positive-gap obligation is declared solved. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.PlusResonantPairs
open PlusCharacterTable

/-- Both extension orientations of the positive integral gaps. -/
def orientedPairs (m : ℕ) : Finset (Label m × Label m) :=
  positivePairs m ∪ (positivePairs m).image Prod.swap

/-- The exact residual list: remove vacuum quotients whose kernel bottom is > 1. -/
def remainingOrientedPairs (m : ℕ) : Finset (Label m × Label m) :=
  (orientedPairs m).filter fun p => ¬(p.2 = .inr 0 ∧ 1 < weight m p.1)

theorem mem_remainingOrientedPairs_iff (m : ℕ) (i j : Label m) :
    (i, j) ∈ remainingOrientedPairs m ↔
      ((i, j) ∈ positivePairs m ∨ (j, i) ∈ positivePairs m) ∧
        ¬(j = .inr 0 ∧ 1 < weight m i) := by
  have hs : (i, j) ∈ (positivePairs m).image Prod.swap ↔ (j, i) ∈ positivePairs m := by
    constructor
    · intro h
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
      have he' := congrArg Prod.swap he
      simp only [Prod.swap_swap, Prod.swap_prod_mk] at he'
      rwa [he'] at hp
    · intro h
      exact Finset.mem_image.mpr ⟨(j, i), h, rfl⟩
  simp only [remainingOrientedPairs, Finset.mem_filter, orientedPairs, Finset.mem_union, hs]

/-- The named TRUE residual retains every unsolved orientation. -/
def RemainingPairObligations : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ p ∈ remainingOrientedPairs m,
    PairSplitting m hm p.1 p.2

theorem remainingPairObligations_iff_allPairObligations :
    RemainingPairObligations ↔ AllPairObligations := by
  constructor
  · intro h m hm hm2 p
    have solve : ∀ i j : Label m,
        ((i, j) ∈ positivePairs m ∨ (j, i) ∈ positivePairs m) →
          PairSplitting m hm i j := by
      intro i j hij
      by_cases hv : j = .inr 0 ∧ 1 < weight m i
      · rw [hv.1]
        exact pairSplitting_vacuum_quotient_of_gt_one m hm hm2 i hv.2
      · exact h m hm hm2 (i, j) ((mem_remainingOrientedPairs_iff m i j).mpr ⟨hij, hv⟩)
    exact ⟨solve _ _ (Or.inl p.property), solve _ _ (Or.inr p.property)⟩
  · intro h m hm hm2 p hp
    rcases ((mem_remainingOrientedPairs_iff m p.1 p.2).mp hp).1 with hp | hp
    · exact (h m hm hm2 ⟨p, hp⟩).1
    · exact (h m hm hm2 ⟨p.swap, hp⟩).2

theorem rationality_of_remainingPairObligations (h : RemainingPairObligations) :
    V2mPlusRationalFactGe2 :=
  rationality_of_allPairObligations (remainingPairObligations_iff_allPairObligations.mp h)

/-- A concrete resonant half-lattice family: the gap is two at m = 8. -/
theorem half_eight_vacuum_quotient_split (hm : 1 ≤ 8) :
    PairSplitting 8 hm (.inr 2) (.inr 0) ∧
      PairSplitting 8 hm (.inr 3) (.inr 0) :=
  half_vacuum_quotient_split 8 hm (by norm_num)

/-- A concrete resonant charged family: physical charge 16 has weight two at m = 32. -/
theorem charged_thirtytwo_vacuum_quotient_split (hm : 1 ≤ 32) :
    PairSplitting 32 hm (.inl ⟨15, by omega⟩) (.inr 0) :=
  charged_vacuum_quotient_split 32 hm (by norm_num) ⟨15, by omega⟩ (by norm_num)

theorem remainingOrientedPairs_two :
    remainingOrientedPairs 2 = {(.inr 0, .inr 1), (.inr 1, .inr 0)} := by
  ext ⟨i, j⟩
  rw [mem_remainingOrientedPairs_iff, positivePairs_two]
  simp only [Finset.mem_singleton, Finset.mem_insert, Prod.mk.injEq]
  constructor
  · tauto
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [weight]

end VOA.Classification.COne.PlusResonantPairs
