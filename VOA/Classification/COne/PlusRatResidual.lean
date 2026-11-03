import VOA.Classification.COne.PlusRatReverse

/-! # The residual list after the vacuum/sign pair

* `onlySignWeightOne_of`: a decidable sufficient criterion (`m ≠ 4`, `4m` not the square of a
  charge `r < m`).  It fails exactly for `m = 4` (half-lattice rows of weight one) and for
  `m = k²`, `k ≥ 3` (a charged row of weight one).
* `remainingPairObligations_two`: for `m = 2` every remaining ordered obligation of
  `RemainingPairObligations` is proved.
* `RemainingAfterVacuumSign`: the named OPEN (TRUE, Abe 2005) residual, equal to
  `RemainingPairObligations` with both vacuum/sign orientations removed at every `m` with
  `OnlySignWeightOne m`; it is equivalent to `RemainingPairObligations` and implies
  `V2mPlusRationalFactGe2`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRatSign
open PlusCharacterTable PlusResonantPairs

/-- A decidable criterion for `OnlySignWeightOne`. -/
theorem onlySignWeightOne_of (m : ℕ) (h4 : m ≠ 4) (hsq : ∀ r : ℕ, r < m → r ^ 2 ≠ 4 * m) :
    OnlySignWeightOne m := by
  intro i hw
  rcases i with r | i
  · exfalso
    simp only [weight] at hw
    have hm0 : (m : ℚ) ≠ 0 := by
      rintro h
      have : m = 0 := by exact_mod_cast h
      subst this
      simp at hw
    have he : ((r.val : ℚ) + 1) ^ 2 = 4 * m := by
      field_simp at hw
      linarith
    have he' : (r.val + 1) ^ 2 = 4 * m := by exact_mod_cast he
    exact hsq (r.val + 1) (by have := r.isLt; omega) he'
  · fin_cases i
    · simp [weight] at hw
    · rfl
    all_goals
      exfalso
      simp [weight] at hw
    all_goals
      have : (m : ℚ) = 4 := by linarith
      exact h4 (by exact_mod_cast this)

theorem onlySignWeightOne_two : OnlySignWeightOne 2 :=
  onlySignWeightOne_of 2 (by norm_num) (by intro r hr; interval_cases r <;> norm_num)

/-- **For `m = 2` every remaining ordered obligation is proved.** -/
theorem remainingPairObligations_two (hm : 1 ≤ 2) :
    ∀ p ∈ remainingOrientedPairs 2, PairSplitting 2 hm p.1 p.2 := by
  intro p hp
  rw [remainingOrientedPairs_two] at hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact pairSplitting_vacuum_sign 2 hm le_rfl onlySignWeightOne_two
  · rw [Finset.mem_singleton.mp hp]
    exact pairSplitting_sign_vacuum 2 hm le_rfl onlySignWeightOne_two

end VOA.Classification.COne.PlusRatSign

namespace VOA.Classification.COne
open PlusCharacterTable PlusResonantPairs PlusRatSign

/-- OPEN, TRUE (Abe, Math. Z. 2005, arXiv:math/0311210, §7): every remaining ordered pair
except the two vacuum/sign orientations at those `m` whose only weight-one row is the sign
row.  Strictly fewer obligations than `RemainingPairObligations`; no pair is weakened. -/
def RemainingAfterVacuumSign : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ p ∈ remainingOrientedPairs m,
    ¬ (OnlySignWeightOne m ∧ (p = (.inr 0, .inr 1) ∨ p = (.inr 1, .inr 0))) →
    PairSplitting m hm p.1 p.2

/-- The removal is exact: the residual is equivalent to the previous one. -/
theorem remainingAfterVacuumSign_iff :
    RemainingAfterVacuumSign ↔ RemainingPairObligations := by
  constructor
  · intro h m hm hm2 p hp
    by_cases hs : OnlySignWeightOne m ∧ (p = (.inr 0, .inr 1) ∨ p = (.inr 1, .inr 0))
    · obtain ⟨hw1, hp' | hp'⟩ := hs
      · rw [hp']; exact pairSplitting_vacuum_sign m hm hm2 hw1
      · rw [hp']; exact pairSplitting_sign_vacuum m hm hm2 hw1
    · exact h m hm hm2 p hp hs
  · intro h m hm hm2 p hp _
    exact h m hm hm2 p hp

/-- **`V_{2m}⁺` rationality from the reduced residual.** -/
theorem rationality_of_remainingAfterVacuumSign (h : RemainingAfterVacuumSign) :
    V2mPlusRationalFactGe2 :=
  rationality_of_remainingPairObligations (remainingAfterVacuumSign_iff.mp h)

end VOA.Classification.COne
