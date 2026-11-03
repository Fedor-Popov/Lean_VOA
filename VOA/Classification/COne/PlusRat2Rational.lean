import VOA.Classification.COne.PlusRat2VacuumSign
import VOA.Classification.COne.PlusRatPrime

/-! # The residual after the vacuum/sign pair, for every `m`

`PairSplitting m hm i j` depends only on the two table weights.  Every remaining ordered pair
with weights `(0, 1)` or `(1, 0)` is therefore one of the two vacuum/sign orientations,
proved for every `m ≥ 2` (`PlusRat2VacuumSign`).  This removes, in particular, the weight-one
collisions at `m = 4` (half rows) and `m = k²` (a charged row).

* `RemainingAfterWeightOne`: the named OPEN residual (TRUE by Abe 2005), equivalent to
  `RemainingPairObligations`, and implying `V2mPlusRationalFactGe2`.
* `V2mPlus_stronglyRational_of_noResidual`: per-`m` strong rationality when every remaining
  pair has weights `(0,1)` or `(1,0)`; instance `m = 4` (`V_8⁺`).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat2
open PlusCharacterTable PlusResonantPairs PlusSplitting OrbRat PlusRatSign

variable (m : ℕ) (hm : 1 ≤ m)

/-- `PairSplitting` only sees the two weights. -/
theorem pairSplitting_congr {i i' j j' : Label m} (hi : weight m i = weight m i')
    (hj : weight m j = weight m j') :
    PairSplitting m hm i j ↔ PairSplitting m hm i' j' := by
  unfold PairSplitting
  rw [hi, hj]

/-- The weight pattern of the two vacuum/sign orientations. -/
def IsVacuumSignWeights (p : Label m × Label m) : Prop :=
  (weight m p.1 = 0 ∧ weight m p.2 = 1) ∨ (weight m p.1 = 1 ∧ weight m p.2 = 0)

/-- Every ordered pair with weights `(0,1)` or `(1,0)` splits, for every `m ≥ 2`. -/
theorem pairSplitting_of_vacuumSignWeights (hm2 : 2 ≤ m) (p : Label m × Label m)
    (hp : IsVacuumSignWeights m p) : PairSplitting m hm p.1 p.2 := by
  have h0 : weight m (.inr 0) = 0 := by simp [weight]
  have h1 : weight m (.inr 1) = 1 := by simp [weight]
  have hvs : PairSplitting m hm (.inr 0) (.inr 1) := by
    intro M _ _
    exact pairSplitting_vacuum_sign_sep m hm hm2 (zetaSeparates m hm hm2)
  have hsv : PairSplitting m hm (.inr 1) (.inr 0) := by
    intro M _ _
    exact pairSplitting_sign_vacuum_sep m hm hm2 (zetaSeparates m hm hm2)
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · intro M _ _
    exact (pairSplitting_congr m hm (ha.trans h0.symm) (hb.trans h1.symm)).mpr hvs
  · intro M _ _
    exact (pairSplitting_congr m hm (ha.trans h1.symm) (hb.trans h0.symm)).mpr hsv

/-- Both vacuum/sign orientations, for every `m ≥ 2` (no arithmetic hypothesis). -/
theorem vacuum_sign_both_all (hm2 : 2 ≤ m) :
    PairSplitting m hm (.inr 0) (.inr 1) ∧ PairSplitting m hm (.inr 1) (.inr 0) :=
  ⟨pairSplitting_vacuum_sign_sep m hm hm2 (zetaSeparates m hm hm2),
    pairSplitting_sign_vacuum_sep m hm hm2 (zetaSeparates m hm hm2)⟩

/-- Per-`m` rationality when every remaining pair is of vacuum/sign weight type. -/
theorem V2mPlus_admissiblyRational_of_noResidual (hm2 : 2 ≤ m)
    (h : ∀ p ∈ remainingOrientedPairs m, IsVacuumSignWeights m p) :
    AdmissiblyRational (V2mPlus m hm) :=
  admissiblyRational_of_remaining m hm hm2 fun q hq =>
    pairSplitting_of_vacuumSignWeights m hm hm2 q (h q hq)

/-- Per-`m` strong rationality when every remaining pair is of vacuum/sign weight type. -/
theorem V2mPlus_stronglyRational_of_noResidual (hm2 : 2 ≤ m)
    (h : ∀ p ∈ remainingOrientedPairs m, IsVacuumSignWeights m p) :
    StronglyRational (V2mPlus m hm) :=
  { OrbRat.V2mPlus_stronglyFinite m hm with
    rational := V2mPlus_admissiblyRational_of_noResidual m hm hm2 h }

end VOA.Classification.COne.PlusRat2

namespace VOA.Classification.COne
open PlusCharacterTable PlusResonantPairs PlusRat2

/-- OPEN, TRUE (Abe, Math. Z. 2005, arXiv:math/0311210, §7): every remaining ordered pair
whose weights are not `(0,1)` or `(1,0)`.  Strictly fewer obligations than
`RemainingAfterVacuumSign`; no pair is weakened. -/
def RemainingAfterWeightOne : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ p ∈ remainingOrientedPairs m,
    ¬ IsVacuumSignWeights m p → PairSplitting m hm p.1 p.2

/-- The removal is exact. -/
theorem remainingAfterWeightOne_iff :
    RemainingAfterWeightOne ↔ RemainingPairObligations := by
  constructor
  · intro h m hm hm2 p hp
    by_cases hs : IsVacuumSignWeights m p
    · exact pairSplitting_of_vacuumSignWeights m hm hm2 p hs
    · exact h m hm hm2 p hp hs
  · intro h m hm hm2 p hp _
    exact h m hm hm2 p hp

/-- `V_{2m}⁺` rationality from the reduced residual. -/
theorem rationality_of_remainingAfterWeightOne (h : RemainingAfterWeightOne) :
    V2mPlusRationalFactGe2 :=
  rationality_of_remainingPairObligations (remainingAfterWeightOne_iff.mp h)

end VOA.Classification.COne

namespace VOA.Classification.COne.PlusRat2
open PlusCharacterTable PlusResonantPairs

/-- At `m = 4` every positive integral gap has weights `(0, 1)` (vacuum against sign and the two
half rows). -/
theorem positivePairs_four (i j : Label 4) (h : (i, j) ∈ positivePairs 4) :
    weight 4 i = 0 ∧ weight 4 j = 1 := by
  simp only [positivePairs, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases i with r | i <;> rcases j with t | j
  · fin_cases r <;> fin_cases t
    all_goals (try norm_num [weight] at h)
  · fin_cases r <;> fin_cases j
    all_goals (try norm_num [weight] at h)
  · fin_cases i <;> fin_cases t
    all_goals (try norm_num [weight] at h)
  · fin_cases i <;> fin_cases j
    all_goals (try norm_num [weight] at h)
    all_goals norm_num [weight]

theorem remaining_four :
    ∀ p ∈ remainingOrientedPairs 4, IsVacuumSignWeights 4 p := by
  rintro ⟨i, j⟩ hp
  rcases ((mem_remainingOrientedPairs_iff 4 i j).mp hp).1 with h | h
  · exact Or.inl (positivePairs_four i j h)
  · obtain ⟨h1, h2⟩ := positivePairs_four j i h
    exact Or.inr ⟨h2, h1⟩

/-- **`V_8⁺` (`m = 4`) is strongly rational.**  This is the first `m` where the weight-one
collision (sign and both half rows at weight one) occurs. -/
theorem V2mPlus_stronglyRational_four (hm : 1 ≤ 4) : StronglyRational (V2mPlus 4 hm) :=
  V2mPlus_stronglyRational_of_noResidual 4 hm (by norm_num) remaining_four

end VOA.Classification.COne.PlusRat2
