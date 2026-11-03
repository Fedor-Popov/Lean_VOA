import VOA.Classification.COne.OrbC2hSingle
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2h
open PlusC2Eval

theorem count_intRange (n : ℕ) (lo s : ℤ) :
    (intRange lo n).count s = if lo ≤ s ∧ s < lo+(n:ℤ) then 1 else 0 := by
  induction n generalizing lo with
  | zero => simp [intRange]
  | succ n ih =>
    rw [intRange, List.count_cons, ih]
    by_cases h : s = lo
    · subst lo
      simp
    · simp only [beq_iff_eq, if_neg (Ne.symm h), add_zero]
      split_ifs <;> omega

theorem single_range_count (i w : ℕ) (s : ℤ) :
    ((intRange (-((i+1+w : ℕ) : ℤ))
      ((max (-1) ((w:ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).count s) =
      if -((i+1+w:ℕ):ℤ) ≤ s then 1 else 0 := by
  rw [count_intRange]
  have hm : -1 ≤ max (-1) ((w:ℤ)+s) := le_max_left _ _
  have hs : (w:ℤ)+s ≤ max (-1) ((w:ℤ)+s) := le_max_right _ _
  rw [Int.toNat_of_nonneg (by omega)]
  split_ifs <;> omega
end VOA.Classification.COne.OrbC2h
