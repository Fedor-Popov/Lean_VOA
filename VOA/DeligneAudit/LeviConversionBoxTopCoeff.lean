import VOA.DeligneAudit.LeviConversionBoxTopZero

/-! Expand a contracted current coefficient into ordered mode products. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [AddCommGroup V]
  [Module A V] [Module ℂ V]

/-- A coefficient of any ordered product of shifted `b` currents contributes
only ordinary `b` words.  No commutation among the `b` modes is used. -/
theorem coeff_bWord_lower_mem (a b : ℕ → A) (xs zs l pref ys : List ℕ)
    (R : A) (v : V) (hsmall : zs.sum < xs.sum) (s : ℕ) :
    (aWord a zs * (pref.map b).prod * PowerSeries.coeff s (bWord b l) *
      (ys.map b).prod) • (R • v) ∈ lowerModeSpan a b xs R v := by
  induction l generalizing s pref with
  | nil =>
    by_cases hs : s = 0
    · subst s
      have hb : PowerSeries.coeff 0 (bWord b []) = 1 := by simp [bWord]
      simp only [hb, mul_one]
      have heq : (aWord a zs * (pref.map b).prod * (ys.map b).prod) •
          (R • v) =
          (aWord a zs * ((pref ++ ys).map b).prod) • (R • v) := by
        simp [List.map_append, List.prod_append, mul_assoc]
      rw [heq]
      exact Submodule.subset_span ⟨zs, pref ++ ys, hsmall, rfl⟩
    · have hb : PowerSeries.coeff s (bWord b []) = 0 := by simp [bWord, hs]
      simp [hb]
  | cons x l ih =>
    have hb : bWord b (x :: l) = bTail b x * bWord b l := rfl
    rw [hb, PowerSeries.coeff_mul]
    have heq :
        (aWord a zs * (pref.map b).prod *
          (∑ q ∈ Finset.antidiagonal s,
            PowerSeries.coeff q.1 (bTail b x) *
              PowerSeries.coeff q.2 (bWord b l)) * (ys.map b).prod) •
          (R • v) =
        ∑ q ∈ Finset.antidiagonal s,
          (aWord a zs * ((pref ++ [x + q.1]).map b).prod *
            PowerSeries.coeff q.2 (bWord b l) * (ys.map b).prod) •
            (R • v) := by
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro q hq
      simp [bTail, List.map_append, List.prod_append, mul_assoc]
    rw [heq]
    apply (lowerModeSpan a b xs R v).sum_mem
    intro q hq
    exact ih (pref ++ [x + q.1]) q.2

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.coeff_bWord_lower_mem
