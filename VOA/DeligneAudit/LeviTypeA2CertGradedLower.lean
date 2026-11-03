import VOA.DeligneAudit.LeviConversionBoxTopMain

/-! Graded lower-mode spans for the second-colour box conversion. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V]

/-- The lower terms with the same radical counts and total mode degree as
the target of a second-colour box conversion. -/
def gradedLowerModeSpan (a b : ℕ → A) (xs ys : List ℕ)
    (k d : ℕ) (R : A) (v : V) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ zs bs : List ℕ,
    zs.length = xs.length ∧ bs.length = ys.length + k ∧
      zs.sum + bs.sum = d ∧ zs.sum < xs.sum ∧
      w = (aWord a zs * (bs.map b).prod) • (R • v)}

theorem gradedLowerModeSpan_le (a b : ℕ → A) (xs ys : List ℕ)
    (k d : ℕ) (R : A) (v : V) :
    gradedLowerModeSpan a b xs ys k d R v ≤ lowerModeSpan a b xs R v := by
  apply Submodule.span_mono
  rintro w ⟨zs, bs, _, _, _, hsmall, rfl⟩
  exact ⟨zs, bs, hsmall, rfl⟩

/-- A shifted-current coefficient keeps its number of `b` letters and
adds precisely the coefficient index to the mode sum. -/
theorem coeff_bWord_graded_mem (a b : ℕ → A)
    (xs ys zs l pref : List ℕ) (k s d : ℕ) (R : A) (v : V)
    (hsmall : zs.sum < xs.sum)
    (hlenA : zs.length = xs.length)
    (hlenB : pref.length + l.length = k)
    (hdegree : zs.sum + pref.sum + l.sum + ys.sum + s = d) :
    (aWord a zs * (pref.map b).prod * PowerSeries.coeff s (bWord b l) *
      (ys.map b).prod) • (R • v) ∈
      gradedLowerModeSpan a b xs ys k d R v := by
  induction l generalizing s pref with
  | nil =>
      by_cases hs : s = 0
      · subst s
        have hb : PowerSeries.coeff 0 (bWord b []) = 1 := by simp [bWord]
        simp only [hb, mul_one]
        have heq : (aWord a zs * (pref.map b).prod * (ys.map b).prod) •
            (R • v) = (aWord a zs * ((pref ++ ys).map b).prod) •
              (R • v) := by
          simp [List.map_append, List.prod_append, mul_assoc]
        rw [heq]
        apply Submodule.subset_span
        refine ⟨zs, pref ++ ys, hlenA, ?_, ?_, hsmall, rfl⟩
        · simp only [List.length_nil, add_zero] at hlenB
          simp only [List.length_append]
          omega
        · simp only [List.sum_nil, add_zero] at hdegree
          simp only [List.sum_append]
          omega
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
        intro q _
        simp [bTail, List.map_append, List.prod_append, mul_assoc]
      rw [heq]
      apply (gradedLowerModeSpan a b xs ys k d R v).sum_mem
      intro q hq
      have hqsum := Finset.mem_antidiagonal.mp hq
      have hlen' : (pref ++ [x + q.1]).length + l.length = k := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlenB ⊢
        omega
      have hdegree' :
          zs.sum + (pref ++ [x + q.1]).sum + l.sum + ys.sum + q.2 = d := by
        simp only [List.sum_append, List.sum_cons, List.sum_nil,
          add_zero] at hdegree ⊢
        omega
      exact ih (pref ++ [x + q.1]) q.2 hlen' hdegree'

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.gradedLowerModeSpan_le
#print axioms VOA.DeligneAudit.LeviConversion.coeff_bWord_graded_mem
