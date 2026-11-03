import VOA.DeligneAudit.D4LeviKSMixedHsymmEvaluation

/-! Coefficients of a list of differently coloured currents. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion

theorem mixed_current_coeff_allocations {A : Type*} [Ring A]
    (bs : List (ℕ → A)) (s : ℕ) :
    PowerSeries.coeff s ((bs.map fCurrent).prod) =
      ((modeAllocations (List.replicate bs.length 0) s).map fun modes =>
        ((bs.zip modes).map fun p => p.1 p.2).prod).sum := by
  induction bs generalizing s with
  | nil =>
      by_cases hs : s = 0 <;> simp [modeAllocations, hs]
  | cons b bs ih =>
      simp only [List.map_cons, List.prod_cons, PowerSeries.coeff_mul,
        fCurrent, PowerSeries.coeff_mk, List.length_cons,
        List.replicate_succ, modeAllocations, zero_add,
        List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map]
      conv =>
        lhs
        rw [← (Finset.antidiagonal s).toList_toFinset,
          List.sum_toFinset _ (Finset.nodup_toList _)]
      congr 1
      apply List.map_congr_left
      intro q hq
      simp only [Function.comp_def, List.map_map, List.zip_cons_cons,
        List.map_cons, List.prod_cons, List.sum_map_mul_left, ← ih]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.mixed_current_coeff_allocations
