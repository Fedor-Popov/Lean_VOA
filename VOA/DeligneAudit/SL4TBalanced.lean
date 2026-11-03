import VOA.DeligneAudit.DeligneFusionCVTrunc

/-! # Closed forms of the balanced truncated Weyl bound -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.CVsl2

/-- The balanced bound when every part has size at most two.
The lower cutoff is expressed without rounding: `r ≤ 2 * ν`. -/
theorem bal_prod_two {r ν : ℕ} (hν : 1 ≤ ν) (hlo : ν ≤ r) (hhi : r ≤ 2 * ν) :
    ((bal r ν).map (· + 1)).prod = 3 ^ (r - ν) * 2 ^ (2 * ν - r) := by
  classical
  rcases Classical.em (r = 2 * ν) with he | he
  · subst r
    have hd : 2 * ν / ν = 2 := Nat.mul_div_left _ (by omega)
    have hm : 2 * ν % ν = 0 := Nat.mul_mod_left _ _
    simp [bal, show ¬2 * ν < ν by omega, hd, hm, show 2 * ν - ν = ν by omega]
  · have hd : r / ν = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hm : r % ν = r - ν := by
      have h := Nat.div_add_mod r ν
      rw [hd] at h
      omega
    simp [bal, show ¬r < ν by omega, hd, hm,
      show ν - (r - ν) = 2 * ν - r by omega]

/-- Once the cutoff reaches the weight, the balanced bound is `2 ^ r`. -/
theorem bal_prod_of_weight_le {r ν : ℕ} (h : r ≤ ν) :
    ((bal r ν).map (· + 1)).prod = 2 ^ r := by
  classical
  rcases lt_or_eq_of_le h with hlt | rfl
  · simp [bal, hlt]
  · rcases Classical.em (r = 0) with hr | hr
    · simp [hr, bal]
    · simp [bal, Nat.div_self (show 0 < r by omega)]

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.bal_prod_two
#print axioms VOA.DeligneAudit.SL4T.bal_prod_of_weight_le
