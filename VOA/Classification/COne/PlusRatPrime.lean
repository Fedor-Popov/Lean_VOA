import VOA.Classification.COne.PlusRatResidual
import VOA.Classification.COne.OrbRatZhu

/-! # Unconditional rationality of `V_{2p}⁺` for `p = 2` and every odd prime `p`

For a fixed `m`, rationality of `V_{2m}⁺` follows from the ordered obligations of that single
`m` (`admissiblyRational_of_remaining`, via the proved reduction
`admissiblyRational_iff_resonantWholeSplitting`).

For `m = p` an odd prime, the only positive integral gap in the character table is
vacuum/sign (`positivePairs_prime`): with `a, b ∈ [1, p-1]`,
* `p ∣ 4a²` is impossible, which removes every charged/neutral gap;
* `b² - a² = 4pz` forces `a + b = p` and `b - a = 4z`, contradicting the parity of `p`;
* the neutral rows `0, 1, p/4, p/4, 1/16, 9/16, 1/16, 9/16` have only the gap `1 - 0`.
Both vacuum/sign orientations are proved in `PlusRatVacuumSign`/`PlusRatReverse`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRatSign
open PlusCharacterTable PlusResonantPairs PlusSplitting OrbRat

/-! ## §1  Rationality from the obligations of one `m` -/

theorem resonantWholeSplitting_of_remaining (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (h : ∀ q ∈ remainingOrientedPairs m, PairSplitting m hm q.1 q.2) :
    ResonantWholeSplitting (V2mPlus m hm) := by
  intro X _ _ B P hh kk hP hQ hb ht hz
  obtain ⟨i, rfl⟩ := label_of_factorBottom m hm hm2 B ⊥ P bot_le hh hb
  obtain ⟨j, rfl⟩ := label_of_factorBottom m hm hm2 B P ⊤ le_top kk ht
  have hij := (nonzero_gap_iff m i j).mp hz
  by_cases hv : j = .inr 0 ∧ 1 < weight m i
  · obtain ⟨rfl, hgt⟩ := hv
    exact pairSplitting_vacuum_quotient_of_gt_one m hm hm2 i hgt B P hP hQ hb ht
  · exact h (i, j) ((mem_remainingOrientedPairs_iff m i j).mpr ⟨hij, hv⟩) B P hP hQ hb ht

/-- Rationality of a single `V_{2m}⁺` from that `m`'s remaining obligations. -/
theorem admissiblyRational_of_remaining (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (h : ∀ q ∈ remainingOrientedPairs m, PairSplitting m hm q.1 q.2) :
    AdmissiblyRational (V2mPlus m hm) :=
  (admissiblyRational_iff_resonantWholeSplitting (V2mPlus_c2Cofinite m hm)
    (V2mPlus_zhuSemisimple m hm hm2)).mpr (resonantWholeSplitting_of_remaining m hm hm2 h)

/-- If the only positive integral gap is vacuum/sign and only the sign row has weight one,
`V_{2m}⁺` is rational. -/
theorem admissiblyRational_of_onlyVacuumSign (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (hw1 : OnlySignWeightOne m)
    (hpp : ∀ i j : Label m, (i, j) ∈ positivePairs m → i = .inr 0 ∧ j = .inr 1) :
    AdmissiblyRational (V2mPlus m hm) := by
  apply admissiblyRational_of_remaining m hm hm2
  rintro ⟨i, j⟩ hq
  rcases ((mem_remainingOrientedPairs_iff m i j).mp hq).1 with h | h
  · obtain ⟨rfl, rfl⟩ := hpp i j h
    exact pairSplitting_vacuum_sign m hm hm2 hw1
  · obtain ⟨rfl, rfl⟩ := hpp j i h
    exact pairSplitting_sign_vacuum m hm hm2 hw1

/-! ## §2  Number theory of the table at an odd prime -/

section Prime
variable (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)

include hp hp2 in
theorem prime_odd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)

include hp hp2 in
/-- `p ∤ 4a²` for `0 < a < p`. -/
theorem not_dvd_four_sq {a : ℕ} (ha0 : 0 < a) (hap : a < p) : ¬ (p : ℤ) ∣ 4 * (a : ℤ) ^ 2 := by
  intro h
  have h' : p ∣ 4 * a ^ 2 := by exact_mod_cast h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h4 | ha
  · have hle := Nat.le_of_dvd (by norm_num) h4
    have h2 := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · omega
    · exact absurd hp (by decide)
  · have := Nat.le_of_dvd ha0 (hp.dvd_of_dvd_pow ha)
    omega

include hp hp2 in
/-- No integral gap between two charged rows. -/
theorem no_charged_gap {a b : ℕ} (ha0 : 0 < a) (hap : a < p) (hb0 : 0 < b) (hbp : b < p)
    {z : ℤ} (hz : z ≠ 0) (he : (b : ℤ) ^ 2 - (a : ℤ) ^ 2 = 4 * p * z) : False := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hprod : (p : ℤ) ∣ ((b : ℤ) - a) * ((b : ℤ) + a) :=
    ⟨4 * z, by linear_combination he⟩
  have hodd := prime_odd p hp hp2
  rcases hpr.dvd_or_dvd hprod with h | h
  · have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    have hba : (b : ℤ) = a := by linarith
    rw [hba, sub_self] at he
    have : (4 * (p : ℤ)) * z = 0 := by linarith
    rcases mul_eq_zero.mp this with h4 | h4
    · omega
    · exact hz h4
  · have h' : (p : ℤ) ∣ ((b : ℤ) + a) - p := dvd_sub h dvd_rfl
    have h0 := Int.eq_zero_of_abs_lt_dvd h' (by rw [abs_lt]; constructor <;> omega)
    have hsum : (b : ℤ) + a = p := by linarith
    have he2 : (p : ℤ) * ((b : ℤ) - a) = (p : ℤ) * (4 * z) := by
      linear_combination he - ((b : ℤ) - a) * hsum
    have hdiff := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) he2
    omega

/-- The neutral rows, scaled by 16. -/
def neutral16 (q : ℕ) : Fin 8 → ℤ := ![0, 16, 4 * q, 4 * q, 1, 9, 1, 9]

theorem weight_inr (q : ℕ) (i : Fin 8) :
    weight q (.inr i) = (neutral16 q i : ℚ) / 16 := by
  fin_cases i <;> simp [weight, neutral16] <;> ring

include hp hp2 in
/-- At an odd prime the only positive integral gap is vacuum/sign. -/
theorem positivePairs_prime (i j : Label p) (hij : (i, j) ∈ positivePairs p) :
    i = .inr 0 ∧ j = .inr 1 := by
  obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff p i j).mp hij
  have heq : weight p j = weight p i + (z : ℚ) := by
    have : ((weight p j : ℚ) : ℂ) = ((weight p i + (z : ℚ) : ℚ) : ℂ) := by
      push_cast; exact he
    exact_mod_cast this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : 0 < p := hp.pos
  rcases i with r | i <;> rcases j with s | j
  · exfalso
    simp only [weight] at heq
    have hzq : (((s.val + 1 : ℕ) : ℤ) ^ 2 - ((r.val + 1 : ℕ) : ℤ) ^ 2 : ℚ) = 4 * p * z := by
      field_simp at heq
      push_cast
      linear_combination heq
    have hzz : ((s.val + 1 : ℕ) : ℤ) ^ 2 - ((r.val + 1 : ℕ) : ℤ) ^ 2 = 4 * p * z := by
      exact_mod_cast hzq
    exact no_charged_gap p hp hp2 (by omega) (by have := r.isLt; omega) (by omega)
      (by have := s.isLt; omega) (ne_of_gt hz) hzz
  · exfalso
    rw [weight_inr] at heq
    simp only [weight] at heq
    have hzq : ((p : ℤ) * neutral16 p j - 4 * ((r.val + 1 : ℕ) : ℤ) ^ 2 : ℚ) =
        ((16 * p * z : ℤ) : ℚ) := by
      field_simp at heq
      push_cast
      linear_combination (1 / 4 : ℚ) * heq
    have hzz : (p : ℤ) * neutral16 p j - 4 * ((r.val + 1 : ℕ) : ℤ) ^ 2 = 16 * p * z := by
      exact_mod_cast hzq
    apply not_dvd_four_sq p hp hp2 (a := r.val + 1) (by omega) (by have := r.isLt; omega)
    exact ⟨neutral16 p j - 16 * z, by linear_combination -hzz⟩
  · exfalso
    rw [weight_inr] at heq
    simp only [weight] at heq
    have hzq : (4 * ((s.val + 1 : ℕ) : ℤ) ^ 2 - (p : ℤ) * neutral16 p i : ℚ) =
        ((16 * p * z : ℤ) : ℚ) := by
      field_simp at heq
      push_cast
      linear_combination (1 / 4 : ℚ) * heq
    have hzz : 4 * ((s.val + 1 : ℕ) : ℤ) ^ 2 - (p : ℤ) * neutral16 p i = 16 * p * z := by
      exact_mod_cast hzq
    apply not_dvd_four_sq p hp hp2 (a := s.val + 1) (by omega) (by have := s.isLt; omega)
    exact ⟨neutral16 p i + 16 * z, by linear_combination hzz⟩
  · rw [weight_inr, weight_inr] at heq
    have hzz : neutral16 p j = neutral16 p i + 16 * z := by
      have : ((neutral16 p j : ℤ) : ℚ) = ((neutral16 p i + 16 * z : ℤ) : ℚ) := by
        push_cast; linear_combination 16 * heq
      exact_mod_cast this
    have hodd := prime_odd p hp hp2
    fin_cases i <;> fin_cases j <;> simp [neutral16] at hzz ⊢ <;> omega

include hp hp2 in
theorem onlySignWeightOne_prime : OnlySignWeightOne p := by
  apply onlySignWeightOne_of p
  · intro h4; subst h4; exact absurd hp (by decide)
  · intro r hr he
    have hdvd : p ∣ r ^ 2 := ⟨4, by rw [he]; ring⟩
    have hpr := hp.dvd_of_dvd_pow hdvd
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; have := hp.pos; omega
    · have := Nat.le_of_dvd h0 hpr; omega

include hp hp2 in
/-- **`V_{2p}⁺` is rational for every odd prime `p`.** -/
theorem V2mPlus_admissiblyRational_prime (hp1 : 1 ≤ p) :
    AdmissiblyRational (V2mPlus p hp1) :=
  admissiblyRational_of_onlyVacuumSign p hp1 hp.two_le (onlySignWeightOne_prime p hp hp2)
    (positivePairs_prime p hp hp2)

end Prime

/-- **`V_4⁺` (`m = 2`) is rational.** -/
theorem V2mPlus_admissiblyRational_two (hm : 1 ≤ 2) : AdmissiblyRational (V2mPlus 2 hm) :=
  admissiblyRational_of_remaining 2 hm le_rfl (remainingPairObligations_two hm)

/-- **Strong rationality** of `V_{2p}⁺` for `p = 2` and every odd prime `p`. -/
theorem V2mPlus_stronglyRational_prime (p : ℕ) (hp : p.Prime) (hp1 : 1 ≤ p) :
    StronglyRational (V2mPlus p hp1) := by
  by_cases hp2 : p = 2
  · subst hp2
    exact { OrbRat.V2mPlus_stronglyFinite 2 hp1 with
      rational := V2mPlus_admissiblyRational_two hp1 }
  · exact { OrbRat.V2mPlus_stronglyFinite p hp1 with
      rational := V2mPlus_admissiblyRational_prime p hp hp2 hp1 }

end VOA.Classification.COne.PlusRatSign
