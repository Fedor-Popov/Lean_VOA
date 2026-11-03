import VOA.Huang.VerlindeRhoConjugation

/-! # The scalar binomial calculation for coordinate reflection -/

namespace VOA.Huang.VerlindeRho
open VOA
open scoped BigOperators

theorem reflectionCoeff_zero : reflectionCoeff 0 = 1 := sqBracketCoeff_zero_diag

theorem reflectionCoeff_succ (a : ℕ) :
    reflectionCoeff (a + 1) = (-1 : ℂ) ^ a / (((a : ℂ) + 1) * (a + 2)) := by
  unfold reflectionCoeff
  change sqBracketCoeffZ 2 (0 + 1) (((a + 1 : ℕ) : ℤ) + 1) = _
  rw [sqBracketCoeffZ_two_eq_coeff_Pw,
    if_pos (by omega), sub_zero, Int.toNat_natCast]
  simp only [Pw, zero_add, zpow_one, uUnit_coe, add_mul, one_mul, map_add,
    PowerSeries.coeff_succ_X_mul, uSeries, PowerSeries.coeff_mk]
  have h1 : (a : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : a + 1 ≠ 0)
  have h2 : (a : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : a + 2 ≠ 0)
  push_cast
  rw [show (a : ℂ) + 1 + 1 = a + 2 by ring]
  rw [pow_succ]
  field_simp [h1, h2]
  ring

/-- An alternating beta sum, proved by Pascal recursion. -/
theorem alternating_beta_sum (n t : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
      ((-1 : ℂ) ^ j / (((j : ℂ) + t + 1) * (j + t + 2))) =
    ((n + 1).factorial : ℂ) * t.factorial / ((n + t + 2).factorial : ℂ) := by
  induction n generalizing t with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one,
      one_mul, pow_zero, Nat.cast_zero, Nat.factorial_one]
    rw [show t + 2 = (t + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hf : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
    field_simp
    ring_nf
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega,
      Finset.sum_choose_succ_mul (fun j _ =>
        (-1 : ℂ) ^ j / (((j : ℂ) + t + 1) * (j + t + 2))) n]
    have hs : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
        ((-1 : ℂ) ^ (j + 1) / (((j + 1 : ℕ) : ℂ) + t + 1) /
          (((j + 1 : ℕ) : ℂ) + t + 2))) =
        -(∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
          ((-1 : ℂ) ^ j / (((j : ℂ) + (t + 1 : ℕ) + 1) *
            (j + (t + 1 : ℕ) + 2)))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      simp only [div_div]
      rw [pow_succ]
      ring
    simp_rw [← div_div] at ⊢
    rw [hs]
    simp_rw [div_div]
    rw [ih t, ih (t + 1)]
    rw [show n + 1 + t + 2 = (n + t + 2) + 1 by omega,
      show n + (t + 1) + 2 = (n + t + 2) + 1 by omega,
      Nat.factorial_succ (n + t + 2), Nat.factorial_succ (n + 1), Nat.factorial_succ t]
    have hf : ((n + t + 2).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n + t + 2)
    have hnt : ((n + t + 2 : ℕ) : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (by omega : n + t + 2 + 1 ≠ 0)
    push_cast at hnt ⊢
    field_simp
    ring

theorem alternating_beta_sum_one (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
      ((-1 : ℂ) ^ j / (((j : ℂ) + 2) * (j + 3))) =
    1 / (((n : ℂ) + 2) * (n + 3)) := by
  have h := alternating_beta_sum n 1
  simp only [Nat.cast_one, Nat.factorial_one, mul_one] at h
  have he : ∀ j : ℕ, ((j : ℂ) + 1 + 1) = j + 2 ∧ ((j : ℂ) + 1 + 2) = j + 3 :=
    fun j => ⟨by ring, by ring⟩
  simp_rw [(he _).1, (he _).2] at h
  rw [h, Nat.factorial_succ (n + 1 + 1), Nat.factorial_succ (n + 1)]
  have hf : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
  push_cast
  field_simp
  ring_nf

theorem cbz_reflection (k j : ℕ) (hj : j ≤ k) :
    cbz (1 - ((j + 2 : ℕ) : ℤ)) (k - j : ℕ) =
      (-1 : ℂ) ^ (k - j) * (k.choose j : ℂ) := by
  rw [show 1 - ((j + 2 : ℕ) : ℤ) = -(j : ℤ) - 1 by omega,
    cbz_apply_nonneg _ (by positivity), Int.toNat_natCast,
    FieldCombinatorics.gBinom_negsucc, Nat.add_sub_of_le hj]
  have hc := Nat.choose_mul_factorial_mul_factorial hj
  have hc' : (k.choose j : ℂ) * j.factorial * (k - j).factorial = k.factorial := by
    exact_mod_cast hc
  have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hkf : ((k - j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - j)
  field_simp
  rw [← hc']
  ring

/-- The scalar identity discharging the full state-space reflection. -/
theorem reflectionBinomialIdentity : ReflectionBinomialIdentity := by
  intro m
  rcases m with _ | m
  · simp [reflectionCoeff_zero, cbz_zero]
  rcases m with _ | k
  · norm_num [Finset.sum_range_succ, reflectionCoeff_zero, reflectionCoeff_succ,
      cbz_apply_nonneg, gBinom]
  have hc0 : cbz 1 ((k + 2 : ℕ) : ℤ) = 0 := cbz_lt (by norm_num) (by omega)
  have hc1 : cbz 0 ((k + 1 : ℕ) : ℤ) = 0 := cbz_lt (by norm_num) (by omega)
  change (∑ a ∈ Finset.range (k + 3),
    (-1 : ℂ) ^ a * reflectionCoeff a * cbz (1 - (a : ℤ)) (k + 2 - a : ℕ)) = _
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_zero, pow_zero,
    show (k + 2 - (0 + 1) : ℕ) = k + 1 by omega, hc1,
    show (1 - (0 + 1 : ℕ) : ℤ) = 0 by norm_num,
    mul_zero, add_zero]
  have ht : ∀ j ∈ Finset.range (k + 1),
      (-1 : ℂ) ^ (j + 1 + 1) * reflectionCoeff (j + 1 + 1) *
          cbz (1 - ((j + 1 + 1 : ℕ) : ℤ)) (k + 2 - (j + 1 + 1) : ℕ) =
      (-1 : ℂ) ^ (k + 1) * ((k.choose j : ℂ) *
        ((-1 : ℂ) ^ j / (((j : ℂ) + 2) * (j + 3)))) := by
    intro j hj
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [show j + 1 + 1 = j + 2 by omega,
      show k + 2 - (j + 2) = k - j by omega, cbz_reflection k j hjk,
      show j + 2 = (j + 1) + 1 by omega, reflectionCoeff_succ]
    have hsq : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
    have hsign : (-1 : ℂ) ^ (k - j) = (-1 : ℂ) ^ k * (-1 : ℂ) ^ j := by
      apply mul_right_cancel₀ (pow_ne_zero j (by norm_num : (-1 : ℂ) ≠ 0))
      rw [← pow_add, Nat.sub_add_cancel hjk, mul_assoc, ← sq, hsq, mul_one]
    rw [hsign]
    push_cast
    simp only [pow_succ]
    have h1 : (j : ℂ) + 1 + 1 = j + 2 := by ring
    have h2 : (j : ℂ) + 1 + 2 = j + 3 := by ring
    rw [h1, h2]
    have hcube : (-1 : ℂ) ^ (j * 3) = (-1 : ℂ) ^ j := by
      rw [mul_comm j 3, pow_mul]
      norm_num
    ring_nf
    rw [hcube]
  rw [Finset.sum_congr rfl ht, ← Finset.mul_sum, alternating_beta_sum_one,
    reflectionCoeff_succ]
  push_cast
  have hc0' : cbz 1 (2 + (k : ℤ)) = 0 := cbz_lt (by norm_num) (by omega)
  ring_nf
  rw [hc0', mul_zero, add_zero]

end VOA.Huang.VerlindeRho
