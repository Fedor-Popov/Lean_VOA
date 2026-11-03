import VOA.Classification.COne.OrbPosLowest

/-!
# Rank-one inner-twist energy bookkeeping

Normalize the root by `(α,α) = 2`, and use `Δ(-h,z)` with
`h = a α/(2n)`. A charge `(k + ε/2) α` then has energy
`(k + ε/2 - a/(2n))² + r`, where `ε = 0,1` and `r` is an oscillator level.
This file proves the completed square, its exact minima, and the gap.
It does not assert existence or classification of twisted VOA modules.
-/

namespace VOA.Classification.COne.OrbPos2
open VOA OrbPos

/-- The rational energy of the shifted charge and oscillator level. -/
def innerEnergy (n : ℕ) (a ε k : ℤ) (r : ℕ) : ℚ :=
  ((k : ℚ) + ε / 2 - a / (2 * n)) ^ 2 + r

/-- The scalar `L₀ - h(0) + (h,h)/2` formula, before completing the square. -/
theorem innerEnergy_shift (n : ℕ) (a ε k : ℤ) (r : ℕ) :
    innerEnergy n a ε k r =
      ((k : ℚ) + ε / 2) ^ 2 + r -
        2 * ((k : ℚ) + ε / 2) * (a / (2 * n)) + (a / (2 * n)) ^ 2 := by
  unfold innerEnergy
  ring

/-- The Li energy has exactly the cyclic form used in the spectrum residual. -/
theorem innerEnergy_eq_cyclicWeight {n : ℕ} (hn : 0 < n) (a ε k : ℤ) (r : ℕ) :
    (innerEnergy n a ε k r : ℂ) =
      CyclicWeight n ((n : ℤ) * (2 * k + ε) - a) r := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  apply Complex.ext
  · simp only [Complex.ratCast_re, CyclicWeight, Complex.ofReal_re]
    unfold innerEnergy
    push_cast
    field_simp [hn0]
  · simp only [Complex.ratCast_im, CyclicWeight, Complex.ofReal_im]

/-- A nontrivial torus shift cannot cancel an integral half-root charge. -/
theorem innerCharge_ne_zero {n : ℕ} {a : ℤ} (ha : 0 < a) (han : a < n)
    (j : ℤ) : (n : ℤ) * j - a ≠ 0 := by
  intro he
  have hn : (0 : ℤ) < n := lt_trans ha han
  have hjpos : 0 < j := by nlinarith
  have hjlt : j < 1 := by nlinarith
  omega

theorem innerEnergy_ne_zero {n : ℕ} {a : ℤ} (ha : 0 < a) (han : a < n)
    (ε k : ℤ) (r : ℕ) : (innerEnergy n a ε k r : ℂ) ≠ 0 := by
  have hn : 0 < n := by omega
  rw [innerEnergy_eq_cyclicWeight hn]
  intro he
  exact innerCharge_ne_zero ha han (2 * k + ε)
    ((cyclicWeight_eq_zero_iff hn _ _).mp he).1

/-- Every nontrivial inner-twist energy with denominator at most five is at least `1/100`.
No restriction on the integral charge is needed for this bound. -/
theorem innerEnergy_gap {n : ℕ} (hn5 : n ≤ 5) {a : ℤ}
    (ha : 0 < a) (han : a < n) (ε k : ℤ) (r : ℕ) :
    (1 : ℝ) / 100 ≤ (innerEnergy n a ε k r : ℂ).re := by
  have hn : 0 < n := by omega
  have he := innerEnergy_ne_zero ha han ε k r
  rw [innerEnergy_eq_cyclicWeight hn] at he ⊢
  convert cyclicWeight_gap hn hn5 _ r he using 1
  norm_num

/-- Both level-one charge cosets attain their minimum at charge translate zero
when the angle is normalized by `0 ≤ a ≤ n`. -/
theorem innerEnergy_minimum {n : ℕ} (hn : 0 < n) {a : ℤ}
    (ha : 0 ≤ a) (han : a ≤ n) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (k : ℤ) (r : ℕ) : innerEnergy n a ε 0 0 ≤ innerEnergy n a ε k r := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have haQ : (0 : ℚ) ≤ a := by exact_mod_cast ha
  have hanQ : (a : ℚ) ≤ n := by exact_mod_cast han
  have ht0 : (0 : ℚ) ≤ a / (2 * n) := by positivity
  have ht1 : (a : ℚ) / (2 * n) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * n)).2
    linarith
  have hr : (0 : ℚ) ≤ r := r.cast_nonneg
  rcases hε with rfl | rfl
  all_goals
    unfold innerEnergy
    push_cast
    by_cases hk : k = 0
    · subst k; nlinarith
    · rcases lt_or_gt_of_ne hk with hk | hk
      · have hkQ : (k : ℚ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ -(k : ℚ)) ht0,
          mul_nonneg (by linarith : (0 : ℚ) ≤ -(k : ℚ))
            (by linarith : (0 : ℚ) ≤ 1 / 2 - a / (2 * n))]
      · have hkQ : (1 : ℚ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (k : ℚ)) ht0,
          mul_nonneg (by linarith : (0 : ℚ) ≤ (k : ℚ))
            (by linarith : (0 : ℚ) ≤ 1 / 2 - a / (2 * n))]

/-- Representative angles `1/2,1/3,1/4,1/5,2/5`: the two explicit minima. -/
theorem innerEnergy_exceptional_table :
    (innerEnergy 2 1 0 0 0, innerEnergy 2 1 1 0 0) = (1/16, 1/16) ∧
    (innerEnergy 3 1 0 0 0, innerEnergy 3 1 1 0 0) = (1/36, 1/9) ∧
    (innerEnergy 4 1 0 0 0, innerEnergy 4 1 1 0 0) = (1/64, 9/64) ∧
    (innerEnergy 5 1 0 0 0, innerEnergy 5 1 1 0 0) = (1/100, 4/25) ∧
    (innerEnergy 5 2 0 0 0, innerEnergy 5 2 1 0 0) = (1/25, 9/100) := by
  norm_num [innerEnergy]

section ShiftedOperator
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The energy part of Li's operation, separated from the unproved field construction.
Here `H` is the root zero mode, whose charge-`q` eigenvalue is `2q`. -/
noncomputable def shiftedL0 (L H : Module.End ℂ M) (t : ℂ) : Module.End ℂ M :=
  L - t • H + t ^ 2 • LinearMap.id

/-- Joint eigenvectors acquire the completed-square energy under the shifted operator. -/
theorem shiftedL0_eigen (L H : Module.End ℂ M) (t q s : ℂ) (v : M)
    (hL : L v = (q ^ 2 + s) • v) (hH : H v = (2 * q) • v) :
    shiftedL0 L H t v = ((q - t) ^ 2 + s) • v := by
  simp only [shiftedL0, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, hL, hH, smul_smul]
  rw [← sub_smul, ← add_smul]
  congr 1
  ring

end ShiftedOperator
end VOA.Classification.COne.OrbPos2
