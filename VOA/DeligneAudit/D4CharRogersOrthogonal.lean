import VOA.DeligneAudit.D4CharRogersRecurrence

/-! Lemma O: all-index Rogers--Szego orthogonality for D4K.ctTheta. -/

namespace VOA.DeligneAudit.D4Char

open DeligneCharacter

noncomputable section

/-- The normalized Gram entry, with all spectator variables retained. -/
def rsGram (k l : ℕ) : D4K.R := rsMoment (rsH k * rsH l)

theorem rsGram_symm (k l : ℕ) : rsGram k l = rsGram l k := by
  rw [rsGram, rsGram, mul_comm]

/-- Move multiplication by x + x^-1 between the two arguments. -/
theorem rsGram_step (k l : ℕ) :
    rsGram (k + 1) l + (1 - D4K.qq ^ k) • rsGram (k - 1) l =
      rsGram k (l + 1) + (1 - D4K.qq ^ l) • rsGram k (l - 1) := by
  have h : (rsH 1 * rsH k) * rsH l = rsH k * (rsH 1 * rsH l) := by ring
  rw [rsH_recurrence_all, rsH_recurrence_all, add_mul, smul_mul_assoc,
    mul_add, mul_smul_comm] at h
  simpa only [map_add, map_smul, rsGram] using congrArg rsMoment h

/-- Every strictly upper triangular Gram entry is zero. -/
theorem rsGram_lt (k l : ℕ) (hkl : k < l) : rsGram k l = 0 := by
  induction k using Nat.strong_induction_on generalizing l with
  | h k ih =>
      cases k with
      | zero =>
          simp only [rsGram, rsH_zero, one_mul, rsMoment_rsH,
            if_neg (by omega : l ≠ 0)]
      | succ k =>
          have h := rsGram_step k l
          rw [ih k (by omega) (l + 1) (by omega),
            ih k (by omega) (l - 1) (by omega), smul_zero, add_zero] at h
          by_cases hk : k = 0
          · subst k
            simpa only [pow_zero, sub_self, zero_smul, add_zero] using h
          · rw [ih (k - 1) (by omega) l (by omega), smul_zero, add_zero] at h
            exact h

/-- The diagonal norm is the finite q-Pochhammer product. -/
theorem rsGram_diagonal (k : ℕ) : rsGram k k = D4K.qpoch k • (1 : D4K.R) := by
  induction k with
  | zero =>
      simpa only [rsGram, rsH_zero, one_mul, D4K.qpoch, Finset.prod_range_zero,
        one_smul, if_pos rfl] using rsMoment_rsH 0
  | succ k ih =>
      have h := rsGram_step k (k + 1)
      rw [rsGram_lt (k - 1) (k + 1) (by omega), smul_zero, add_zero,
        rsGram_lt k (k + 1 + 1) (by omega), zero_add, Nat.add_sub_cancel, ih,
        smul_smul] at h
      rw [D4K.qpoch_succ]
      simpa only [mul_comm] using h

/-- Lemma O, with the factor one half built into rsMoment. -/
theorem rsMoment_orthogonal (k l : ℕ) :
    rsMoment (rsH k * rsH l) = if k = l then D4K.qpoch k • (1 : D4K.R) else 0 := by
  change rsGram k l = _
  rcases lt_trichotomy k l with h | h | h
  · rw [if_neg (by omega), rsGram_lt k l h]
  · subst l
    rw [if_pos rfl, rsGram_diagonal]
  · rw [if_neg (by omega), rsGram_symm, rsGram_lt l k h]

/-- Lemma O directly on the original unnormalized kernel functional. -/
theorem ctTheta_rsH_mul (k l : ℕ) :
    D4K.ctTheta (rsH k * rsH l) =
      if k = l then (2 * D4K.qpoch k) • (1 : D4K.R) else 0 := by
  have h := congrArg (fun v : D4K.R => (2 : D4K.Kq) • v) (rsMoment_orthogonal k l)
  have h2 : (2 : D4K.Kq) ≠ 0 := by
    rw [show (2 : D4K.Kq) = HahnSeries.C (2 : ℚ) from (map_ofNat HahnSeries.C 2).symm]
    exact HahnSeries.C_ne_zero two_ne_zero
  simp only [rsMoment, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ h2, one_smul] at h
  split_ifs at h ⊢ <;> simpa only [smul_smul, smul_zero] using h

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsGram_symm
#print axioms VOA.DeligneAudit.D4Char.rsGram_step
#print axioms VOA.DeligneAudit.D4Char.rsGram_lt
#print axioms VOA.DeligneAudit.D4Char.rsGram_diagonal
#print axioms VOA.DeligneAudit.D4Char.rsMoment_orthogonal
#print axioms VOA.DeligneAudit.D4Char.ctTheta_rsH_mul
