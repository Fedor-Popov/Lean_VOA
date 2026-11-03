import VOA.DeligneAudit.D4CharRogersMoments
import VOA.DeligneAudit.D4CharPieriInteger

/-! The three-term Rogers--Szego recurrence in the actual D4 Laurent ring. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian DeligneCharacter

noncomputable section

theorem rsMon_add (v : D4K.V) (a b : D4K.Kq) :
    D4K.mon v (a + b) = D4K.mon v a + D4K.mon v b := Finsupp.single_add v a b

theorem rsMon_smul (a b : D4K.Kq) (v : D4K.V) :
    a • D4K.mon v b = D4K.mon v (a * b) := by
  simp only [D4K.mon, AddMonoidAlgebra.smul_single']

theorem rsX_mul_mon (a b : ℤ) (c : D4K.Kq) :
    D4K.xPow a * D4K.mon (b • D4K.xv) c = D4K.mon ((a + b) • D4K.xv) c := by
  rw [D4K.xPow, D4K.mon_mul_mon, ← add_smul, one_mul]

/-- The coefficient form of q-Pascal needed by the three-term recurrence. -/
theorem rsGaussian_step (n j : ℕ) :
    qbinom D4K.qq (n + 2) (j + 1) +
        (1 - D4K.qq ^ (n + 1)) * qbinom D4K.qq n j =
      qbinom D4K.qq (n + 1) (j + 1) + qbinom D4K.qq (n + 1) j := by
  rw [show n + 2 = (n + 1) + 1 by omega, qbinom_succ_succ]
  linear_combination -(qbinom_lower D4K.qq n j)

@[simp] theorem rsH_one : rsH 1 = D4K.xPow 1 + D4K.xPow (-1) := by
  norm_num [rsH, Finset.sum_range_succ, qbinom_diagonal, D4K.xPow]

/-- Lemma O(ii), uniformly for every positive index. -/
theorem rsH_recurrence (n : ℕ) :
    rsH 1 * rsH (n + 1) = rsH (n + 2) +
      (1 - D4K.qq ^ (n + 1)) • rsH n := by
  let f := fun j : ℕ => D4K.mon (((n : ℤ) + 2 - 2 * j) • D4K.xv)
    (qbinom D4K.qq (n + 2) j)
  let g := fun j : ℕ => D4K.mon (((n : ℤ) + 2 - 2 * j) • D4K.xv)
    (qbinom D4K.qq (n + 1) j)
  let h := fun j : ℕ => D4K.mon (((n : ℤ) - 2 * j) • D4K.xv)
    (qbinom D4K.qq (n + 1) j)
  let c := fun j : ℕ => D4K.mon (((n : ℤ) - 2 * j) • D4K.xv)
    ((1 - D4K.qq ^ (n + 1)) * qbinom D4K.qq n j)
  have ht (j : ℕ) : f (j + 1) + c j = g (j + 1) + h j := by
    dsimp [f, g, h, c]
    rw [show (n : ℤ) + 2 - 2 * ((j : ℤ) + 1) = n - 2 * j by omega,
      ← rsMon_add, ← rsMon_add, rsGaussian_step]
  have hf : (∑ j ∈ Finset.range (n + 2), f (j + 1)) = rsH (n + 2) - f 0 := by
    apply eq_sub_iff_add_eq.mpr
    rw [← Finset.sum_range_succ']
    simp only [rsH, f, Nat.cast_add, Nat.cast_ofNat]
  have hg : (∑ j ∈ Finset.range (n + 2), g (j + 1)) =
      D4K.xPow 1 * rsH (n + 1) - g 0 := by
    apply eq_sub_iff_add_eq.mpr
    rw [← Finset.sum_range_succ', Finset.sum_range_succ]
    have hz : g (n + 2) = 0 := by
      simp [g, qbinom_eq_zero_of_lt D4K.qq (by omega : n + 1 < n + 2), D4K.mon]
      rfl
    rw [hz, add_zero, rsH, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [rsX_mul_mon]
    dsimp [g]
    congr 2
    push_cast
    ring
  have hh : (∑ j ∈ Finset.range (n + 2), h j) = D4K.xPow (-1) * rsH (n + 1) := by
    rw [rsH, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [rsX_mul_mon]
    dsimp [h]
    congr 2
    push_cast
    ring
  have hc : (∑ j ∈ Finset.range (n + 2), c j) =
      (1 - D4K.qq ^ (n + 1)) • rsH n := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    have hz : c (n + 1) = 0 := by
      simp [c, qbinom_eq_zero_of_lt D4K.qq (by omega : n < n + 1), D4K.mon]
      rfl
    rw [hz, add_zero, rsH, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (rsMon_smul _ _ _).symm
  have hs := Finset.sum_congr (s₁ := Finset.range (n + 2)) rfl (fun j _ => ht j)
  simp only [Finset.sum_add_distrib] at hs
  rw [hf, hg, hh, hc] at hs
  have hfg : f 0 = g 0 := by simp [f, g]
  rw [hfg] at hs
  rw [rsH_one, add_mul]
  linear_combination -hs

/-- The recurrence with its zero-index case included by a vanishing coefficient. -/
theorem rsH_recurrence_all (n : ℕ) :
    rsH 1 * rsH n = rsH (n + 1) + (1 - D4K.qq ^ n) • rsH (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.add_sub_cancel] using rsH_recurrence n

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsMon_add
#print axioms VOA.DeligneAudit.D4Char.rsMon_smul
#print axioms VOA.DeligneAudit.D4Char.rsX_mul_mon
#print axioms VOA.DeligneAudit.D4Char.rsGaussian_step
#print axioms VOA.DeligneAudit.D4Char.rsH_one
#print axioms VOA.DeligneAudit.D4Char.rsH_recurrence
#print axioms VOA.DeligneAudit.D4Char.rsH_recurrence_all
