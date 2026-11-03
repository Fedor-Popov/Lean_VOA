import VOA.DeligneAudit.DeligneFusionCVShifted

/-!
# Exact cutoff coefficient identities for the SRK kernel calculation

Splitting off the lowest mode of a current series gives the quadratic and
cubic coefficient identities used in SRK (8.24)--(8.26). These are identities
of endomorphisms, before applying any highest-weight or CV relation.
-/

namespace VOA.DeligneAudit.CVsl2

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A cutoff current is its first monomial plus the next cutoff current. -/
theorem cutoff_series_split (F : ℕ → Module.End ℂ V) (A : ℕ) :
    Garland.Fs (fromMode F A) =
      PowerSeries.monomial A (F A) + Garland.Fs (fromMode F (A + 1)) := by
  apply PowerSeries.ext
  intro k
  simp only [Garland.Fs, PowerSeries.coeff_mk, map_add,
    PowerSeries.coeff_monomial, fromMode]
  split_ifs <;> simp_all <;> omega

private theorem cutoff_monomial_commute {F : ℕ → Module.End ℂ V}
    (hFF : ∀ i j, F i * F j = F j * F i) (A : ℕ) :
    Commute (PowerSeries.monomial A (F A))
      (Garland.Fs (fromMode F (A + 1))) := by
  have hc : Commute (Garland.Fs (fromMode F A))
      (Garland.Fs (fromMode F (A + 1))) := by
    apply current_series_commute
    intro i j
    by_cases hi : A ≤ i <;> by_cases hj : A + 1 ≤ j
    · simpa only [fromMode, if_pos hi, if_pos hj] using hFF i j
    · simp [fromMode, hi, hj]
    · simp [fromMode, hi, hj]
    · simp [fromMode, hi, hj]
  have hm : PowerSeries.monomial A (F A) =
      Garland.Fs (fromMode F A) - Garland.Fs (fromMode F (A + 1)) := by
    rw [cutoff_series_split]
    abel
  rw [hm]
  exact hc.sub_left (Commute.refl _)

private theorem coeff_monomial_mul_add {R : Type*} [Semiring R]
    (p q : ℕ) (a : R) (P : PowerSeries R) :
    PowerSeries.coeff (p + q) (PowerSeries.monomial p a * P) =
      a * PowerSeries.coeff q P := by
  simpa only [PowerSeries.coeff, PowerSeries.monomial, Finsupp.single_add] using
    (MvPowerSeries.coeff_add_monomial_mul
      (Finsupp.single () p) (Finsupp.single () q) P a)

private theorem monomial_pow {R : Type*} [Semiring R]
    (m : ℕ) (a : R) (n : ℕ) :
    PowerSeries.monomial m a ^ n = PowerSeries.monomial (n * m) (a ^ n) := by
  induction n with
  | zero => simp [PowerSeries.monomial_zero_eq_C_apply]
  | succ n ih =>
    rw [pow_succ, ih, PowerSeries.monomial_mul_monomial, pow_succ,
      Nat.succ_mul]

private theorem commute_cube {R : Type*} [Semiring R] {a b : R}
    (h : Commute a b) :
    (a + b) ^ 3 = a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3 := by
  have hp := h.add_pow' 3
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hp
  norm_num [Finset.sum_range_succ] at hp
  rw [hp]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  abel

/-- The quadratic cutoff identity, with ordinary-power normalization. -/
theorem cutoff_split_two {F : ℕ → Module.End ℂ V}
    (hFF : ∀ i j, F i * F j = F j * F i) (A j : ℕ) (hj : 2 ≤ j) :
    QFrom F A 2 (2 * A + j - 1) =
      2 • (F A * F (A + j - 1)) + QFrom F (A + 1) 2 (2 * A + j - 1) := by
  have hc := cutoff_monomial_commute hFF A
  have hsquare :
      (PowerSeries.monomial A (F A) + Garland.Fs (fromMode F (A + 1))) ^ 2 =
        PowerSeries.monomial A (F A) ^ 2 +
          2 • (PowerSeries.monomial A (F A) * Garland.Fs (fromMode F (A + 1))) +
          Garland.Fs (fromMode F (A + 1)) ^ 2 := by
    simpa only [two_mul, add_mul, two_nsmul] using hc.add_sq
  have heq := congrArg (PowerSeries.coeff (2 * A + j - 1)) hsquare
  rw [← cutoff_series_split F A] at heq
  have hindex : 2 * A + j - 1 = A + (A + j - 1) := by omega
  have hne : 2 * A + j - 1 ≠ 2 * A := by omega
  have hbound : A + 1 ≤ A + j - 1 := by omega
  simp only [map_add, map_nsmul, monomial_pow,
    PowerSeries.coeff_monomial, if_neg hne, zero_add] at heq
  have hcoeff : PowerSeries.coeff (2 * A + j - 1)
      (PowerSeries.monomial A (F A) * Garland.Fs (fromMode F (A + 1))) =
      F A * F (A + j - 1) := by
    rw [hindex, coeff_monomial_mul_add]
    simp only [Garland.Fs, PowerSeries.coeff_mk, fromMode, if_pos hbound]
  rw [hcoeff] at heq
  exact heq

/-- The cubic cutoff identity, with ordinary-power normalization. -/
theorem cutoff_split_three {F : ℕ → Module.End ℂ V}
    (hFF : ∀ i j, F i * F j = F j * F i) (A j : ℕ) (hj : 2 ≤ j) :
    QFrom F A 3 (3 * A + j - 1) =
      3 • (F A ^ 2 * F (A + j - 1)) +
      3 • (F A * QFrom F (A + 1) 2 (2 * A + j - 1)) +
      QFrom F (A + 1) 3 (3 * A + j - 1) := by
  have hc := cutoff_monomial_commute hFF A
  have heq := congrArg (PowerSeries.coeff (3 * A + j - 1)) (commute_cube hc)
  rw [← cutoff_series_split F A] at heq
  have hindex₂ : 3 * A + j - 1 = 2 * A + (A + j - 1) := by omega
  have hindex₁ : 3 * A + j - 1 = A + (2 * A + j - 1) := by omega
  have hne : 3 * A + j - 1 ≠ 3 * A := by omega
  have hbound : A + 1 ≤ A + j - 1 := by omega
  simp only [map_add, map_nsmul, monomial_pow,
    PowerSeries.coeff_monomial, if_neg hne, zero_add] at heq
  have hcoeff₂ : PowerSeries.coeff (3 * A + j - 1)
      (PowerSeries.monomial (2 * A) (F A ^ 2) *
        Garland.Fs (fromMode F (A + 1))) = F A ^ 2 * F (A + j - 1) := by
    rw [hindex₂, coeff_monomial_mul_add]
    simp only [Garland.Fs, PowerSeries.coeff_mk, fromMode, if_pos hbound]
  have hcoeff₁ : PowerSeries.coeff (3 * A + j - 1)
      (PowerSeries.monomial A (F A) * Garland.Fs (fromMode F (A + 1)) ^ 2) =
      F A * QFrom F (A + 1) 2 (2 * A + j - 1) := by
    rw [hindex₁, coeff_monomial_mul_add]
    rfl
  rw [hcoeff₂, hcoeff₁] at heq
  exact heq

end

end VOA.DeligneAudit.CVsl2

#print axioms VOA.DeligneAudit.CVsl2.cutoff_series_split
#print axioms VOA.DeligneAudit.CVsl2.cutoff_split_two
#print axioms VOA.DeligneAudit.CVsl2.cutoff_split_three
