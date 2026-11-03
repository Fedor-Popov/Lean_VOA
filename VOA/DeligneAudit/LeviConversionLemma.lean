import VOA.DeligneAudit.LeviConversionCoeff

/-! The conversion relation after applying a Garland coefficient to a vector. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [AddCommGroup V] [Module A V]

/-- The full conversion relation before separating the top contraction count. -/
theorem conversion_sum_zero (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (R : A) (v : V)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • (R • v) = 0) :
    (((choices xs).map (conversionTerm f a b k s)).sum) • (R • v) = 0 := by
  have h := congrArg (PowerSeries.coeff s) (wick_series f a b hfa hfb hab k xs)
  rw [aConst_word, PowerSeries.coeff_C_mul, coeff_wickSum] at h
  calc
    (((choices xs).map (conversionTerm f a b k s)).sum) • (R • v) =
        (aWord a xs * PowerSeries.coeff s (fCurrent f ^ k)) • (R • v) := by
          rw [h]
    _ = aWord a xs • (PowerSeries.coeff s (fCurrent f ^ k) • (R • v)) :=
      mul_smul _ _ _
    _ = 0 := by rw [hkill, smul_zero]

theorem spectator_comm_coeff (f : ℕ → A) (R : A)
    (hRf : ∀ i, R * f i = f i * R) (k s : ℕ) :
    R * PowerSeries.coeff s (fCurrent f ^ k) =
      PowerSeries.coeff s (fCurrent f ^ k) * R := by
  have hseries : PowerSeries.C R * fCurrent f = fCurrent f * PowerSeries.C R := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      fCurrent, PowerSeries.coeff_mk]
    exact hRf n
  have hpow : PowerSeries.C R * fCurrent f ^ k =
      fCurrent f ^ k * PowerSeries.C R :=
    (Commute.pow_right (show Commute (PowerSeries.C R) (fCurrent f) from hseries) k).eq
  have hc := congrArg (PowerSeries.coeff s) hpow
  simpa only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C] using hc

/-- Conversion from a Garland vanishing relation on `v`, with a commuting spectator. -/
theorem conversion_sum_zero_of_spectator (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0) :
    (((choices xs).map (conversionTerm f a b k s)).sum) • (R • v) = 0 := by
  have hc := spectator_comm_coeff f R hRf k s
  have hkillR : PowerSeries.coeff s (fCurrent f ^ k) • (R • v) = 0 := by
    rw [← mul_smul, ← hc, mul_smul, hkill, smul_zero]
  exact conversion_sum_zero f a b hfa hfb hab k s xs R v hkillR

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.conversion_sum_zero
#print axioms VOA.DeligneAudit.LeviConversion.conversion_sum_zero_of_spectator
