import VOA.DeligneAudit.D4FusionContactAllMNormalSeries
import Mathlib.Data.Nat.Factorial.Basic

/-! Iterated two-step current transport for arbitrary whole powers. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem iterate_deriv_power (D : Derivation ℂ A A) (u v : A)
    (hu : D u = v) (hv : D v = 0) (k n : ℕ) :
    ((D : A → A)^[k]) (u ^ (n + k)) =
      ((n + k).descFactorial k : A) * u ^ n * v ^ k := by
  induction k generalizing n with
  | zero =>
      simp only [Function.iterate_zero_apply, Nat.add_zero, Nat.descFactorial_zero,
        Nat.cast_one, pow_zero, one_mul, mul_one]
  | succ k ih =>
      rw [Function.iterate_succ_apply', show n + (k + 1) = (n + 1) + k by omega, ih]
      rw [Nat.descFactorial_succ, show n + 1 + k - k = n + 1 by omega]
      have hz : D (v ^ k) = 0 := by simp only [Derivation.leibniz_pow, hv, smul_zero]
      simp only [Derivation.leibniz, Derivation.map_natCast, AllMWheels.deriv_pow_succ,
        hu, hz, smul_eq_mul]
      simp only [pow_succ]
      push_cast
      ring

theorem iterate_deriv_self_power (D : Derivation ℂ A A) (u v : A)
    (hu : D u = v) (hv : D v = 0) (r : ℕ) :
    ((D : A → A)^[r]) (u ^ r) = (r.factorial : A) * v ^ r := by
  simpa only [Nat.zero_add, Nat.descFactorial_self, pow_zero, mul_one] using
    iterate_deriv_power D u v hu hv r 0

theorem coeff_series_iterate (D : Derivation ℂ A A) (f : PowerSeries A) (r s : ℕ) :
    PowerSeries.coeff s (((seriesDeriv D : PowerSeries A → PowerSeries A)^[r]) f) =
      ((D : A → A)^[r]) (PowerSeries.coeff s f) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', coeff_seriesDeriv, ih,
      Function.iterate_succ_apply']

theorem iterate_deriv_powerCoeff (D : Derivation ℂ A A) (U V : ℕ → A)
    (hU : ∀ i, D (U i) = V i) (hV : ∀ i, D (V i) = 0) (r s : ℕ) :
    ((D : A → A)^[r]) (PowerSeries.coeff s (PowerSeries.mk U ^ r)) =
      r.factorial • PowerSeries.coeff s (PowerSeries.mk V ^ r) := by
  have hu : seriesDeriv D (PowerSeries.mk U) = PowerSeries.mk V := seriesDeriv_mk D U V hU
  have hv : seriesDeriv D (PowerSeries.mk V) = 0 := by
    apply PowerSeries.ext
    intro i
    simp only [coeff_seriesDeriv, PowerSeries.coeff_mk, hV, map_zero]
  have he : ((seriesDeriv D : PowerSeries A → PowerSeries A)^[r]) (PowerSeries.mk U ^ r) =
      r.factorial • (PowerSeries.mk V ^ r) := by
    simpa only [nsmul_eq_mul] using
      iterate_deriv_self_power (seriesDeriv D) (PowerSeries.mk U) (PowerSeries.mk V) hu hv r
  have hc := congrArg (PowerSeries.coeff s) he
  simpa only [coeff_series_iterate, map_nsmul] using hc

theorem iterate_deriv_nsmul (D : Derivation ℂ A A) (r c : ℕ) (p : A) :
    ((D : A → A)^[r]) (c • p) = c • ((D : A → A)^[r]) p := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih, map_nsmul,
      Function.iterate_succ_apply']

theorem iterate_deriv_mem (I : Ideal A) (D : Derivation ℂ A A)
    (hI : ∀ p ∈ I, D p ∈ I) (r : ℕ) {p : A} (hp : p ∈ I) :
    ((D : A → A)^[r]) p ∈ I := by
  induction r with
  | zero => exact hp
  | succ r ih => rw [Function.iterate_succ_apply']; exact hI _ ih

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.iterate_deriv_powerCoeff
