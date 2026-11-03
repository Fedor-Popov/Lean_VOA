import VOA.DeligneAudit.D4FusionContactAllMWheelsCore
import Mathlib.RingTheory.PowerSeries.Basic

/-! Coefficientwise extension of a derivation to formal power series.
Only finite coefficient convolutions are used. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def seriesLinear (D : Derivation ℂ A A) : PowerSeries A →ₗ[ℂ] PowerSeries A where
  toFun f := PowerSeries.mk (fun n => D (PowerSeries.coeff n f))
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add]
  map_smul' c f := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_smul, Derivation.map_smul,
      RingHom.id_apply]

@[simp] theorem coeff_seriesLinear (D : Derivation ℂ A A) (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (seriesLinear D f) = D (PowerSeries.coeff n f) := by
  simp only [seriesLinear, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk]

def seriesDeriv (D : Derivation ℂ A A) : Derivation ℂ (PowerSeries A) (PowerSeries A) :=
  Derivation.mk' (seriesLinear D) (by
    intro f g
    apply PowerSeries.ext
    intro n
    simp only [smul_eq_mul, coeff_seriesLinear, map_add, PowerSeries.coeff_mul, map_sum]
    simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    exact Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun x : ℕ × ℕ => PowerSeries.coeff x.1 g * D (PowerSeries.coeff x.2 f)))

@[simp] theorem coeff_seriesDeriv (D : Derivation ℂ A A) (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (seriesDeriv D f) = D (PowerSeries.coeff n f) :=
  coeff_seriesLinear D f n

theorem seriesDeriv_mk (D : Derivation ℂ A A) (U V : ℕ → A)
    (hU : ∀ n, D (U n) = V n) : seriesDeriv D (PowerSeries.mk U) = PowerSeries.mk V := by
  ext n
  simpa only [coeff_seriesDeriv, PowerSeries.coeff_mk] using hU n

omit [Algebra ℂ A] in
/-- A bounded left factor only samples the proved high-degree right coefficients. -/
theorem coeff_mul_mem_region (I : Ideal A) (Z Q : PowerSeries A) (L s : ℕ)
    (hZ : ∀ j, L ≤ j → PowerSeries.coeff j Z = 0)
    (hQ : ∀ i j, i + j = s → j < L → PowerSeries.coeff i Q ∈ I) :
    PowerSeries.coeff s (Z * Q) ∈ I := by
  rw [PowerSeries.coeff_mul]
  apply I.sum_mem
  intro x hx
  have hsum : x.1 + x.2 = s := Finset.mem_antidiagonal.mp hx
  by_cases hj : L ≤ x.1
  · rw [hZ x.1 hj, zero_mul]
    exact I.zero_mem
  · exact I.mul_mem_left _ (hQ x.2 x.1 (by omega) (by omega))

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.seriesDeriv
