/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Extending a coefficient derivation to formal series

Differentiation of coefficients defines an actual derivation on the
formal-series ring. The product rule is proved by the finite coefficient
convolution, so no analytic convergence assumption is needed.
-/
namespace VOA
noncomputable section
open scoped BigOperators
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Apply a coefficient-ring derivation separately at every formal
series coefficient. -/
def powerSeriesCoefficientDerivation (D : Derivation ℂ R R) :
    Derivation ℂ (PowerSeries R) (PowerSeries R) where
  toLinearMap :=
    { toFun := fun P => PowerSeries.mk fun n => D (PowerSeries.coeff n P)
      map_add' := by intro P Q; ext n; simp
      map_smul' := by intro c P; ext n; simp [PowerSeries.coeff_smul] }
  map_one_eq_zero' := by
    ext n
    change PowerSeries.coeff n (PowerSeries.mk (fun a => D (PowerSeries.coeff a (1 : PowerSeries R)))) = 0
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs <;> simp
  leibniz' := by
    intro P Q
    ext n
    change PowerSeries.coeff n (PowerSeries.mk (fun a => D (PowerSeries.coeff a (P*Q)))) =
      PowerSeries.coeff n (P * PowerSeries.mk (fun a => D (PowerSeries.coeff a Q)) +
        Q * PowerSeries.mk (fun a => D (PowerSeries.coeff a P)))
    simp only [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul]
    rw [map_sum]
    simp only [D.leibniz, smul_eq_mul, PowerSeries.coeff_mk, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_equiv (Equiv.prodComm ℕ ℕ)
    · intro ij; simp [Finset.mem_antidiagonal, add_comm]
    · intro ij _; simp [mul_comm]

/-- Each coefficient of the extended derivation is the original
coefficient derivation applied to that coefficient. -/
theorem coeff_powerSeriesCoefficientDerivation (D : Derivation ℂ R R)
    (P : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (powerSeriesCoefficientDerivation D P) = D (PowerSeries.coeff n P) := by
  change PowerSeries.coeff n (PowerSeries.mk (fun a => D (PowerSeries.coeff a P))) = _
  exact PowerSeries.coeff_mk _ _

/-- On a series assembled from a coefficient sequence, the extension
acts on that sequence term by term. -/
theorem powerSeriesCoefficientDerivation_mk (D : Derivation ℂ R R) (f : ℕ → R) :
    powerSeriesCoefficientDerivation D (PowerSeries.mk f) = PowerSeries.mk (fun n => D (f n)) := by
  ext n
  simp [coeff_powerSeriesCoefficientDerivation]

end
end VOA
