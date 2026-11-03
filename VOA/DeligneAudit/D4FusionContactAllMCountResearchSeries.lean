import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Coefficientwise derivations on current series

The Leibniz identity uses the actual finite coefficient convolution.
This lets constant color derivations commute with whole current
coefficient extraction, without a coefficient-separation assumption.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Apply an actual coefficient-ring derivation coefficient by coefficient. -/
def seriesDerivation (D : Derivation R A A) :
    Derivation R (PowerSeries A) (PowerSeries A) where
  toFun f := PowerSeries.mk fun n => D (PowerSeries.coeff n f)
  map_add' f g := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk,map_add]
  map_smul' a f := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk,PowerSeries.coeff_smul,Derivation.map_smul,
      RingHom.id_apply]
  map_one_eq_zero' := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.mk
      (fun j => D (PowerSeries.coeff j (1 : PowerSeries A)))) = PowerSeries.coeff n 0
    rw [PowerSeries.coeff_mk,map_zero,PowerSeries.coeff_one]
    split_ifs
    · exact D.map_one_eq_zero
    · exact map_zero D
  leibniz' f g := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.mk
      (fun j => D (PowerSeries.coeff j (f*g)))) = PowerSeries.coeff n
      (f • PowerSeries.mk (fun j => D (PowerSeries.coeff j g)) +
       g • PowerSeries.mk (fun j => D (PowerSeries.coeff j f)))
    simp only [PowerSeries.coeff_mk,smul_eq_mul,map_add,
      PowerSeries.coeff_mul,map_sum,Derivation.leibniz,Finset.sum_add_distrib]
    congr 1
    have hh := (Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun x : ℕ × ℕ => PowerSeries.coeff x.1 g * D (PowerSeries.coeff x.2 f)))
    simpa only [Prod.swap,smul_eq_mul] using hh

@[simp] theorem seriesDerivation_coeff (D : Derivation R A A) (n : ℕ) (f : PowerSeries A) :
    PowerSeries.coeff n (seriesDerivation D f) = D (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n (PowerSeries.mk fun j => D (PowerSeries.coeff j f)) = _
  rw [PowerSeries.coeff_mk]

@[simp] theorem seriesDerivation_mk (D : Derivation R A A) (f : ℕ → A) :
    seriesDerivation D (PowerSeries.mk f) = PowerSeries.mk fun n => D (f n) := by
  apply PowerSeries.ext
  intro n
  simp only [seriesDerivation_coeff,PowerSeries.coeff_mk]

end

#print axioms seriesDerivation

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
