import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Nat.Factorial.Basic
import Lean.Elab.Tactic.Omega

/-! Whole-series jet convolutions vanish in any ideal containing the two
source tails. Ordinary formal derivatives retain their exact factorials. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable {R : Type*} [CommSemiring R]

def jetDerivative (a : ℕ) (f : PowerSeries R) : PowerSeries R :=
  ((PowerSeries.derivative R : PowerSeries R → PowerSeries R)^[a]) f

@[simp] theorem jetDerivative_zero (f : PowerSeries R) : jetDerivative 0 f = f := rfl

theorem jetDerivative_succ (a : ℕ) (f : PowerSeries R) :
    jetDerivative (a + 1) f = jetDerivative a (PowerSeries.derivative R f) :=
  Function.iterate_succ_apply _ _ _

theorem coeff_jetDerivative (f : PowerSeries R) (a n : ℕ) :
    PowerSeries.coeff n (jetDerivative a f) =
      PowerSeries.coeff (n + a) f * ((n + 1).ascFactorial a : R) := by
  induction a generalizing f with
  | zero =>
      simp only [jetDerivative_zero,Nat.add_zero,Nat.ascFactorial_zero,Nat.cast_one,mul_one]
  | succ a ih =>
      rw [jetDerivative_succ,ih,PowerSeries.coeff_derivative,Nat.ascFactorial_succ,Nat.cast_mul]
      rw [show n + 1 + a = n + a + 1 by omega,show n + (a + 1) = n + a + 1 by omega]
      simp only [mul_assoc,Nat.cast_add,Nat.cast_one]

theorem coeff_jetDerivative_mem (I : Ideal R) (f : PowerSeries R) (a n : ℕ)
    (h : PowerSeries.coeff (n + a) f ∈ I) :
    PowerSeries.coeff n (jetDerivative a f) ∈ I := by
  rw [coeff_jetDerivative]
  exact Ideal.mul_mem_right _ I h

/-- If both factors were outside their source tails, their summed original
current degree would be at most twice the cutoff, contradicting h. -/
theorem coeff_jet_product_mem (I : Ideal R) (f g : PowerSeries R)
    (r s m a b N : ℕ)
    (hf : ∀ k, m < r + k → PowerSeries.coeff k f ∈ I)
    (hg : ∀ k, m < s + k → PowerSeries.coeff k g ∈ I)
    (h : 2 * m < r + s + N + a + b) :
    PowerSeries.coeff N (jetDerivative a f * jetDerivative b g) ∈ I := by
  rw [PowerSeries.coeff_mul]
  apply Submodule.sum_mem
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  by_cases hleft : m < r + (p.1 + a)
  · exact Ideal.mul_mem_right _ I
      (coeff_jetDerivative_mem I f a p.1 (hf _ hleft))
  · have hright : m < s + (p.2 + b) := by omega
    exact I.mul_mem_left _ (coeff_jetDerivative_mem I g b p.2 (hg _ hright))

end
#print axioms coeff_jetDerivative
#print axioms coeff_jet_product_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
