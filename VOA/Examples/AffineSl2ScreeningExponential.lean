/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningDifferentiation

/-!
# Actual boson differentiation and its finite terminal error

Differentiate the actual oscillator coefficients, retain the terminal term,
and prove that this term has zero selected screening coefficient. The
result is a finite polynomial identity, with no infinite exponential.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Actual partial differentiation in one oscillator variable, extended to
all auxiliary coefficients. -/
def oscillatorPartial (r : ℕ) (v : Fin 3 × ℕ) :
    Derivation ℂ (Auxiliary r) (Auxiliary r) := auxiliaryDerivative r (pderiv v)

/-- Oscillator partials act on the selected actual polynomial coefficient. -/
theorem oscillatorPartial_apply (r : ℕ) (v : Fin 3 × ℕ) (P : Auxiliary r)
    (g : Fin r → ℤ) : oscillatorPartial r v P g=pderiv v (P g) :=
  auxiliaryDerivative_apply r (pderiv v) P g

/-- Partial differentiation of a single auxiliary monomial. -/
theorem oscillatorPartial_single (r : ℕ) (v : Fin 3 × ℕ)
    (g : Fin r → ℤ) (p : WakFock) :
    oscillatorPartial r v (single g p)=single g (pderiv v p) :=
  coefficientDerivative_single r (pderiv v) g p

/-- The auxiliary power sum, with constant oscillator coefficient one. -/
def auxiliaryPowerSum (r m : ℕ) : Auxiliary r :=
  ∑ i : Fin r, single ((m : ℤ) • unitExponent r i) 1

/-- Differentiating the matching boson power yields its auxiliary power sum. -/
theorem oscillatorPartial_bosonPower (r m : ℕ) :
    oscillatorPartial r (2,m-1) (bosonPower r m)=auxiliaryPowerSum r m := by
  simp only [bosonPower,map_sum,oscillatorPartial_single,pderiv_X_self,auxiliaryPowerSum]

/-- Differentiating at a different positive boson mode gives zero. -/
theorem oscillatorPartial_bosonPower_ne (r m n : ℕ) (hm : 0<m) (hn : 0<n)
    (hne : m≠n) : oscillatorPartial r (2,m-1) (bosonPower r n)=0 := by
  have h : ((2,n-1) : Fin 3 × ℕ)≠(2,m-1) := by
    intro he
    have := congrArg Prod.snd he
    omega
  simp only [bosonPower,map_sum,oscillatorPartial_single,pderiv_X_of_ne h,
    AddMonoidAlgebra.single_zero,Finset.sum_const_zero]

/-- No beta factor depends on any boson variable. -/
theorem oscillatorPartial_betaFactor_boson (r N m : ℕ) (i : Fin r) :
    oscillatorPartial r (2,m) (betaFactor r N i)=0 := by
  simp only [betaFactor,map_sum,oscillatorPartial_single]
  apply Finset.sum_eq_zero
  intro j hj
  rw [pderiv_X_of_ne (show ((0,j) : Fin 3 × ℕ)≠(2,m) by
    intro h; have := congrArg Prod.fst h; exact (by decide : (0 : Fin 3)≠2) this),
    AddMonoidAlgebra.single_zero]

/-- The rational Vandermonde has no oscillator dependence at all. -/
theorem oscillatorPartial_delta (r : ℕ) (v : Fin 3 × ℕ) :
    oscillatorPartial r v (delta r)=0 := by
  ext g : 1
  rw [oscillatorPartial_apply]
  simp [delta,rationalConstants]
  rfl

/-- The finite exponential has its exact matching-mode derivative plus
an explicit final factorial term. The correction has not yet been dropped. -/
theorem exponentialFactor_boson_derivative (r N M m : ℕ) :
    oscillatorPartial r (2,m-1) (exponentialFactor r N M m) +
      (-(M : ℂ)/m) • (auxiliaryPowerSum r m *
        exponentialTerm r (-(M : ℂ)/m) (bosonPower r m) N) =
      (-(M : ℂ)/m) • (auxiliaryPowerSum r m * exponentialFactor r N M m) := by
  rw [exponentialFactor_eq_finiteExponential]
  simpa only [oscillatorPartial_bosonPower] using
    finiteExponential_derivative r (oscillatorPartial r (2,m-1))
      (-(M : ℂ)/m) (bosonPower r m) N

/-- A finite exponential at another positive boson mode differentiates to zero. -/
theorem exponentialFactor_boson_derivative_ne (r N M m n : ℕ)
    (hm : 0<m) (hn : 0<n) (hne : m≠n) :
    oscillatorPartial r (2,m-1) (exponentialFactor r N M n)=0 := by
  rw [exponentialFactor_eq_finiteExponential]
  have h := finiteExponential_derivative r (oscillatorPartial r (2,m-1))
    (-(M : ℂ)/n) (bosonPower r n) N
  simpa only [oscillatorPartial_bosonPower_ne r m n hm hn hne,
    zero_mul,smul_zero,add_zero] using h

/-- Multiplying oscillator coefficients by a scalar cannot lower their
auxiliary-degree support. -/
theorem LowerDegree.smul {r : ℕ} {d : ℤ} {P : Auxiliary r}
    (hP : LowerDegree d P) (c : ℂ) : LowerDegree d (c • P) := by
  intro g hg
  change c • P g=0
  rw [hP g hg,smul_zero]

/-- The auxiliary power sum has lower degree equal to its mode index. -/
theorem auxiliaryPowerSum_lower (r m : ℕ) :
    LowerDegree (m : ℤ) (auxiliaryPowerSum r m) := by
  apply LowerDegree.sum
  intro i hi
  exact LowerDegree.single r _ _ _ (by rw [exponentDegree_smul_unit])

/-- The actual factorial term has auxiliary degree at least mN. -/
theorem exponentialTerm_boson_lower (r M m N : ℕ) :
    LowerDegree ((N : ℤ)*m) (exponentialTerm r (-(M : ℂ)/m) (bosonPower r m) N) := by
  exact ((bosonPower_lower r m).pow N).smul _

/-- The terminal correction in the actual boson derivative has degree
at least m(N+1), not merely N. The power sum supplies the extra mode. -/
theorem exponential_derivative_error_lower (r N M m : ℕ) :
    LowerDegree ((m : ℤ)*(N+1))
      ((-(M : ℂ)/m) • (auxiliaryPowerSum r m *
        exponentialTerm r (-(M : ℂ)/m) (bosonPower r m) N)) := by
  have h := ((auxiliaryPowerSum_lower r m).mul (exponentialTerm_boson_lower r M m N)).smul (-(M : ℂ)/m)
  convert h using 1 <;> ring

/-- After Vandermonde extraction, the terminal boson derivative error
vanishes even with arbitrary remaining nonnegative-degree factors. -/
theorem exponential_derivative_error_zero (r q M m : ℕ) (hq : 0<q) (hm : 0<m)
    (Q : Auxiliary r) (hQ : LowerDegree 0 Q) :
    (delta r^(2*M)*(((-(M : ℂ)/m) • (auxiliaryPowerSum r m *
      exponentialTerm r (-(M : ℂ)/m) (bosonPower r m) (r*(q-1))))*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  apply screening_high_degree_product_zero r q M hq _ Q _ hQ
  apply (exponential_derivative_error_lower r (r*(q-1)) M m).mono
  have hq' : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
  have hm' : (1 : ℤ)≤m := by omega
  push_cast
  rw [hq']
  nlinarith [show (0 : ℤ)≤r*(q-1) by nlinarith]

/-- The ACTUAL boson derivative of a finite exponential has the expected
power-sum multiplier at the selected screening coefficient. The finite
terminal correction is proved to vanish here, not assumed away. -/
theorem selected_exponential_boson_derivative (r q M m : ℕ) (hq : 0<q) (hm : 0<m)
    (Q : Auxiliary r) (hQ : LowerDegree 0 Q) :
    (delta r^(2*M)*(oscillatorPartial r (2,m-1)
      (exponentialFactor r (r*(q-1)) M m)*Q))
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) =
    (delta r^(2*M)*(((-(M : ℂ)/m) •
      (auxiliaryPowerSum r m * exponentialFactor r (r*(q-1)) M m))*Q))
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  have h := congrArg (fun P : Auxiliary r => (delta r^(2*M)*(P*Q))
    (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)))
    (exponentialFactor_boson_derivative r (r*(q-1)) M m)
  dsimp only at h
  rw [add_mul,mul_add] at h
  change
    (delta r^(2*M)*(oscillatorPartial r (2,m-1)
      (exponentialFactor r (r*(q-1)) M m)*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) +
    (delta r^(2*M)*(((-(M : ℂ)/m) • (auxiliaryPowerSum r m *
      exponentialTerm r (-(M : ℂ)/m) (bosonPower r m) (r*(q-1))))*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) = _ at h
  rw [exponential_derivative_error_zero r q M m hq hm Q hQ,add_zero] at h
  simpa only [mul_assoc] using h

end
end VOA.Wak.Screening
