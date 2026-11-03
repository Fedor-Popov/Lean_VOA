/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningBosonState

/-!
# Finite beta lowering on the whole screening state

This sums actual oscillator partials before applying the finite product
rule. Its selected coefficient is an auxiliary power-sum insertion. The
finite sum is explicit; identifying it with the actual current's NB-bound
is a separate reindexing step.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Finite beta lowering as a genuine derivation of the auxiliary algebra. -/
def betaShiftDerivative (r D n : ℕ) : Derivation ℂ (Auxiliary r) (Auxiliary r) :=
  ∑ j∈Finset.range (D+1), (single 0 (X (0,j)) : Auxiliary r) •
    oscillatorPartial r (0,j+n)

/-- The finite derivation is exactly the displayed sum of oscillator partials. -/
theorem betaShiftDerivative_apply (r D n : ℕ) (P : Auxiliary r) :
    betaShiftDerivative r D n P=
      ∑ j∈Finset.range (D+1), single 0 (X (0,j))*oscillatorPartial r (0,j+n) P := by
  unfold betaShiftDerivative
  have h (S : Finset ℕ) :
      (∑ j∈S, (single 0 (X (0,j)) : Auxiliary r) • oscillatorPartial r (0,j+n)) P=
        ∑ j∈S,single 0 (X (0,j))*oscillatorPartial r (0,j+n) P := by
    classical
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,Derivation.zero_apply]
    | @insert j S hj ih =>
        rw [Finset.sum_insert hj,Finset.sum_insert hj,Derivation.add_apply,ih,
          Derivation.smul_apply,smul_eq_mul]
  exact h _

/-- On a beta factor, the actual finite derivation is the
finite shifted factor proved above, with the same cutoff. -/
theorem betaShiftDerivative_factor (r D n : ℕ) (i : Fin r) :
    betaShiftDerivative r D n (betaFactor r D i)=betaShiftFactor r D n i := by
  rw [betaShiftDerivative_apply,betaShiftFactor_eq_partials]

/-- The finite beta lowering derivation kills every boson exponential. -/
theorem betaShiftDerivative_exponential (r D n N M m : ℕ) :
    betaShiftDerivative r D n (exponentialFactor r N M m)=0 := by
  rw [betaShiftDerivative_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [oscillatorPartial_exponentialFactor_beta,mul_zero]

/-- The Vandermonde coefficients are constant under finite beta lowering. -/
theorem betaShiftDerivative_delta (r D n : ℕ) :
    betaShiftDerivative r D n (delta r)=0 := by
  rw [betaShiftDerivative_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [oscillatorPartial_delta,mul_zero]

/-- Summing the beta factors' multiplier equations gives a power sum for
the entire beta product, with all errors above its cutoff. -/
theorem beta_product_error (r D n : ℕ) :
    LowerDegree (D+1 : ℤ)
      (betaShiftDerivative r D n (∏ i : Fin r,betaFactor r D i)-
        auxiliaryPowerSum r n*(∏ i : Fin r,betaFactor r D i)) := by
  have he := derivative_error_prod (betaShiftDerivative r D n) (D+1 : ℤ)
    Finset.univ (betaFactor r D)
    (fun i => single ((n : ℤ) • unitExponent r i) 1)
    (fun i _ => betaFactor_lower r D i) (by
      intro i hi
      dsimp only
      rw [betaShiftDerivative_factor]
      have h := (betaShiftFactor_error_lower r D n i).neg
      convert h using 1 <;> ring)
  exact he

/-- Finite beta lowering of the complete integrand differentiates only
its beta product: the Vandermonde and boson factors contribute zero. -/
theorem betaShiftDerivative_integrand (r q M n : ℕ) :
    betaShiftDerivative r (r*(q-1)) n (integrand r q M)=
      delta r^(2*M)*(betaShiftDerivative r (r*(q-1)) n
        (∏ i : Fin r,betaFactor r (r*(q-1)) i))*
          (∏ j∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (j+1)) := by
  have he := derivative_prod_zero (betaShiftDerivative r (r*(q-1)) n)
    (Finset.range (r*(q-1))) (fun j => exponentialFactor r (r*(q-1)) M (j+1))
    (fun j _ => betaShiftDerivative_exponential r _ n _ M (j+1))
  rw [integrand,(betaShiftDerivative r (r*(q-1)) n).leibniz,he,
    (betaShiftDerivative r (r*(q-1)) n).leibniz,
    (betaShiftDerivative r (r*(q-1)) n).leibniz_pow,betaShiftDerivative_delta]
  simp only [smul_zero,zero_add,add_zero,mul_zero,smul_eq_mul]
  ring

/-- Extracting a coefficient of the finite beta derivation gives the
actual finite sum of beta creation variables times oscillator partials. -/
theorem betaShiftDerivative_coefficient (r D n : ℕ) (P : Auxiliary r)
    (g : Fin r → ℤ) : betaShiftDerivative r D n P g=
      ∑ j∈Finset.range (D+1), X (0,j)*pderiv (0,j+n) (P g) := by
  classical
  rw [betaShiftDerivative_apply]
  have h (S : Finset ℕ) :
      (∑ j∈S,(single 0 (X (0,j)) : Auxiliary r)*oscillatorPartial r (0,j+n) P) g=
        ∑ j∈S,X (0,j)*pderiv (0,j+n) (P g) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; rfl
    | @insert j S hj ih =>
        rw [Finset.sum_insert hj,Finset.sum_insert hj]
        change ((single 0 (X (0,j)) : Auxiliary r)*oscillatorPartial r (0,j+n) P) g+
          (∑ l∈S,(single 0 (X (0,l)) : Auxiliary r)*oscillatorPartial r (0,l+n) P) g=_
        rw [ih,AddMonoidAlgebra.single_zero_mul_apply,oscillatorPartial_apply]
  exact h _

/-- The actual finite beta lowering sum on the whole state is exactly the
auxiliary power-sum insertion, including its finite boundary cancellations. -/
theorem state_beta_shift (r q M n : ℕ) (hq : 0<q) :
    (∑ j∈Finset.range (r*(q-1)+1), X (0,j)*pderiv (0,j+n) (state r q M))=
      (auxiliaryPowerSum r n*integrand r q M)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  let B := ∏ i : Fin r,betaFactor r (r*(q-1)) i
  let E := ∏ j∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (j+1)
  let D := betaShiftDerivative r (r*(q-1)) n
  have he : LowerDegree 0 E := lowerDegree_prod_zero _ _ (fun j _ => exponentialFactor_lower r _ M _)
  have hb : LowerDegree ((r*(q-1) : ℕ)+1 : ℤ) (D B-auxiliaryPowerSum r n*B) :=
    beta_product_error r _ n
  have hc : (((r*(q-1) : ℕ) : ℤ)+1)=(r : ℤ)*(q-1)+1 := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
  rw [hc] at hb
  have hz := screening_high_degree_product_zero r q M hq _ E hb he
  have ha : D (integrand r q M)-auxiliaryPowerSum r n*integrand r q M=
      delta r^(2*M)*((D B-auxiliaryPowerSum r n*B)*E) := by
    dsimp only [D]
    rw [betaShiftDerivative_integrand,integrand]
    dsimp only [B,E]
    ring
  rw [← ha] at hz
  change (D (integrand r q M)) _-(auxiliaryPowerSum r n*integrand r q M) _=0 at hz
  rw [betaShiftDerivative_coefficient] at hz
  exact sub_eq_zero.mp hz

/-- The actual screening state contains no beta oscillator above the
finite factor cutoff. This is proved by differentiating every factor. -/
theorem state_beta_derivative_above (r q M j : ℕ) (hj : r*(q-1)<j) :
    pderiv (0,j) (state r q M)=0 := by
  have hb := derivative_prod_zero (oscillatorPartial r (0,j)) Finset.univ
    (betaFactor r (r*(q-1))) (by
      intro i hi
      rw [oscillatorPartial_betaFactor,if_neg (by omega)])
  have he := derivative_prod_zero (oscillatorPartial r (0,j))
    (Finset.range (r*(q-1))) (fun m => exponentialFactor r (r*(q-1)) M (m+1))
    (fun m _ => oscillatorPartial_exponentialFactor_beta r _ M _ j)
  rw [state,← oscillatorPartial_apply,integrand,
    (oscillatorPartial r (0,j)).leibniz,he,
    (oscillatorPartial r (0,j)).leibniz,hb,
    (oscillatorPartial r (0,j)).leibniz_pow,oscillatorPartial_delta]
  simp only [smul_zero,add_zero,zero_smul]
  rfl

end
end VOA.Wak.Screening
