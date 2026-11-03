/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningEulerExponential

/-!
# Finite integration by parts with one beta factor omitted

Each first beta partial removes one beta factor from the integrand. Euler
differentiation in its auxiliary variable kills all the remaining beta
factors. The identity below separates the Vandermonde derivative from the
boson insertion with every exponential boundary term proved irrelevant.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- The actual screening integrand with beta factor i removed. -/
def omittedIntegrand (r q M : ℕ) (i : Fin r) : Auxiliary r :=
  delta r^(2*M)*(∏ j∈Finset.univ.erase i,betaFactor r (r*(q-1)) j)*
    ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1)

/-- The omitted beta product has nonnegative auxiliary degree. -/
theorem omittedBeta_lower (r D : ℕ) (i : Fin r) :
    LowerDegree 0 (∏ j∈Finset.univ.erase i,betaFactor r D j) := by
  classical
  exact lowerDegree_prod_zero _ _ (fun j _ => betaFactor_lower r D j)

/-- Exact finite integration by parts on the actual omitted integrand.
The boson insertion equals the Vandermonde derivative contribution minus
the selected exponent contribution, divided only formally by keeping M
on the left. No inverse M or analytic contour is used in the theorem. -/
theorem omittedIntegrand_ibp (r q M : ℕ) (hq : 0<q) (i : Fin r) :
    (M : ℂ) • ((bosonAuxiliarySeries r (r*(q-1)) i*omittedIntegrand r q M i)
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) =
    (auxiliaryEuler i (delta r^(2*M))*
      ((∏ j∈Finset.univ.erase i,betaFactor r (r*(q-1)) j)*
        ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1)))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) -
    (((r-1)*M+q-1 : ℕ) : ℂ) • (omittedIntegrand r q M i)
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  classical
  let B := ∏ j∈Finset.univ.erase i,betaFactor r (r*(q-1)) j
  let E := ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1)
  let a := (-(M : ℂ)) • bosonAuxiliarySeries r (r*(q-1)) i
  have he : LowerDegree (((r*(q-1) : ℕ) : ℤ)+1)
      (auxiliaryEuler i E-a*E) := auxiliaryEuler_exponential_product_error r _ M i
  have hc : (((r*(q-1) : ℕ) : ℤ)+1)=(r : ℤ)*(q-1)+1 := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
  rw [hc] at he
  have herr : LowerDegree ((r : ℤ)*(q-1)+1) (B*(auxiliaryEuler i E-a*E)) := by
    simpa using (omittedBeta_lower r (r*(q-1)) i).mul he
  have hz := screening_high_degree_zero r q M hq _ herr
  have ha : auxiliaryEuler i (omittedIntegrand r q M i)-a*omittedIntegrand r q M i-
      auxiliaryEuler i (delta r^(2*M))*(B*E)=
      delta r^(2*M)*(B*(auxiliaryEuler i E-a*E)) := by
    rw [omittedIntegrand,(auxiliaryEuler i).leibniz,(auxiliaryEuler i).leibniz,
      auxiliaryEuler_beta_omitted]
    simp only [smul_eq_mul,mul_zero,add_zero]
    dsimp only [B,E]
    ring
  rw [← ha] at hz
  change (auxiliaryEuler i (omittedIntegrand r q M i)) _-
    (a*omittedIntegrand r q M i) _-
    (auxiliaryEuler i (delta r^(2*M))*(B*E)) _=0 at hz
  rw [auxiliaryEuler_apply] at hz
  have hs : a*omittedIntegrand r q M i=(-(M : ℂ)) •
      (bosonAuxiliarySeries r (r*(q-1)) i*omittedIntegrand r q M i) :=
    smul_mul_assoc _ _ _
  rw [hs] at hz
  change (((r-1)*M+q-1 : ℕ) : ℂ) • (omittedIntegrand r q M i) _-
    (-(M : ℂ)) • (bosonAuxiliarySeries r (r*(q-1)) i*omittedIntegrand r q M i) _-
    (auxiliaryEuler i (delta r^(2*M))*(B*E)) _=0 at hz
  simp only [neg_smul] at hz
  change (M : ℂ) • _ = (auxiliaryEuler i (delta r^(2*M))*(B*E)) _-_
  linear_combination hz

end
end VOA.Wak.Screening
