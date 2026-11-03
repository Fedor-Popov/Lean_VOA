/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningBetaDerivative

/-!
# Finite Leibniz estimates for the entire screening product

An error supported above the auxiliary cutoff stays above it when multiplied
by any remaining nonnegative-degree factors. This proves the product rule
for the truncated factors without replacing them by infinite exponentials.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Adding two errors preserves their common lower auxiliary degree. -/
theorem LowerDegree.add {r : ℕ} {d : ℤ} {P Q : Auxiliary r}
    (hP : LowerDegree d P) (hQ : LowerDegree d Q) : LowerDegree d (P+Q) := by
  intro g hg
  change P g+Q g=0
  rw [hP g hg,hQ g hg,add_zero]

/-- Negation does not change the lower auxiliary-degree bound. -/
theorem LowerDegree.neg {r : ℕ} {d : ℤ} {P : Auxiliary r}
    (hP : LowerDegree d P) : LowerDegree d (-P) := by
  intro g hg
  change -(P g)=0
  rw [hP g hg,neg_zero]

/-- A finite product of nonnegative-degree factors still has nonnegative degree. -/
theorem lowerDegree_prod_zero {r : ℕ} {I : Type*} (S : Finset I)
    (P : I → Auxiliary r) (hP : ∀ i∈S, LowerDegree 0 (P i)) :
    LowerDegree 0 (∏ i∈S, P i) := by
  simpa using LowerDegree.prod S (fun _ => 0) P hP

/-- If derivatives of two factors equal specified multipliers up to
high-degree errors, the derivative of their product has the sum multiplier
up to a high-degree error. -/
theorem derivative_error_mul {r : ℕ} (D : Derivation ℂ (Auxiliary r) (Auxiliary r))
    (d : ℤ) (P Q a b : Auxiliary r) (hP : LowerDegree 0 P) (hQ : LowerDegree 0 Q)
    (heP : LowerDegree d (D P-a*P)) (heQ : LowerDegree d (D Q-b*Q)) :
    LowerDegree d (D (P*Q)-(a+b)*(P*Q)) := by
  have hp : LowerDegree d ((D P-a*P)*Q) := by simpa using heP.mul hQ
  have hq : LowerDegree d (P*(D Q-b*Q)) := by simpa using hP.mul heQ
  convert hp.add hq using 1
  rw [D.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The whole finite product inherits the factor derivative identities,
with the multiplier summed over every factor and every error retained above
the same cutoff. -/
theorem derivative_error_prod {r : ℕ} {I : Type*}
    (D : Derivation ℂ (Auxiliary r) (Auxiliary r)) (d : ℤ)
    (S : Finset I) (P a : I → Auxiliary r)
    (hP : ∀ i∈S, LowerDegree 0 (P i))
    (he : ∀ i∈S, LowerDegree d (D (P i)-a i*P i)) :
    LowerDegree d (D (∏ i∈S,P i)-(∑ i∈S,a i)*(∏ i∈S,P i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,D.map_one_eq_zero,
      zero_mul,sub_self]; exact LowerDegree.zero r d
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi]
      exact derivative_error_mul D d _ _ _ _ (hP i (by simp))
        (lowerDegree_prod_zero S P (fun j hj => hP j (by simp [hj])))
        (he i (by simp))
        (ih (fun j hj => hP j (by simp [hj])) (fun j hj => he j (by simp [hj])))

/-- A derivation killing each factor kills their finite product exactly. -/
theorem derivative_prod_zero {r : ℕ} {I : Type*}
    (D : Derivation ℂ (Auxiliary r) (Auxiliary r)) (S : Finset I)
    (P : I → Auxiliary r) (h : ∀ i∈S,D (P i)=0) : D (∏ i∈S,P i)=0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,D.map_one_eq_zero]
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi,D.leibniz,h i (by simp),
        ih (fun j hj => h j (by simp [hj]))]
      simp

end
end VOA.Wak.Screening
