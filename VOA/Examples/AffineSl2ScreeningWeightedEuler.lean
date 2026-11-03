/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningBetaPairs
import VOA.Examples.AffineSl2ScreeningDividedDifference

/-!
# Weighted Vandermonde differentiation for the actual affine screening

Weighting each Euler derivative by the beta product with that variable
omitted makes every Vandermonde difference an eigenvector with a polynomial
multiplier. This proves the pairwise derivative formula without dividing
by differences of auxiliary variables.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- The beta product with one factor omitted. -/
def betaOmit (r N : ℕ) (i : Fin r) : Auxiliary r :=
  ∏ j∈Finset.univ.erase i,betaFactor r N j

/-- The beta product with two factors omitted. -/
def betaOmitPair (r N : ℕ) (i j : Fin r) : Auxiliary r :=
  ∏ l∈(Finset.univ.erase i).erase j,betaFactor r N l

/-- Restoring the second omitted factor recovers the single omission. -/
theorem betaOmitPair_restore (r N : ℕ) (i j : Fin r) (hij : i≠j) :
    betaFactor r N j*betaOmitPair r N i j=betaOmit r N i := by
  classical
  exact Finset.mul_prod_erase _ _ (by simp [Ne.symm hij])

/-- Two omissions do not depend on their order. -/
theorem betaOmitPair_swap (r N : ℕ) (i j : Fin r) :
    betaOmitPair r N i j=betaOmitPair r N j i := by
  have he : (Finset.univ.erase i).erase j=(Finset.univ.erase j).erase i := by
    ext l
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    exact and_comm
  rw [betaOmitPair,betaOmitPair,he]

/-- The polynomially weighted Euler derivation associated to all omissions. -/
def weightedEuler (r N : ℕ) : Derivation ℂ (Auxiliary r) (Auxiliary r) :=
  ∑ i : Fin r,betaOmit r N i • auxiliaryEuler i

/-- The weighted derivation is the literal finite sum of weighted derivatives. -/
theorem weightedEuler_apply (r N : ℕ) (P : Auxiliary r) :
    weightedEuler r N P=∑ i : Fin r,betaOmit r N i*auxiliaryEuler i P := by
  classical
  unfold weightedEuler
  have hs (S : Finset (Fin r)) :
      (∑ i∈S,betaOmit r N i • auxiliaryEuler i) P=
        ∑ i∈S,betaOmit r N i*auxiliaryEuler i P := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi,Finset.sum_insert hi,Derivation.add_apply,
          Derivation.smul_apply,ih,smul_eq_mul]
  exact hs Finset.univ

/-- An auxiliary coordinate differentiates only in its own Euler variable. -/
theorem auxiliaryEuler_variable (r : ℕ) (i j : Fin r) :
    auxiliaryEuler i (auxiliaryVariable r j)=
      if i=j then auxiliaryVariable r j else 0 := by
  classical
  rw [auxiliaryVariable,auxiliaryEuler_single]
  by_cases h : i=j
  · subst j; simp [unitExponent]
  · simp [unitExponent,Pi.single_eq_of_ne h,h]
    rfl

/-- The weighted derivative of one coordinate restores its omitted beta weight. -/
theorem weightedEuler_variable (r N : ℕ) (i : Fin r) :
    weightedEuler r N (auxiliaryVariable r i)=betaOmit r N i*auxiliaryVariable r i := by
  rw [weightedEuler_apply]
  simp [auxiliaryEuler_variable]

/-- Every Vandermonde difference has a polynomial logarithmic multiplier.
No inverse difference is used, even when variables coincide. -/
theorem weightedEuler_difference (r N : ℕ) (i j : Fin r) (hij : i≠j) :
    weightedEuler r N (auxiliaryVariable r i-auxiliaryVariable r j)=
      (auxiliaryVariable r i-auxiliaryVariable r j)*
        (betaCompanion r N i j*betaOmitPair r N i j) := by
  rw [map_sub,weightedEuler_variable,weightedEuler_variable,
    ← betaOmitPair_restore r N i j hij,← betaOmitPair_restore r N j i (Ne.symm hij),
    ← betaOmitPair_swap r N i j]
  calc
    _ = (auxiliaryVariable r i*betaFactor r N j-
      auxiliaryVariable r j*betaFactor r N i)*betaOmitPair r N i j := by ring
    _ = _ := by rw [← betaCompanion_mul]; ring

/-- A finite product of derivation eigenvectors has the sum of their
polynomial multipliers. This remains valid without invertibility. -/
theorem derivation_product_multipliers {A I : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (S : Finset I) (f g : I→A)
    (h : ∀ i∈S,D (f i)=f i*g i) :
    D (∏ i∈S,f i)=(∏ i∈S,f i)*(∑ i∈S,g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,D.leibniz,
        h i (by simp),ih (fun j hj => h j (by simp [hj]))]
      simp only [smul_eq_mul]
      ring

/-- Exact weighted differentiation of the actual Vandermonde. -/
theorem weightedEuler_delta (r N : ℕ) :
    weightedEuler r N (delta r)=delta r*
      ∑ ij∈variablePairs r,betaCompanion r N ij.1 ij.2*betaOmitPair r N ij.1 ij.2 := by
  rw [delta_product]
  apply derivation_product_multipliers
  intro ij hij
  exact weightedEuler_difference r N ij.1 ij.2
    (ne_of_lt (Finset.mem_filter.mp hij).2)

/-- Exact weighted differentiation of every even Vandermonde power. -/
theorem weightedEuler_delta_power (r N M : ℕ) :
    weightedEuler r N (delta r^(2*M))=(2*M : ℂ) •
      (delta r^(2*M)*∑ ij∈variablePairs r,
        betaCompanion r N ij.1 ij.2*betaOmitPair r N ij.1 ij.2) := by
  cases M with
  | zero => simp
  | succ M =>
      rw [(weightedEuler r N).leibniz_pow,weightedEuler_delta]
      simp only [smul_eq_mul]
      rw [← mul_assoc,← pow_succ]
      have h : 2*(M+1)-1+1=2*(M+1) := by omega
      simp only [h]
      push_cast
      simp only [Algebra.smul_def,map_add,map_mul,map_natCast]
      norm_num only [map_ofNat,map_one]
      rw [show (algebraMap ℕ (Auxiliary r)) M=(M : Auxiliary r) from map_natCast _ M]

end
end VOA.Wak.Screening
