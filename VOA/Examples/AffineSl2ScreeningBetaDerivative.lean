/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningExponential

/-!
# Actual beta partials and finite shift boundaries

The beta derivative selects exactly one term of the finite beta factor.
The truncated lowering shift agrees with multiplication by an auxiliary
power after extraction: the difference has degree above the screening
cutoff. This is a coefficient identity, not yet a Ward equation for a current.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- A beta partial of a finite beta factor picks its matching auxiliary
monomial if the oscillator lies inside the cutoff, and is zero otherwise. -/
theorem oscillatorPartial_betaFactor (r D j : ℕ) (i : Fin r) :
    oscillatorPartial r (0,j) (betaFactor r D i)=
      if j≤D then single ((j : ℤ) • unitExponent r i) 1 else 0 := by
  classical
  simp only [betaFactor,map_sum,oscillatorPartial_single]
  by_cases hj : j≤D
  · rw [if_pos hj,Finset.sum_eq_single j]
    · rw [pderiv_X_self]
    · intro b hb hbj
      rw [pderiv_X_of_ne (by simpa using hbj : ((0,b) : Fin 3 × ℕ)≠(0,j)),
        AddMonoidAlgebra.single_zero]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro b hb
    have hbj : b≠j := by have := Finset.mem_range.mp hb; omega
    rw [pderiv_X_of_ne (by simpa using hbj : ((0,b) : Fin 3 × ℕ)≠(0,j)),
      AddMonoidAlgebra.single_zero]

/-- Beta differentiation does not change a boson power. -/
theorem oscillatorPartial_bosonPower_beta (r j m : ℕ) :
    oscillatorPartial r (0,j) (bosonPower r m)=0 := by
  simp only [bosonPower,map_sum,oscillatorPartial_single]
  apply Finset.sum_eq_zero
  intro i hi
  rw [pderiv_X_of_ne (show ((2,m-1) : Fin 3 × ℕ)≠(0,j) by
    intro h; have := congrArg Prod.fst h; exact (by decide : (2 : Fin 3)≠0) this),
    AddMonoidAlgebra.single_zero]

/-- Every boson exponential has zero beta partial, with no restriction on
its finite cutoff or on the mode. -/
theorem oscillatorPartial_exponentialFactor_beta (r D M m j : ℕ) :
    oscillatorPartial r (0,j) (exponentialFactor r D M m)=0 := by
  rw [exponentialFactor_eq_finiteExponential]
  have h := finiteExponential_derivative r (oscillatorPartial r (0,j))
    (-(M : ℂ)/m) (bosonPower r m) D
  simpa only [oscillatorPartial_bosonPower_beta,zero_mul,smul_zero,add_zero] using h

/-- The finite beta lowering shift on one factor. Each retained input
oscillator has depth j+n and is replaced by the oscillator of depth j. -/
def betaShiftFactor (r D n : ℕ) (i : Fin r) : Auxiliary r :=
  ∑ j∈Finset.range (D+1), if j+n≤D then
    single (((j+n : ℕ) : ℤ) • unitExponent r i) (X (0,j)) else 0

/-- This finite shifted expression is a sum of ACTUAL beta partials,
multiplied by their replacement creation variables. -/
theorem betaShiftFactor_eq_partials (r D n : ℕ) (i : Fin r) :
    betaShiftFactor r D n i =
      ∑ j∈Finset.range (D+1), single 0 (X (0,j))*
        oscillatorPartial r (0,j+n) (betaFactor r D i) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [oscillatorPartial_betaFactor]
  split_ifs <;> simp [single_mul_single]

/-- The difference between the finite beta shift and the auxiliary
monomial times the beta factor is supported strictly above D. This keeps
all truncation errors rather than deleting them by convention. -/
theorem betaShiftFactor_error_lower (r D n : ℕ) (i : Fin r) :
    LowerDegree (D+1 : ℤ)
      (single ((n : ℤ) • unitExponent r i) 1 * betaFactor r D i-
        betaShiftFactor r D n i) := by
  classical
  rw [betaFactor,betaShiftFactor,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply LowerDegree.sum
  intro j hj
  rw [single_mul_single,one_mul]
  have he : (n : ℤ) • unitExponent r i+(j : ℤ) • unitExponent r i=
      (((j+n : ℕ) : ℤ)) • unitExponent r i := by
    rw [← add_smul,Nat.cast_add,add_comm]
  rw [he]
  split_ifs with h
  · rw [sub_self]; exact LowerDegree.zero _ _
  · rw [sub_zero]
    apply LowerDegree.single
    rw [exponentDegree_smul_unit]
    exact_mod_cast (show D+1≤j+n by omega)

/-- After selecting the screening coefficient, the finite beta shift
is exactly auxiliary multiplication, even with arbitrary other factors
of nonnegative auxiliary degree. -/
theorem selected_betaShiftFactor (r q M n : ℕ) (hq : 0<q)
    (i : Fin r) (Q : Auxiliary r) (hQ : LowerDegree 0 Q) :
    (delta r^(2*M)*(betaShiftFactor r (r*(q-1)) n i*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) =
    (delta r^(2*M)*(((single ((n : ℤ) • unitExponent r i) 1 : Auxiliary r)*
      betaFactor r (r*(q-1)) i)*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  have herror := betaShiftFactor_error_lower r (r*(q-1)) n i
  have hcast : ((r*(q-1) : ℕ) : ℤ)+1=(r : ℤ)*(q-1)+1 := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
  rw [hcast] at herror
  have hz := screening_high_degree_product_zero r q M hq _ Q herror hQ
  rw [sub_mul,mul_sub] at hz
  change
    (delta r^(2*M)*(((single ((n : ℤ) • unitExponent r i) 1 : Auxiliary r)*
      betaFactor r (r*(q-1)) i)*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) -
    (delta r^(2*M)*(betaShiftFactor r (r*(q-1)) n i*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 at hz
  exact (sub_eq_zero.mp hz).symm

end
end VOA.Wak.Screening
