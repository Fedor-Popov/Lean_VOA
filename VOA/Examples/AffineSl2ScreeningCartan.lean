/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningBetaState
import VOA.Examples.AffineSl2ScreeningOperators

/-!
# Actual positive Cartan annihilation of the finite screening state

Reindex the actual current's integer interval into oscillator depths.
Oscillator independence makes the bound agree with the finite screening
cutoff. The whole-state beta and boson identities then cancel exactly.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- The actual integer-indexed beta part of a positive Cartan current is
the natural-depth oscillator sum, with the same NB truncation bound. -/
theorem cartan_beta_sum_reindex (P : WakFock) (n : ℕ) (hn : 0<n) :
    (∑ p∈Finset.Icc (1-NB P) (-1), bV (-p)*bD ((n : ℤ)-p) P)=
      ∑ j∈Finset.range (NB P-1).toNat, X (0,j)*pderiv (0,j+n) P := by
  classical
  have hNB := two_le_NB P
  refine Finset.sum_bij (fun p _ => (-p-1).toNat) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_Icc.mp hp
    apply Finset.mem_range.mpr
    dsimp only
    omega
  · intro p hp q hq he
    have hp' := Finset.mem_Icc.mp hp
    have hq' := Finset.mem_Icc.mp hq
    dsimp only at he
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨-(j : ℤ)-1,?_,?_⟩
    · apply Finset.mem_Icc.mpr; constructor <;> omega
    · dsimp only; omega
  · intro p hp
    have hp' := Finset.mem_Icc.mp hp
    rw [bV_of_pos (by omega),bD_of_pos (by omega),dV_apply]
    dsimp only
    have hi : ((n : ℤ)-p-1).toNat=(-p-1).toNat+n := by omega
    rw [hi]

/-- Any proved oscillator cutoff can replace the current's NB cutoff.
The added or removed summands have zero actual partial derivatives. -/
theorem cartan_beta_sum_cutoff (P : WakFock) (n D : ℕ) (hn : 0<n)
    (hD : ∀ j, D<j → pderiv (0,j) P=0) :
    (∑ j∈Finset.range (NB P-1).toNat, X (0,j)*pderiv (0,j+n) P)=
      ∑ j∈Finset.range (D+1), X (0,j)*pderiv (0,j+n) P := by
  classical
  let F := fun j => X (0,j)*pderiv (0,j+n) P
  have hNB := two_le_NB P
  have hleft : (∑ j∈Finset.range (NB P-1).toNat,F j)=
      ∑ j∈Finset.range (max (NB P-1).toNat (D+1)),F j := by
    apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
    intro j hj hjnot
    have hj' : (NB P-1).toNat≤j := by simpa using hjnot
    dsimp only [F]
    rw [pderiv_eq_zero_of_NB_le (by omega),mul_zero]
  have hright : (∑ j∈Finset.range (D+1),F j)=
      ∑ j∈Finset.range (max (NB P-1).toNat (D+1)),F j := by
    apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
    intro j hj hjnot
    have hj' : D+1≤j := by simpa using hjnot
    dsimp only [F]
    rw [hD (j+n) (by omega),mul_zero]
  exact hleft.trans hright.symm

/-- Actual positive charged Cartan modes on a gamma-independent polynomial
can use any explicit cutoff containing all of its beta oscillators. -/
theorem H_positive_explicit_cutoff (k lam : ℂ) (P : WakFock) (hP : P∈gammaFree)
    (n D : ℕ) (hn : 0<n) (hD : ∀ j, D<j → pderiv (0,j) P=0) :
    Charged.H k lam (n : ℤ) P=
      (2 : ℂ) • (∑ j∈Finset.range (D+1),X (0,j)*pderiv (0,j+n) P)+
      ((2*(k+2))*(n : ℂ)) • pderiv (2,n-1) P := by
  rw [H_positive_gammaFree k lam P hP (n : ℤ) (by exact_mod_cast hn),
    cartan_beta_sum_reindex P n hn,cartan_beta_sum_cutoff P n D hn hD,
    aD_of_pos (by exact_mod_cast hn),dV_apply]
  have hi : ((n : ℤ)-1).toNat=n-1 := by omega
  simp only [hi,Int.cast_natCast]

/-- Every ACTUAL positive Cartan mode kills the finite screening state
when M(k+2)=1. The proof combines the finite whole-state identities and
both cutoff cancellations; no Cartan Ward hypothesis is assumed. -/
theorem state_positive_cartan (r q M n : ℕ) (hq : 0<q) (hn : 0<n)
    (k lam : ℂ) (hMk : (M : ℂ)*(k+2)=1) :
    Charged.H k lam (n : ℤ) (state r q M)=0 := by
  rw [H_positive_explicit_cutoff k lam (state r q M)
    (by intro j; exact state_gamma_derivative r q M j) n (r*(q-1)) hn
    (fun j hj => state_beta_derivative_above r q M j hj),
    state_beta_shift r q M n hq,state_boson_derivative r q M n hq hn,
    smul_smul,← add_smul]
  have hn' : (n : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : (2 : ℂ)+((2*(k+2))*(n : ℂ))*(-(M : ℂ)/n)=0 := by
    field_simp
    linear_combination -2*hMk
  rw [hc,zero_smul]

end
end VOA.Wak.Screening
