/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningSelectedSums

/-!
# Screening cutoffs in the actual lowering operator

Integer mode sums are reindexed by oscillator depth. Their actual NB bounds
can be replaced by the screening degree because all changed derivatives
vanish, including quadratic terms beyond the total depth cutoff.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Reindex the actual boson-beta sum by natural oscillator depth. -/
theorem lowering_boson_reindex (P : WakFock) :
    (∑ m∈Finset.Icc 1 (NB P-2),aV m*bD (m+1) P)=
      ∑ j∈Finset.range (NB P-2).toNat,X (2,j)*pderiv (0,j+1) P := by
  have hNB := two_le_NB P
  refine Finset.sum_bij (fun m _ => (m-1).toNat) ?_ ?_ ?_ ?_
  · intro m hm
    have := Finset.mem_Icc.mp hm
    apply Finset.mem_range.mpr
    dsimp only
    omega
  · intro m hm n hn he
    have := Finset.mem_Icc.mp hm
    have := Finset.mem_Icc.mp hn
    dsimp only at he
    omega
  · intro j hj
    have := Finset.mem_range.mp hj
    refine ⟨(j : ℤ)+1,Finset.mem_Icc.mpr (by constructor <;> omega),by simp⟩
  · intro m hm
    have := Finset.mem_Icc.mp hm
    rw [aV_of_pos (by omega),bD_of_pos (by omega),dV_apply]
    dsimp only
    rw [show (m+1-1).toNat=(m-1).toNat+1 by omega]

/-- Replace the boson sum bound by any proved beta depth cutoff. -/
theorem lowering_boson_cutoff (P : WakFock) (N : ℕ)
    (hN : ∀ j,N<j → pderiv (0,j) P=0) :
    (∑ j∈Finset.range (NB P-2).toNat,X (2,j)*pderiv (0,j+1) P)=
      ∑ j∈Finset.range N,X (2,j)*pderiv (0,j+1) P := by
  have hNB := two_le_NB P
  apply Finset.sum_congr_of_eq_on_inter
  · intro j hj hout
    have : N≤j := by simpa using hout
    rw [hN (j+1) (by omega),mul_zero]
  · intro j hj hout
    have : (NB P-2).toNat≤j := by simpa using hout
    rw [pderiv_eq_zero_of_NB_le (by omega),mul_zero]
  · intro j hj hj2
    rfl

/-- The inner positive-mode triangle is the finite natural antidiagonal
of two beta depths. -/
theorem lowering_inner_reindex (P : WakFock) (m : ℤ) (hm : 1≤m) :
    (∑ u∈Finset.Icc 1 m,bD (m+1-u) (bD u P))=
      ∑ a∈Finset.range ((m-1).toNat+1),
        pderiv (0,(m-1).toNat-a) (pderiv (0,a) P) := by
  refine Finset.sum_bij (fun u _ => (u-1).toNat) ?_ ?_ ?_ ?_
  · intro u hu
    have := Finset.mem_Icc.mp hu
    apply Finset.mem_range.mpr
    dsimp only
    omega
  · intro u hu v hv he
    have := Finset.mem_Icc.mp hu
    have := Finset.mem_Icc.mp hv
    dsimp only at he
    omega
  · intro a ha
    have := Finset.mem_range.mp ha
    refine ⟨(a : ℤ)+1,Finset.mem_Icc.mpr (by constructor <;> omega),by simp⟩
  · intro u hu
    have := Finset.mem_Icc.mp hu
    rw [bD_of_pos (by omega : 1≤m+1-u),bD_of_pos (by omega : 1≤u),dV_apply,dV_apply]
    dsimp only
    have he : (m+1-u-1).toNat=(m-1).toNat-(u-1).toNat := by omega
    rw [he]

/-- Reindex the actual quadratic-beta sum by total natural depth. -/
theorem lowering_quadratic_reindex (P : WakFock) :
    (∑ m∈Finset.Icc 1 (2*NB P-2),bV m*
      ∑ u∈Finset.Icc 1 m,bD (m+1-u) (bD u P))=
    ∑ d∈Finset.range (2*NB P-2).toNat,X (0,d)*
      ∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) P) := by
  have hNB := two_le_NB P
  refine Finset.sum_bij (fun m _ => (m-1).toNat) ?_ ?_ ?_ ?_
  · intro m hm
    have := Finset.mem_Icc.mp hm
    apply Finset.mem_range.mpr
    dsimp only
    omega
  · intro m hm n hn he
    have := Finset.mem_Icc.mp hm
    have := Finset.mem_Icc.mp hn
    dsimp only at he
    omega
  · intro d hd
    have := Finset.mem_range.mp hd
    refine ⟨(d : ℤ)+1,Finset.mem_Icc.mpr (by constructor <;> omega),by simp⟩
  · intro m hm
    have := Finset.mem_Icc.mp hm
    rw [bV_of_pos (by omega),lowering_inner_reindex P m (by omega)]

/-- Beyond twice the actual oscillator bound, every term in a quadratic
antidiagonal is zero because at least one derivative is absent. -/
theorem quadratic_term_above_NB (P : WakFock) (d a : ℕ)
    (hd : (2*NB P-2).toNat≤d) (ha : a≤d) :
    pderiv (0,d-a) (pderiv (0,a) P)=0 := by
  have hNB := two_le_NB P
  by_cases h : NB P≤(a : ℤ)+1
  · rw [pderiv_eq_zero_of_NB_le h,map_zero]
  · rw [pderiv_comm',pderiv_eq_zero_of_NB_le (P := P) (a := 0) (i := d-a) (by omega),map_zero]

/-- The actual quadratic-beta bound can be replaced by the screening
total depth bound, including cases where the two cutoffs differ either way. -/
theorem state_lowering_quadratic_cutoff (r q M : ℕ) (hq : 0<q) :
    (∑ d∈Finset.range (2*NB (state r q M)-2).toNat,X (0,d)*
      ∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) (state r q M)))=
    ∑ d∈Finset.range (r*(q-1)+1),X (0,d)*
      ∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) (state r q M)) := by
  apply Finset.sum_congr_of_eq_on_inter
  · intro d hd hout
    have hd' : r*(q-1)<d := by simpa using hout
    have hz : (∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) (state r q M)))=0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have := Finset.mem_range.mp ha
      exact state_beta_double_above_degree r q M a (d-a) hq (by omega)
    rw [hz,mul_zero]
  · intro d hd hout
    have hd' : (2*NB (state r q M)-2).toNat≤d := by simpa using hout
    have hz : (∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) (state r q M)))=0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact quadratic_term_above_NB _ d a hd' (by have := Finset.mem_range.mp ha; omega)
    rw [hz,mul_zero]
  · intro d hd hd2
    rfl

/-- The ACTUAL lowering current is expressed entirely with the natural
screening cutoffs, rather than the implementation's NB bounds. -/
theorem state_lowering_natural (r q M : ℕ) (hq : 0<q) (k lam : ℂ)
    (hMk : (M : ℂ)*(k+2)=1) :
    Charged.F k lam 1 (state r q M)=
      -(∑ d∈Finset.range (r*(q-1)+1),X (0,d)*
        ∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) (state r q M))) -
      (∑ j∈Finset.range (r*(q-1)),X (2,j)*pderiv (0,j+1) (state r q M)) +
      (k-lam) • bD 1 (state r q M) := by
  rw [state_lowering_positive r q M hq k lam hMk,lowering_boson_reindex,
    lowering_boson_cutoff _ (r*(q-1)) (fun j hj => state_beta_derivative_above r q M j hj),
    lowering_quadratic_reindex,state_lowering_quadratic_cutoff r q M hq]

end
end VOA.Wak.Screening
