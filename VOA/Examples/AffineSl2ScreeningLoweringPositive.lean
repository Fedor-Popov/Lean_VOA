/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningLoweringResidual

/-!
# Positive-index form of the actual lowering residual

Remove the piecewise regions of the projected finite current formulas.
Terms outside the displayed positive intervals vanish by actual oscillator
truncation. The resulting formula has just first and second beta partials.
-/
namespace VOA.Wak.Screening
open MvPolynomial
open scoped BigOperators
noncomputable section

/-- A beta annihilation mode above the polynomial's actual cutoff vanishes. -/
theorem bD_above_cutoff (P : WakFock) (i : ℤ) (hi : NB P ≤ i) : bD i P=0 := by
  have hNB := two_le_NB P
  rw [bD_of_pos (by omega),dV_apply]
  exact pderiv_eq_zero_of_NB_le (by omega)

/-- After gamma projection, the gamma-gamma composite is the full finite
positive triangle. Extending its upper bound introduces only zero beta
annihilation terms. -/
theorem gammaErase_GG_triangle (P : WakFock) (hP : P∈gammaFree)
    (s : ℤ) (hs : 0<s) : gammaErase (GG s P)=
      ∑ u∈Finset.Icc 1 (s-1),bD (s-u) (bD u P) := by
  rw [gammaErase_GG_positive P hP s hs]
  apply Finset.sum_congr_of_eq_on_inter
  · intro u hu hout
    rw [if_neg (by simp only [Finset.mem_Icc] at hout; omega)]
  · intro u hu hout
    have hu' := Finset.mem_Icc.mp hu
    have hNB := two_le_NB P
    have hi : NB P≤u := by
      simp only [Finset.mem_Icc,not_and_or,not_le] at hout
      omega
    rw [bD_above_cutoff P u hi,map_zero]
  · intro u hu huv
    have huv' := Finset.mem_Icc.mp huv
    rw [if_pos (by omega)]

/-- Gamma projection of the boson-gamma term is the negative of a finite
positive-mode boson/beta contraction sum. -/
theorem gammaErase_AG_positive (k : ℂ) (P : WakFock) (hP : P∈gammaFree) :
    gammaErase (AG k 1 P)=
      -(∑ m∈Finset.Icc 1 (NB P-2),aV m*bD (m+1) P) := by
  rw [gammaErase_AG_one k P hP]
  have hNB := two_le_NB P
  have hrestrict : (∑ p∈Finset.Icc (min (2-NB P) 0) (NB P-1),
      if p≤-1 then -(aV (-p)*bD (1-p) P) else 0)=
      ∑ p∈Finset.Icc (2-NB P) (-1),-(aV (-p)*bD (1-p) P) := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro p hp hout
      have hp' := Finset.mem_Icc.mp hp
      rw [if_neg (by simp only [Finset.mem_Icc] at hout; omega)]
    · intro p hp hout
      have hp' := Finset.mem_Icc.mp hp
      exact False.elim (hout (Finset.mem_Icc.mpr (by constructor <;> omega)))
    · intro p hp hp2
      rw [if_pos (Finset.mem_Icc.mp hp2).2]
  rw [hrestrict,Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_bij (fun p _ => -p) ?_ ?_ ?_ ?_
  · intro p hp; have hp' := Finset.mem_Icc.mp hp
    apply Finset.mem_Icc.mpr; dsimp only; constructor <;> omega
  · intro p hp v hv he; dsimp only at he; omega
  · intro m hm; have hm' := Finset.mem_Icc.mp hm
    refine ⟨-m,Finset.mem_Icc.mpr ?_,by simp⟩
    constructor <;> omega
  · intro p hp
    dsimp only
    rw [show 1-p=-p+1 by omega]

/-- The projected triple ghost term is a finite positive triangle of
second beta partials, with the exact creation index fixed by mode balance. -/
theorem gammaErase_BGG_positive (P : WakFock) (hP : P∈gammaFree) :
    gammaErase (BGG 1 P)=
      ∑ m∈Finset.Icc 1 (2*NB P-2),bV m*
        ∑ u∈Finset.Icc 1 m,bD (m+1-u) (bD u P) := by
  rw [BGG_gammaFree P hP,map_sum]
  refine Finset.sum_bij (fun p _ => -p) ?_ ?_ ?_ ?_
  · intro p hp; have hp' := Finset.mem_Icc.mp hp
    apply Finset.mem_Icc.mpr; dsimp only; constructor <;> omega
  · intro p hp v hv he; dsimp only at he; omega
  · intro m hm; have hm' := Finset.mem_Icc.mp hm
    refine ⟨-m,Finset.mem_Icc.mpr ?_,by simp⟩
    constructor <;> omega
  · intro p hp
    have hp' := Finset.mem_Icc.mp hp
    dsimp only
    rw [map_mul,gammaErase_bV,gammaErase_GG_triangle P hP (1-p) (by omega)]
    simp only [show 1-p=-p+1 by omega,add_sub_cancel_right]

/-- On any gamma-independent polynomial, the projected lowering mode has
the positive-index formula with explicit first and second beta partials. -/
theorem gammaErase_F_one_positive (k lam : ℂ) (P : WakFock) (hP : P∈gammaFree) :
    gammaErase (Charged.F k lam 1 P)=
      -(∑ m∈Finset.Icc 1 (2*NB P-2),bV m*
        ∑ u∈Finset.Icc 1 m,bD (m+1-u) (bD u P)) -
      (∑ m∈Finset.Icc 1 (NB P-2),aV m*bD (m+1) P) +
      (k-lam) • bD 1 P := by
  have hf : Charged.F k lam 1 P=
      -BGG 1 P+AG k 1 P+(k-lam) • bD 1 P := by
    rw [Charged.F,Fcur]
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,
      LinearMap.smul_apply,Gam_of_pos (show (1 : ℤ)≥1 by omega),
      LinearMap.neg_apply,Int.cast_one,mul_one]
    module
  rw [hf,map_add,map_add,map_neg,map_smul,gammaErase_BGG_positive P hP,
    gammaErase_AG_positive k P hP,gammaErase_fixed _ (gammaFree_bD P hP 1)]
  simp only [sub_eq_add_neg]

/-- The ACTUAL lowering result on the screening state has no gamma terms
and equals this positive-index finite expression. Its vanishing still
requires the finite screening integration-by-parts identity. -/
theorem state_lowering_positive (r q M : ℕ) (hq : 0<q) (k lam : ℂ)
    (hMk : (M : ℂ)*(k+2)=1) :
    Charged.F k lam 1 (state r q M)=
      -(∑ m∈Finset.Icc 1 (2*NB (state r q M)-2),bV m*
        ∑ u∈Finset.Icc 1 m,bD (m+1-u) (bD u (state r q M))) -
      (∑ m∈Finset.Icc 1 (NB (state r q M)-2),aV m*bD (m+1) (state r q M)) +
      (k-lam) • bD 1 (state r q M) := by
  rw [← gammaErase_state_lowering r q M hq k lam hMk]
  exact gammaErase_F_one_positive k lam _ (fun j => state_gamma_derivative r q M j)

end
end VOA.Wak.Screening
