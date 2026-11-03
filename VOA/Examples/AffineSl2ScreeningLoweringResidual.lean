/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningGammaProjection

/-!
# The actual gamma-free lowering residual

Projecting the actual finite current formulas kills every gamma tail.
On the screening state the projection is the identity on F_1 S, by the
proved positive Cartan equations. The resulting finite expression contains
only beta first and second partials and boson creation variables.
-/
namespace VOA.Wak.Screening
open MvPolynomial
open scoped BigOperators
noncomputable section

/-- The projected positive gamma-gamma composite contains only its finite
second-partial middle. Both creation/derivative tails vanish under projection. -/
theorem gammaErase_GG_positive (P : WakFock) (hP : P∈gammaFree)
    (s : ℤ) (hs : 0<s) : gammaErase (GG s P)=
    ∑ u∈Finset.Icc (min (s-NB P+1) 0) (NB P-1),
      if 0<u ∧ u<s then bD (s-u) (bD u P) else 0 := by
  rw [GG_positive P s hs,map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h0 : u≤0
  · rw [if_pos h0,map_neg,map_mul,gammaErase_cV,zero_mul,neg_zero,
      if_neg (by omega)]
  · rw [if_neg h0]
    by_cases hus : u<s
    · rw [if_pos hus,if_pos (by omega)]
      exact gammaErase_fixed _ (gammaFree_bD _ (gammaFree_bD P hP u) (s-u))
    · rw [if_neg hus,map_neg,map_mul,gammaErase_cV,zero_mul,neg_zero,
        if_neg (by omega)]

/-- Projecting the actual index-one boson-gamma composite leaves just its
negative-index boson creation times beta partial sum. -/
theorem gammaErase_AG_one (k : ℂ) (P : WakFock) (hP : P∈gammaFree) :
    gammaErase (AG k 1 P)=
      ∑ p∈Finset.Icc (min (2-NB P) 0) (NB P-1),
        if p≤-1 then -(aV (-p)*bD (1-p) P) else 0 := by
  rw [AG_one k P,map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hn : p≤-1
  · rw [if_pos hn,map_neg,map_mul,gammaErase_aV,
      gammaErase_fixed _ (gammaFree_bD P hP (1-p)),if_pos hn]
  · rw [if_neg hn,map_smul,map_mul,gammaErase_cV,zero_mul,smul_zero,if_neg hn]

/-- The finite gamma-free residual of the actual lowering mode. Every
bound is retained from the actual normal-ordered currents; its vanishing
requires a further screening integration-by-parts calculation. -/
def loweringResidual (k lam : ℂ) (P : WakFock) : WakFock :=
    -(∑ p∈Finset.Icc (2-2*NB P) (-1), bV (-p)*
      ∑ u∈Finset.Icc (min (1-p-NB P+1) 0) (NB P-1),
        if 0<u ∧ u<1-p then bD (1-p-u) (bD u P) else 0) +
    (∑ p∈Finset.Icc (min (2-NB P) 0) (NB P-1),
      if p≤-1 then -(aV (-p)*bD (1-p) P) else 0) +
    (k-lam) • bD 1 P

/-- The projection of the ACTUAL charged lowering mode equals the finite
residual on every gamma-independent input. No Ward equation is assumed. -/
theorem gammaErase_F_one (k lam : ℂ) (P : WakFock) (hP : P∈gammaFree) :
    gammaErase (Charged.F k lam 1 P)=loweringResidual k lam P := by
  rw [F_one_gammaFree k lam P hP,map_add,map_add,map_neg,map_sum,map_smul,
    gammaErase_fixed _ (gammaFree_bD P hP 1)]
  unfold loweringResidual
  congr 2
  · congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_Icc.mp hp
    rw [map_mul,gammaErase_bV,gammaErase_GG_positive P hP (1-p) (by omega)]
  · have h := gammaErase_AG_one k P hP
    rw [AG_one k P] at h
    exact h

/-- For the actual screening state, F_1 ITSELF equals the gamma-free
finite residual. Positive Cartan annihilation proves that projection loses
no information about this output. The residual is not yet proved zero. -/
theorem state_lowering_eq_residual (r q M : ℕ) (hq : 0<q) (k lam : ℂ)
    (hMk : (M : ℂ)*(k+2)=1) :
    Charged.F k lam 1 (state r q M)=loweringResidual k lam (state r q M) := by
  rw [← gammaErase_state_lowering r q M hq k lam hMk]
  exact gammaErase_F_one k lam _ (fun j => state_gamma_derivative r q M j)

end
end VOA.Wak.Screening
