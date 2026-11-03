/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningRaising

/-!
# Finite actual current formulas on gamma-independent polynomials

Normal-ordered operator sums are reduced to explicit finite oscillator
expressions with bounds supplied by the input polynomial. These are identities
for the actual charged Wakimoto action, not assumed screening Ward equations.
-/
namespace VOA.Wak.Screening
open MvPolynomial
open scoped BigOperators
noncomputable section

/-- On a gamma-independent polynomial every nonnegative beta mode vanishes. -/
theorem Bet_gammaFree (P : WakFock) (hP : P∈gammaFree) (n : ℤ) (hn : 0≤n) :
    Bet n P=0 := by
  rw [Bet_of_nonneg hn,cD_of_nonneg hn,dV_apply]
  exact hP n.toNat

/-- In the positive Cartan composite only negative beta modes contribute;
the corresponding positive gamma mode is minus a beta partial derivative. -/
theorem bgFam_gammaFree (P : WakFock) (hP : P∈gammaFree)
    (n p : ℤ) (hn : 0<n) : bgFam n p P =
      if p≤-1 then -(bV (-p) * bD (n-p) P) else 0 := by
  by_cases hp : p≤-1
  · rw [bgFam,if_pos hp,Module.End.mul_apply,Bet_of_neg hp,
      Gam_of_pos (by omega),LinearMap.neg_apply,mulL_apply,mul_neg,if_pos hp]
  · rw [bgFam,if_neg hp,Module.End.mul_apply,Bet_gammaFree P hP p (by omega),
      map_zero,if_neg hp]

/-- The actual positive Cartan composite is a finite beta-shift sum. The
bound NB P comes from the largest variable index present in the input. -/
theorem BG_gammaFree (P : WakFock) (hP : P∈gammaFree) (n : ℤ) (hn : 0<n) :
    BG n P = -∑ p ∈ Finset.Icc (1-NB P) (-1), bV (-p) * bD (n-p) P := by
  rw [BG,opSum_apply (bgFam_locFin n)]
  have hs : Function.support (fun p => bgFam n p P) ⊆
      (↑(Finset.Icc (1-NB P) (-1)) : Set ℤ) := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Finset.coe_Icc,Set.mem_Icc]
    by_contra hout
    have hz : bgFam n p P=0 := by
      by_cases hp' : p≤-1
      · rw [bgFam,if_pos hp',Module.End.mul_apply,
          Gam_apply_eq_zero (by omega),map_zero]
      · rw [bgFam_gammaFree P hP n p hn,if_neg hp']
    exact hp hz
  rw [finsum_eq_finsetSum_of_support_subset _ hs]
  simp only [bgFam_gammaFree P hP n _ hn]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [if_pos (Finset.mem_Icc.mp hp).2]

/-- Positive Cartan currents on gamma-independent inputs are the explicit
beta shift derivation plus the boson partial derivative, with coefficient
2(k+2)n. This is an actual mode identity, before any screening cancellation. -/
theorem H_positive_gammaFree (k lam : ℂ) (P : WakFock) (hP : P∈gammaFree)
    (n : ℤ) (hn : 0<n) : Charged.H k lam n P =
      (2 : ℂ) • (∑ p ∈ Finset.Icc (1-NB P) (-1), bV (-p) * bD (n-p) P) +
      ((2*(k+2))*(n : ℂ)) • aD n P := by
  rw [Charged.H,if_neg (by omega),add_zero,Hcur,
    LinearMap.add_apply,LinearMap.smul_apply,BG_gammaFree P hP n hn,
    Aos_of_nonneg k (by omega),LinearMap.smul_apply]
  module

/-- The gamma-gamma summand has three explicit regions when its total
index is positive: two creation/derivative tails and a finite double-partial
middle. The formula is valid on every oscillator polynomial. -/
theorem ggFam_positive (P : WakFock) (s u : ℤ) (hs : 0<s) :
    ggFam s u P =
      if u≤0 then -(cV (-u) * bD (s-u) P)
      else if u<s then bD (s-u) (bD u P)
      else -(cV (u-s) * bD u P) := by
  by_cases hu : u≤0
  · rw [ggFam,if_pos hu,Module.End.mul_apply,Gam_of_nonpos hu,
      Gam_of_pos (by omega),LinearMap.neg_apply,mulL_apply,mul_neg,if_pos hu]
  · rw [ggFam,if_neg hu,Module.End.mul_apply,if_neg hu]
    by_cases hu' : u<s
    · rw [if_pos hu',Gam_of_pos (by omega),Gam_of_pos (by omega)]
      simp only [LinearMap.neg_apply,map_neg,neg_neg]
    · rw [if_neg hu',Gam_of_nonpos (by omega),Gam_of_pos (by omega),
        LinearMap.neg_apply,mulL_apply,mul_neg]
      congr 2
      congr 1
      omega

/-- The actual gamma-gamma composite has a finite interval formula,
including all creation/derivative tails. No infinite summation remains. -/
theorem GG_positive (P : WakFock) (s : ℤ) (hs : 0<s) :
    GG s P = ∑ u ∈ Finset.Icc (min (s-NB P+1) 0) (NB P-1),
      if u≤0 then -(cV (-u) * bD (s-u) P)
      else if u<s then bD (s-u) (bD u P)
      else -(cV (u-s) * bD u P) := by
  rw [GG,opSum_apply (ggFam_locFin s)]
  have hb : Function.support (fun u => ggFam s u P) ⊆
      (↑(Finset.Icc (min (s-NB P+1) 0) (NB P-1)) : Set ℤ) := by
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [Finset.coe_Icc,Set.mem_Icc]
    by_contra hout
    have hz : ggFam s u P=0 := by
      by_cases hu' : u≤0
      · rw [ggFam,if_pos hu',Module.End.mul_apply,
          Gam_apply_eq_zero (P := P) (n := s-u) (by have := two_le_NB P; omega),map_zero]
      · rw [ggFam,if_neg hu',Module.End.mul_apply,
          Gam_apply_eq_zero (P := P) (n := u) (by omega),map_zero]
    exact hu hz
  rw [finsum_eq_finsetSum_of_support_subset _ hb]
  apply Finset.sum_congr rfl
  intro u hu
  exact ggFam_positive P s u hs

/-- On gamma-independent inputs the triple ghost composite contains only
negative beta creation modes; the other half annihilates the input. -/
theorem BGG_gammaFree (P : WakFock) (hP : P∈gammaFree) :
    BGG 1 P = ∑ p ∈ Finset.Icc (2-2*NB P) (-1), bV (-p) * GG (1-p) P := by
  rw [BGG,opSum_apply (bggFam_locFin 1)]
  have hb : Function.support (fun p => bggFam 1 p P) ⊆
      (↑(Finset.Icc (2-2*NB P) (-1)) : Set ℤ) := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Finset.coe_Icc,Set.mem_Icc]
    by_contra hout
    have hz : bggFam 1 p P=0 := by
      by_cases hp' : p≤-1
      · rw [bggFam,if_pos hp',Module.End.mul_apply,
          GG_apply_eq_zero (by omega),map_zero]
      · rw [bggFam,if_neg hp',Module.End.mul_apply,
          Bet_gammaFree P hP p (by omega),map_zero]
    exact hp hz
  rw [finsum_eq_finsetSum_of_support_subset _ hb]
  apply Finset.sum_congr rfl
  intro p hp
  rw [bggFam,if_pos (Finset.mem_Icc.mp hp).2,Module.End.mul_apply,
    Bet_of_neg (Finset.mem_Icc.mp hp).2,mulL_apply]

/-- Each boson-gamma summand at index one is a creation times beta
partial for negative p, or a gamma creation times boson partial otherwise.
The p=0 term vanishes automatically through aD 0. -/
theorem agFam_one (k : ℂ) (P : WakFock) (p : ℤ) : agFam k 1 p P =
    if p≤-1 then -(aV (-p) * bD (1-p) P)
    else ((2*(k+2))*(p : ℂ)) • (cV (p-1) * aD p P) := by
  by_cases hp : p≤-1
  · rw [agFam,if_pos hp,Module.End.mul_apply,Aos_of_neg k hp,
      Gam_of_pos (by omega),LinearMap.neg_apply,mulL_apply,mul_neg,if_pos hp]
  · rw [agFam,if_neg hp,Module.End.mul_apply,Aos_of_nonneg k (by omega),
      LinearMap.smul_apply,map_smul,if_neg hp]
    by_cases hp0 : p=0
    · subst p; simp
    · rw [Gam_of_nonpos (by omega),mulL_apply]
      congr 2
      congr 1
      omega

/-- The actual boson-gamma composite at index one has a finite partial-
derivative formula on every polynomial. -/
theorem AG_one (k : ℂ) (P : WakFock) : AG k 1 P =
    ∑ p ∈ Finset.Icc (min (2-NB P) 0) (NB P-1),
      if p≤-1 then -(aV (-p) * bD (1-p) P)
      else ((2*(k+2))*(p : ℂ)) • (cV (p-1) * aD p P) := by
  rw [AG,opSum_apply (agFam_locFin k 1)]
  have hb : Function.support (fun p => agFam k 1 p P) ⊆
      (↑(Finset.Icc (min (2-NB P) 0) (NB P-1)) : Set ℤ) := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Finset.coe_Icc,Set.mem_Icc]
    by_contra hout
    have hz : agFam k 1 p P=0 := by
      by_cases hp' : p≤-1
      · rw [agFam,if_pos hp',Module.End.mul_apply,
          Gam_apply_eq_zero (by have := two_le_NB P; omega),map_zero]
      · rw [agFam,if_neg hp',Module.End.mul_apply,
          Aos_apply_eq_zero k (by omega),map_zero]
    exact hp hz
  rw [finsum_eq_finsetSum_of_support_subset _ hb]
  apply Finset.sum_congr rfl
  intro p hp
  exact agFam_one k P p

/-- The actual charged lowering mode at index one is reduced to finite
beta, gamma and boson partial sums. Expanding GG with GG_positive gives
only first and second partial derivatives. Cancellation on the screening
coefficient is a separate remaining step. -/
theorem F_one_gammaFree (k lam : ℂ) (P : WakFock) (hP : P∈gammaFree) :
    Charged.F k lam 1 P =
      -(∑ p ∈ Finset.Icc (2-2*NB P) (-1), bV (-p) * GG (1-p) P) +
      (∑ p ∈ Finset.Icc (min (2-NB P) 0) (NB P-1),
        if p≤-1 then -(aV (-p) * bD (1-p) P)
        else ((2*(k+2))*(p : ℂ)) • (cV (p-1) * aD p P)) +
      (k-lam) • bD 1 P := by
  rw [Charged.F,Fcur]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,
    LinearMap.smul_apply,BGG_gammaFree P hP,AG_one,Gam_of_pos (show (1 : ℤ)≥1 by omega)]
  simp only [LinearMap.neg_apply,Int.cast_one,mul_one]
  module

end
end VOA.Wak.Screening
