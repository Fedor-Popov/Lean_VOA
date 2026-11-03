/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic

/-!
# Partial degrees, partial Euler operators and the Weyl relations on `ℂ[x]`

For a finite set `s` of variables, `sdeg s μ = Σ_{q ∈ s} μ q` is the partial degree of a
monomial, `sProj s d` the projection onto partial degree `d`, and `sEuler s = Σ_{q ∈ s} x_q ∂_q`
the partial Euler operator. Proved:

* `sEuler_monomial`: `sEuler s x^μ = sdeg s μ · x^μ`; `sProj_sEuler`.
* `sProj_pderiv`: `∂_q` (`q ∈ s`) lowers the partial degree by one.
* `sum_sProj`: every polynomial is the sum of its partial-degree components below a bound.
* the Weyl relations `pderiv_X_mul'`, `pderiv_pderiv_comm`.

Everything is proved outright.
-/

namespace VOA.KoszulResidual

open MvPolynomial

noncomputable section

variable {σ : Type*} [DecidableEq σ]

/-- Two linear maps out of `ℂ[x]` agreeing on the monomials `x^μ` agree. -/
theorem poly_linearMap_ext {M : Type*} [AddCommGroup M] [Module ℂ M]
    {f g : MvPolynomial σ ℂ →ₗ[ℂ] M} (h : ∀ μ : σ →₀ ℕ, f (monomial μ 1) = g (monomial μ 1)) :
    f = g :=
  (basisMonomials σ ℂ).ext fun μ => by rw [coe_basisMonomials]; exact h μ

/-- The partial degree of an exponent along `s`. -/
def sdeg (s : Finset σ) (μ : σ →₀ ℕ) : ℕ := ∑ q ∈ s, μ q

theorem sdeg_add (s : Finset σ) (μ ν : σ →₀ ℕ) : sdeg s (μ + ν) = sdeg s μ + sdeg s ν := by
  simp [sdeg, Finset.sum_add_distrib]

theorem sdeg_single (s : Finset σ) (q : σ) (n : ℕ) :
    sdeg s (Finsupp.single q n) = if q ∈ s then n else 0 := by
  unfold sdeg
  split_ifs with hq
  · rw [Finset.sum_eq_single q (fun b _ hb => by simp [Finsupp.single_apply, Ne.symm hb])
      (fun h => absurd hq h)]
    simp
  · exact Finset.sum_eq_zero fun b hb => by
      rw [Finsupp.single_apply, if_neg (fun e => hq (by rw [e]; exact hb))]

/-- The projection onto partial degree `d` along `s`. -/
def sProj (s : Finset σ) (d : ℕ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  (basisMonomials σ ℂ).constr ℂ fun μ => if sdeg s μ = d then monomial μ 1 else 0

theorem sProj_monomial (s : Finset σ) (d : ℕ) (μ : σ →₀ ℕ) (a : ℂ) :
    sProj s d (monomial μ a) = if sdeg s μ = d then monomial μ a else 0 := by
  have h := (basisMonomials σ ℂ).constr_basis ℂ
    (fun μ => if sdeg s μ = d then (monomial μ 1 : MvPolynomial σ ℂ) else 0) μ
  rw [coe_basisMonomials] at h
  rw [show monomial μ a = a • monomial μ 1 by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, sProj, h]
  split_ifs <;> simp [smul_monomial]

theorem coeff_sProj (s : Finset σ) (d : ℕ) (p : MvPolynomial σ ℂ) (μ : σ →₀ ℕ) :
    coeff μ (sProj s d p) = if sdeg s μ = d then coeff μ p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial ν a =>
      rw [sProj_monomial]
      split_ifs with h1 h2 h2
      · rfl
      · rw [coeff_monomial, if_neg]; rintro rfl; exact h2 h1
      · rw [coeff_zero, coeff_monomial, if_neg]; rintro rfl; exact h1 h2
      · rw [coeff_zero]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq]; split_ifs <;> simp

/-- The partial Euler operator `Σ_{q ∈ s} x_q ∂_q`. -/
def sEuler (s : Finset σ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  ∑ q ∈ s, LinearMap.mulLeft ℂ (X q) ∘ₗ (pderiv q).toLinearMap

theorem X_mul_pderiv_monomial' (q : σ) (μ : σ →₀ ℕ) (a : ℂ) :
    X q * pderiv q (monomial μ a) = ((μ q : ℕ) : ℂ) • monomial μ a := by
  rw [X_mul_pderiv_monomial]
  simp [smul_monomial, nsmul_eq_mul]

theorem sEuler_monomial (s : Finset σ) (μ : σ →₀ ℕ) (a : ℂ) :
    sEuler s (monomial μ a) = ((sdeg s μ : ℕ) : ℂ) • monomial μ a := by
  simp only [sEuler, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, Derivation.coeFn_coe, LinearMap.mulLeft_apply,
    X_mul_pderiv_monomial', sdeg, Nat.cast_sum, Finset.sum_smul]

theorem sProj_sEuler (s : Finset σ) (d : ℕ) (p : MvPolynomial σ ℂ) :
    sProj s d (sEuler s p) = (d : ℂ) • sProj s d p := by
  have : (sProj s d ∘ₗ sEuler s) = (d : ℂ) • sProj s d := by
    refine poly_linearMap_ext fun μ => ?_
    rw [LinearMap.comp_apply, sEuler_monomial, map_smul, sProj_monomial, LinearMap.smul_apply,
      sProj_monomial]
    split_ifs with h
    · rw [h]
    · simp
  exact LinearMap.congr_fun this p

theorem sEuler_sProj (s : Finset σ) (d : ℕ) (p : MvPolynomial σ ℂ) :
    sEuler s (sProj s d p) = (d : ℂ) • sProj s d p := by
  have : (sEuler s ∘ₗ sProj s d) = (d : ℂ) • sProj s d := by
    refine poly_linearMap_ext fun μ => ?_
    rw [LinearMap.comp_apply, sProj_monomial, LinearMap.smul_apply, sProj_monomial]
    split_ifs with h
    · rw [sEuler_monomial, h]
    · simp
  exact LinearMap.congr_fun this p

theorem pderiv_monomial' (q : σ) (μ : σ →₀ ℕ) (a : ℂ) :
    pderiv q (monomial μ a) = monomial (μ - Finsupp.single q 1) (a * (μ q : ℂ)) :=
  pderiv_monomial

/-- `∂_q` (`q ∈ s`) lowers the partial degree by one. -/
theorem sProj_pderiv (s : Finset σ) {q : σ} (hq : q ∈ s) (d : ℕ) (p : MvPolynomial σ ℂ) :
    sProj s d (pderiv q p) = pderiv q (sProj s (d + 1) p) := by
  have : (sProj s d ∘ₗ (pderiv q).toLinearMap) =
      (pderiv q).toLinearMap ∘ₗ sProj s (d + 1) := by
    refine poly_linearMap_ext fun μ => ?_
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe]
    rw [pderiv_monomial', sProj_monomial, sProj_monomial]
    by_cases hμ : μ q = 0
    · rw [hμ, Nat.cast_zero, mul_zero, monomial_zero]
      split_ifs
      · rw [pderiv_monomial', hμ, Nat.cast_zero, mul_zero, monomial_zero]
      · rw [map_zero]
      · rw [pderiv_monomial', hμ, Nat.cast_zero, mul_zero, monomial_zero]
      · rw [map_zero]
    · have hdeg : sdeg s (μ - Finsupp.single q 1) + 1 = sdeg s μ := by
        have hsplit : μ = (μ - Finsupp.single q 1) + Finsupp.single q 1 := by
          ext r
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs with h
          · subst h; omega
          · omega
        conv_rhs => rw [hsplit]
        rw [sdeg_add, sdeg_single, if_pos hq]
      split_ifs with h1 h2 h2
      · rw [pderiv_monomial']
      · omega
      · omega
      · rfl
  exact LinearMap.congr_fun this p

/-- Every polynomial is the sum of its partial-degree components below a bound. -/
theorem exists_sProj_eq_zero (s : Finset σ) (p : MvPolynomial σ ℂ) :
    ∃ D : ℕ, ∀ d, D < d → sProj s d p = 0 := by
  classical
  refine ⟨p.support.sup (sdeg s), fun d hd => ?_⟩
  ext μ
  rw [coeff_sProj, coeff_zero]
  split_ifs with h
  · by_contra hne
    have hmem : μ ∈ p.support := mem_support_iff.mpr hne
    have := Finset.le_sup (f := sdeg s) hmem
    omega
  · rfl

theorem eq_zero_of_sProj (s : Finset σ) {p : MvPolynomial σ ℂ} (h : ∀ d, sProj s d p = 0) :
    p = 0 := by
  ext μ
  have := congrArg (coeff μ) (h (sdeg s μ))
  rwa [coeff_sProj, if_pos rfl, coeff_zero] at this

/-! ### Weyl relations -/

theorem pderiv_X_mul' (q q' : σ) (p : MvPolynomial σ ℂ) :
    pderiv q (X q' * p) = X q' * pderiv q p + if q = q' then p else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  split_ifs with h h' h'
  · subst h; ring
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · simp [add_comm]

theorem pderiv_pderiv_comm (q q' : σ) (p : MvPolynomial σ ℂ) :
    pderiv q (pderiv q' p) = pderiv q' (pderiv q p) := by
  have : ((pderiv q : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap ∘ₗ
      (pderiv q' : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap) =
      ((pderiv q' : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap ∘ₗ
      (pderiv q : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap) := by
    refine poly_linearMap_ext fun μ => ?_
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, pderiv_monomial']
    by_cases hqq : q = q'
    · subst hqq; rfl
    · have e : μ - Finsupp.single q' 1 - Finsupp.single q 1 =
          μ - Finsupp.single q 1 - Finsupp.single q' 1 := by
        ext r
        simp only [Finsupp.coe_tsub, Pi.sub_apply]
        omega
      rw [e]
      congr 1
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hqq,
        if_neg (Ne.symm hqq), tsub_zero]
      ring
  exact LinearMap.congr_fun this p

end

end VOA.KoszulResidual
