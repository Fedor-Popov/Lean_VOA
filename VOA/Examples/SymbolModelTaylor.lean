/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Analysis.Complex.Basic

/-!
# Infinitesimally transitive families detect polynomials (Taylor argument)

Let `P = C[x_s]` (any set of variables) and let `L_i` be linear operators on `P` of the form
`c • ∂_{x} + E`, where `E` preserves homogeneous degree (e.g. a derivation sending variables to
linear forms). If for every variable `x` some `L_i` has this form with `c ≠ 0`, then:

`eq_bot_of_stable` — every subspace `S ⊆ ker(constantCoeff)` stable under all `L_i` is zero.

This is the algebraic core of the cyclicity of evaluation at a point at which a family of
vector fields spans the tangent space (used in `SymbolModelJet` for the loop-group orbit argument). The proof is an induction on the lowest
homogeneous component: `L_i` lowers it by one through `c ∂_x` and the `E` part does not interfere;
a homogeneous polynomial of positive degree with all partial derivatives zero vanishes.

Everything is proved outright.
-/

namespace VOA.SymbolModel

open MvPolynomial

noncomputable section

variable {σ : Type*}

/-! ### Coefficients of partial derivatives -/

theorem coeff_pderiv_eq (i : σ) (P : MvPolynomial σ ℂ) (t : σ →₀ ℕ) :
    coeff t (pderiv i P) = coeff (t + Finsupp.single i 1) P * ((t i : ℂ) + 1) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hs : s = t + Finsupp.single i 1
    · subst hs
      rw [if_pos (by simp), if_pos rfl]
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.cast_add,
        Nat.cast_one]
    · rw [if_neg hs, zero_mul]
      split_ifs with h
      · have hsi : s i = 0 := by
          by_contra hne
          apply hs
          ext j
          have := congrArg (fun f => f j) h
          simp only [Finsupp.coe_tsub, Pi.sub_apply] at this
          by_cases hj : j = i
          · subst hj; simp at this ⊢; omega
          · simp [Ne.symm hj] at this ⊢; omega
        rw [hsi, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, add_mul]

theorem eq_C_of_pderiv_eq_zero (P : MvPolynomial σ ℂ) (h : ∀ i, pderiv i P = 0) :
    P = C (coeff 0 P) := by
  classical
  ext t
  rw [coeff_C]
  split_ifs with ht
  · rw [ht]
  · obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact ht (Finsupp.ext fun j => by simp [hne j])
    have e : t - Finsupp.single i 1 + Finsupp.single i 1 = t := by
      ext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hj]
    have hc := coeff_pderiv_eq i P (t - Finsupp.single i 1)
    rw [h i, coeff_zero, e] at hc
    have hne : (((t - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero ((t - Finsupp.single i (1 : ℕ) : σ →₀ ℕ) i)
    exact (mul_eq_zero.mp hc.symm).resolve_right hne

theorem eq_zero_of_isHomogeneous_of_pderiv {P : MvPolynomial σ ℂ} {k : ℕ}
    (hP : P.IsHomogeneous (k + 1)) (h : ∀ i, pderiv i P = 0) : P = 0 := by
  have hC := eq_C_of_pderiv_eq_zero P h
  have h0 : coeff 0 P = 0 := by
    by_contra hne
    have := hP hne
    simp at this
  rw [hC, h0, C_0]

/-! ### Homogeneous components through `∂` and through degree-preserving maps -/

theorem homogeneousComponent_pderiv (i : σ) (P : MvPolynomial σ ℂ) (d : ℕ) :
    homogeneousComponent d (pderiv i P) = pderiv i (homogeneousComponent (d + 1) P) := by
  conv_lhs => rw [← sum_homogeneousComponent P, map_sum, map_sum]
  rw [Finset.sum_eq_single (d + 1)]
  · have h := (homogeneousComponent_isHomogeneous (d + 1) P).pderiv (i := i)
    rw [Nat.add_sub_cancel] at h
    exact (homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr h)).trans (if_pos rfl)
  · intro e _ he
    rcases e with _ | e
    · rw [homogeneousComponent_zero, pderiv_C, map_zero]
    · have h := (homogeneousComponent_isHomogeneous (e + 1) P).pderiv (i := i)
      rw [Nat.add_sub_cancel] at h
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr h), if_neg (by omega)]
  · intro hd
    rw [Finset.mem_range, not_lt] at hd
    rw [homogeneousComponent_eq_zero (d + 1) P (by omega), map_zero, map_zero]

/-- A linear map preserving homogeneity commutes with the homogeneous components. -/
theorem homogeneousComponent_comm (E : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (hE : ∀ d (Q : MvPolynomial σ ℂ), Q.IsHomogeneous d → (E Q).IsHomogeneous d)
    (P : MvPolynomial σ ℂ) (d : ℕ) :
    homogeneousComponent d (E P) = E (homogeneousComponent d P) := by
  conv_lhs => rw [← sum_homogeneousComponent P, map_sum, map_sum]
  rw [Finset.sum_eq_single d]
  · exact (homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      (hE d _ (homogeneousComponent_isHomogeneous d P)))).trans (if_pos rfl)
  · intro e _ he
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      (hE e _ (homogeneousComponent_isHomogeneous e P))), if_neg (Ne.symm he)]
  · intro hd
    rw [Finset.mem_range, not_lt] at hd
    rw [homogeneousComponent_eq_zero d P (by omega), map_zero, map_zero]

/-! ### The Taylor argument -/

/-- An operator of the form `c • ∂_x + E` with `E` degree-preserving. -/
structure TaylorForm (L : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (x : σ) where
  c : ℂ
  c_ne : c ≠ 0
  E : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ
  E_hom : ∀ d (Q : MvPolynomial σ ℂ), Q.IsHomogeneous d → (E Q).IsHomogeneous d
  eq : L = c • (pderiv (R := ℂ) x).toLinearMap + E

/-- **The Taylor argument.** A subspace inside `ker constantCoeff`, stable under a family of
operators that contains, for every variable `x`, one of the form `c • ∂_x + E`, is zero. -/
theorem eq_bot_of_stable {ι : Type*} (L : ι → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (hL : ∀ x : σ, ∃ i, Nonempty (TaylorForm (L i) x)) (S : Submodule ℂ (MvPolynomial σ ℂ))
    (hS : ∀ i, ∀ Q ∈ S, L i Q ∈ S) (h0 : ∀ Q ∈ S, constantCoeff Q = 0) : S = ⊥ := by
  -- lowest components vanish, by induction on the degree
  have key : ∀ k : ℕ, ∀ Q ∈ S, (∀ d < k, homogeneousComponent d Q = 0) →
      homogeneousComponent k Q = 0 := by
    intro k
    induction k with
    | zero =>
      intro Q hQ _
      rw [homogeneousComponent_zero, ← constantCoeff_eq, h0 Q hQ, C_0]
    | succ k ih =>
      intro Q hQ hlow
      apply eq_zero_of_isHomogeneous_of_pderiv (homogeneousComponent_isHomogeneous _ Q)
      intro x
      obtain ⟨i, ⟨T⟩⟩ := hL x
      have hLQ := hS i Q hQ
      have hcomp : ∀ d, homogeneousComponent d (L i Q) =
          T.c • pderiv x (homogeneousComponent (d + 1) Q) + T.E (homogeneousComponent d Q) := by
        intro d
        rw [LinearMap.congr_fun T.eq Q, LinearMap.add_apply, LinearMap.smul_apply, map_add,
          map_smul, Derivation.coeFn_coe, homogeneousComponent_pderiv,
          homogeneousComponent_comm T.E T.E_hom]
      have hlow' : ∀ d < k, homogeneousComponent d (L i Q) = 0 := by
        intro d hd
        rw [hcomp, hlow (d + 1) (by omega), hlow d (by omega), map_zero, smul_zero, map_zero,
          add_zero]
      have := ih (L i Q) hLQ hlow'
      rw [hcomp, hlow k (by omega), map_zero, add_zero] at this
      exact (smul_eq_zero.mp this).resolve_left T.c_ne
  rw [eq_bot_iff]
  intro Q hQ
  rw [Submodule.mem_bot, ← sum_homogeneousComponent Q]
  refine Finset.sum_eq_zero fun k _ => ?_
  induction k using Nat.strong_induction_on with
  | _ k ihk => exact key k Q hQ fun d hd => ihk d hd (Finset.mem_range.mpr (by
      have := Finset.mem_range.mp ‹k ∈ Finset.range (Q.totalDegree + 1)›; omega))

/-! ### Derivations sending variables to linear forms preserve homogeneity -/

theorem derivation_monomial_isHomogeneous
    (E : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hE : ∀ y, (E (X y)).IsHomogeneous 1) (s : σ →₀ ℕ) :
    (E (monomial s (1 : ℂ))).IsHomogeneous (Finsupp.weight 1 s) := by
  classical
  induction s using Finsupp.induction with
  | zero => simp only [monomial_zero', map_one, Derivation.map_one_eq_zero]; exact
      isHomogeneous_zero _ _ _
  | single_add a b f _ _ ih =>
    rw [← mul_one (1 : ℂ), ← monomial_mul, Derivation.leibniz, map_add]
    have h1 : (monomial (Finsupp.single a b) (1 : ℂ)).IsHomogeneous b :=
      isHomogeneous_monomial _ (by simp)
    have h2 : (monomial f (1 : ℂ)).IsHomogeneous (Finsupp.weight 1 f) :=
      isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_weight_one]; rfl)
    have h3 : (E (monomial (Finsupp.single a b) (1 : ℂ))).IsHomogeneous b := by
      rw [← X_pow_eq_monomial, Derivation.leibniz_pow]
      rcases b with _ | k
      · simp only [zero_smul]; exact isHomogeneous_zero _ _ _
      · rw [← mem_homogeneousSubmodule]
        refine nsmul_mem ?_ _
        rw [mem_homogeneousSubmodule, smul_eq_mul, Nat.add_sub_cancel]
        exact (isHomogeneous_X_pow a k).mul (hE a)
    have hw : Finsupp.weight 1 (Finsupp.single a b) = b := by
      simp [Finsupp.weight_apply]
    rw [hw, smul_eq_mul, smul_eq_mul]
    exact (h1.mul ih).add (by rw [mul_comm]; exact h3.mul h2)

theorem derivation_isHomogeneous (E : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hE : ∀ y, (E (X y)).IsHomogeneous 1) (d : ℕ) (Q : MvPolynomial σ ℂ)
    (hQ : Q.IsHomogeneous d) : (E Q).IsHomogeneous d := by
  classical
  rw [Q.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun s hs => ?_
  have hsd : Finsupp.weight 1 s = d := hQ (mem_support_iff.mp hs)
  rw [show monomial s (coeff s Q) = coeff s Q • monomial s (1 : ℂ) by
    rw [smul_monomial, smul_eq_mul, mul_one], E.map_smul, ← mem_homogeneousSubmodule]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_homogeneousSubmodule, ← hsd]
  exact derivation_monomial_isHomogeneous E hE s

end

end VOA.SymbolModel
