/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

/-!
# Finite power-sum witnesses for integer screening nonvanishing

Newton identities express every elementary symmetric polynomial using
positive power sums, with the correct weighted degree. In particular the
product of all auxiliary variables, raised to s, has a finite power-sum
expression of degree rs. This is the test polynomial needed in the finite
screening coefficient argument; no infinite generating series is assumed.
-/
namespace VOA.VirasoroScreening
open MvPolynomial
open scoped BigOperators

/-- Substitute the positive power sums for formal variables; variable i
has degree i+1, so no degree-zero power sum is used. -/
noncomputable def powerSumSubstitution (σ : Type*) [Fintype σ] :
    MvPolynomial ℕ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval (fun i => psum σ ℚ (i+1))

/-- Every elementary symmetric polynomial has a finite expression in
positive power sums whose formal weighted degree is exactly its index.
Newton's recurrence divides only by positive integers. -/
theorem exists_weighted_newton (σ : Type*) [Fintype σ] (k : ℕ) :
    ∃ P : MvPolynomial ℕ ℚ, P.IsWeightedHomogeneous (fun i => i+1) k ∧
      powerSumSubstitution σ P = esymm σ ℚ k := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k=0
    · subst k
      exact ⟨1,isWeightedHomogeneous_one _ _,by simp [powerSumSubstitution]⟩
    let P : ℕ → MvPolynomial ℕ ℚ := fun i =>
      if hi : i<k then (ih i hi).choose else 0
    have hP (i : ℕ) (hi : i<k) :
        (P i).IsWeightedHomogeneous (fun j => j+1) i ∧
          powerSumSubstitution σ (P i) = esymm σ ℚ i := by
      simpa only [P,dif_pos hi] using (ih i hi).choose_spec
    let S := (Finset.antidiagonal k).filter (fun a => a.1<k)
    let Q : MvPolynomial ℕ ℚ := ∑ a ∈ S,
      C ((-1:ℚ)^a.1) * (P a.1 * X (a.2-1))
    have hQ : Q.IsWeightedHomogeneous (fun i => i+1) k := by
      apply IsWeightedHomogeneous.sum
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      have hsum := Finset.mem_antidiagonal.mp ha'.1
      have hpos : 0<a.2 := by omega
      have hw := ((hP a.1 ha'.2).1.mul
        (isWeightedHomogeneous_X ℚ (fun i : ℕ => i+1) (a.2-1))).C_mul ((-1:ℚ)^a.1)
      convert hw using 1 <;> omega
    refine ⟨C ((k:ℚ)⁻¹ * (-1:ℚ)^(k+1)) * Q,
      hQ.C_mul _,?_⟩
    have he : powerSumSubstitution σ Q =
        ∑ a ∈ S, (-1 : MvPolynomial σ ℚ)^a.1 * esymm σ ℚ a.1 * psum σ ℚ a.2 := by
      simp only [Q,map_sum,map_mul]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      have hsum := Finset.mem_antidiagonal.mp ha'.1
      have hpos : 0<a.2 := by omega
      rw [(hP a.1 ha'.2).2]
      simp [powerSumSubstitution,show a.2-1+1=a.2 by omega,mul_assoc]
    rw [map_mul,he]
    have hn := mul_esymm_eq_sum σ ℚ k
    change (k : MvPolynomial σ ℚ) * esymm σ ℚ k =
      (-1)^(k+1) * ∑ a ∈ S, (-1)^a.1 * esymm σ ℚ a.1 * psum σ ℚ a.2 at hn
    have hc : powerSumSubstitution σ (C ((k:ℚ)⁻¹ * (-1:ℚ)^(k+1))) =
        C ((k:ℚ)⁻¹) * (-1)^(k+1) := by simp [powerSumSubstitution]
    rw [hc,mul_assoc,← hn,← mul_assoc]
    have hkq : (k:ℚ) ≠ 0 := by exact_mod_cast hk
    have hkk : C ((k:ℚ)⁻¹) * (k : MvPolynomial σ ℚ) = 1 := by
      rw [← map_natCast C k,← map_mul]
      simp [hkq]
    rw [hkk,one_mul]

/-- The product of all r auxiliary variables to power s admits a finite
power-sum expression of weighted degree rs. This is the specific witness
that detects the central Vandermonde coefficient. -/
theorem exists_weighted_product_witness (r s : ℕ) :
    ∃ P : MvPolynomial ℕ ℚ,
      P.IsWeightedHomogeneous (fun i => i+1) (r*s) ∧
      powerSumSubstitution (Fin r) P = (∏ i : Fin r, (X i : MvPolynomial (Fin r) ℚ))^s := by
  obtain ⟨P,hP,hE⟩ := exists_weighted_newton (Fin r) r
  refine ⟨P^s,?_,?_⟩
  · simpa [smul_eq_mul,Nat.mul_comm] using hP.pow s
  · rw [map_pow,hE]
    congr 1
    unfold esymm
    have hc : (Finset.univ : Finset (Fin r)).card = r := by simp
    have hs : (Finset.univ : Finset (Fin r)).powersetCard r = {Finset.univ} := by
      ext u
      simp only [Finset.mem_powersetCard,Finset.mem_singleton]
      constructor
      · rintro ⟨hu,he⟩
        exact Finset.eq_of_subset_of_card_le hu (by simpa [hc,he])
      · intro hu
        subst u
        simp
    rw [hs]
    simp

end VOA.VirasoroScreening
