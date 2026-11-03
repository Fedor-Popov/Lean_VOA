/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonArbitraryPair
import VOA.Commutative.GordonCommonFactors
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The common Gordon cluster divisor -/

namespace VOA.GordonDivisor

open scoped BigOperators
open VOA.GordonFiltration VOA.GordonArbitraryPair VOA.GordonCommonFactors

noncomputable section

/-- Pairwise separated prime powers with varying exponents multiply inside a common divisor. -/
theorem prod_pow_dvd_of_pairwise_prime_varying
    {A M : Type*} [DecidableEq A] [CommMonoidWithZero M] [IsCancelMulZero M]
    (s : Finset A) (f : A → M) (e : A → ℕ) (p : M)
    (hprime : ∀ a ∈ s, Prime (f a))
    (hseparate : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ f a ∣ f b)
    (heach : ∀ a ∈ s, f a ^ e a ∣ p) :
    (∏ a ∈ s, f a ^ e a) ∣ p := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert a s ha ih =>
      have hadiv : f a ^ e a ∣ p := heach a (Finset.mem_insert_self a s)
      rcases hadiv with ⟨q, hpq⟩
      have htail : ∀ b ∈ s, f b ^ e b ∣ q := by
        intro b hb
        have hbprime : Prime (f b) := hprime b (Finset.mem_insert_of_mem hb)
        have hbnot : ¬ f b ∣ f a ^ e a := by
          intro hbaPow
          have hba : f b ∣ f a := hbprime.dvd_of_dvd_pow hbaPow
          have hba_ne : b ≠ a := fun h => ha (h ▸ hb)
          exact hseparate b (Finset.mem_insert_of_mem hb) a
            (Finset.mem_insert_self a s) hba_ne hba
        exact hbprime.pow_dvd_of_dvd_mul_left (e b) hbnot (by
          rw [← hpq]
          exact heach b (Finset.mem_insert_of_mem hb))
      have htailProduct : (∏ b ∈ s, f b ^ e b) ∣ q :=
        ih q (fun b hb => hprime b (Finset.mem_insert_of_mem hb))
          (fun b hb c hc hbc => hseparate b (Finset.mem_insert_of_mem hb)
            c (Finset.mem_insert_of_mem hc) hbc)
          htail
      rw [Finset.prod_insert ha, hpq]
      exact mul_dvd_mul_left (f a ^ e a) htailProduct


variable {σ τ K : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [LinearOrder τ]
variable [Field K]

/-- Every unordered block pair contributes its full Gordon multiplicity exactly once. -/
def clusterDivisor (f : σ → τ) : MvPolynomial τ K :=
  ∏ ij : IncreasingPair τ, collisionFactor ij.val.1 ij.val.2 ^
    (2 * min (blockSize f ij.val.1) (blockSize f ij.val.2))

/-- The polynomial degree of the cluster divisor, before regrouping equal-size blocks. -/
def clusterDegree (f : σ → τ) : ℕ :=
  ∑ ij : IncreasingPair τ, 2 * min (blockSize f ij.val.1) (blockSize f ij.val.2)

theorem clusterDivisor_ne_zero (f : σ → τ) : clusterDivisor (K := K) f ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  exact pow_ne_zero _ (collisionFactor_prime ij.val.1 ij.val.2 (ne_of_gt ij.property)).ne_zero

theorem clusterDivisor_isHomogeneous (f : σ → τ) :
    (clusterDivisor (K := K) f).IsHomogeneous (clusterDegree f) := by
  apply MvPolynomial.IsHomogeneous.prod
  intro ij _
  simpa only [one_mul] using
    ((MvPolynomial.isHomogeneous_X K ij.val.1).sub
      (MvPolynomial.isHomogeneous_X K ij.val.2)).pow
        (2 * min (blockSize f ij.val.1) (blockSize f ij.val.2))

theorem totalDegree_clusterDivisor (f : σ → τ) :
    (clusterDivisor (K := K) f).totalDegree = clusterDegree f :=
  (clusterDivisor_isHomogeneous f).totalDegree (clusterDivisor_ne_zero f)

/-- All pairwise multiplicities combine to the entire cluster divisor, without
an unjustified comaximality assumption on collision ideals. -/
theorem clusterDivisor_dvd [CharZero K] (f : σ → τ)
    (U : Submodule K (MvPolynomial σ K)) (F : MvPolynomial σ K) (hF : F.IsSymmetric)
    (hmem : F ∈ filtration (τ := τ) U (shape f)) :
    clusterDivisor f ∣ blockEval f F := by
  apply prod_pow_dvd_of_pairwise_prime_varying
  · intro ij _
    exact collisionFactor_prime ij.val.1 ij.val.2 (ne_of_gt ij.property)
  · intro ij _ kl _ hne
    exact collisionFactor_not_dvd_of_pairs_ne ij.property kl.property
      (fun he ↦ hne (Subtype.ext he))
  · intro ij _
    exact difference_pow_two_min_dvd f ij.val.1 ij.val.2 (ne_of_lt ij.property) U F hF hmem

end
end VOA.GordonDivisor
