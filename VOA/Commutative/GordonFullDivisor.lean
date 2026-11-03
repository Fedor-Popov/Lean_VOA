/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonPairedRelations
import VOA.Commutative.GordonDegree

/-! # The full Section 4 Gordon divisor from actual relation and evaluation kernels -/

namespace VOA.GordonFullDivisor

open scoped BigOperators
open MvPolynomial VOA.GordonFiltration VOA.GordonCommonFactors VOA.GordonDivisor
open VOA.GordonPairedEvaluation VOA.GordonPairedRelations VOA.GordonRestrictedDual
open VOA.GordonResidualFiltration

noncomputable section

variable {K ρ τ α β γ : Type*} [Field K]
variable [Fintype ρ] [Fintype τ] [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq ρ] [LinearOrder τ] [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- The three disjoint families of collision factors in the full Gordon divisor. -/
abbrev Edge (m : ℕ) (f : ρ → τ) := IncreasingPair τ ⊕
  (({u : τ // blockSize f u = m} × Residual α β γ) ⊕ (α × β))

/-- Orient every collision pair by the order cluster < e < f < h. -/
def edgePair (m : ℕ) (f : ρ → τ) : Edge (α := α) (β := β) (γ := γ) m f →
    Target τ α β γ × Target τ α β γ
  | .inl ij => (Sum.inl ij.val.1, Sum.inl ij.val.2)
  | .inr (.inl ud) => (Sum.inl ud.1.val, Sum.inr ud.2)
  | .inr (.inr xy) => (eLabel xy.1, fLabel xy.2)

theorem edgePair_injective (m : ℕ) (f : ρ → τ) :
    Function.Injective (edgePair (α := α) (β := β) (γ := γ) m f) := by
  rintro (a | (a | a)) (b | (b | b)) h <;>
    simp_all [edgePair, eLabel, fLabel, Subtype.ext_iff, Prod.mk.injEq]
  · exact Prod.ext h.1 h.2
  · exact Prod.ext (Subtype.ext h.1) h.2
  · exact Prod.ext h.1 h.2

theorem edgePair_ne (m : ℕ) (f : ρ → τ)
    (e : Edge (α := α) (β := β) (γ := γ) m f) :
    (edgePair m f e).1 ≠ (edgePair m f e).2 := by
  rcases e with ij | (ud | xy)
  · simpa [edgePair] using ij.property.ne
  · simp [edgePair]
  · simp [edgePair, eLabel, fLabel]

theorem edgePair_not_reverse (m : ℕ) (f : ρ → τ)
    (a b : Edge (α := α) (β := β) (γ := γ) m f) :
    ¬ ((edgePair m f b).1 = (edgePair m f a).2 ∧
      (edgePair m f b).2 = (edgePair m f a).1) := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp only [edgePair, eLabel, fLabel, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false, not_false_eq_true]
  rintro ⟨h₁, h₂⟩
  have hb := b.property
  rw [h₁, h₂] at hb
  exact a.property.asymm hb

def edgeExponent (m : ℕ) (f : ρ → τ) : Edge (α := α) (β := β) (γ := γ) m f → ℕ
  | .inl ij => 2 * min (blockSize f ij.val.1) (blockSize f ij.val.2)
  | .inr _ => 1

/-- The full product: cluster powers, maximal-block/residual factors, and residual e-f factors. -/
def fullDivisor (m : ℕ) (f : ρ → τ) : MvPolynomial (Target τ α β γ) K :=
  ∏ e : Edge (α := α) (β := β) (γ := γ) m f,
    collisionFactor (edgePair m f e).1 (edgePair m f e).2 ^ edgeExponent m f e

def fullDegree (m : ℕ) (f : ρ → τ) : ℕ :=
  ∑ e : Edge (α := α) (β := β) (γ := γ) m f, edgeExponent m f e

/-- The degree of the full divisor is exactly the exponent in Proposition 4.6. -/
theorem fullDegree_eq (m : ℕ) (f : ρ → τ) :
    fullDegree (α := α) (β := β) (γ := γ) m f = clusterDegree f +
      Fintype.card {u : τ // blockSize f u = m} *
        (Fintype.card α + Fintype.card β + Fintype.card γ) +
      Fintype.card α * Fintype.card β := by
  simp [fullDegree, edgeExponent, Fintype.sum_sum_type, clusterDegree,
    Fintype.card_prod, Fintype.card_sum, Nat.add_assoc]

theorem fullDivisor_ne_zero (m : ℕ) (f : ρ → τ) :
    fullDivisor (K := K) (α := α) (β := β) (γ := γ) m f ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  apply pow_ne_zero
  exact (collisionFactor_prime _ _ (edgePair_ne m f e).symm).ne_zero

theorem fullDivisor_isHomogeneous (m : ℕ) (f : ρ → τ) :
    (fullDivisor (K := K) (α := α) (β := β) (γ := γ) m f).IsHomogeneous
      (fullDegree (α := α) (β := β) (γ := γ) m f) := by
  apply IsHomogeneous.prod
  intro e _
  have h : (collisionFactor (K := K) (edgePair m f e).1
      (edgePair m f e).2).IsHomogeneous 1 :=
    (isHomogeneous_X K (edgePair m f e).1).sub
      (isHomogeneous_X K (edgePair m f e).2)
  simpa using h.pow (edgeExponent m f e)

/-- The full divisor follows from the genuine auxiliary functional model, next-pair
kernels, and the genuine lexicographic Gordon kernels. -/
theorem fullDivisor_dvd [CharZero K] (m D : ℕ) (f : ρ → τ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (hnext : ∀ x : α, ∀ y : β, nextPairEval x y F = 0)
    (U : Submodule K (MvPolynomial (Target ρ α β γ) K))
    (hG : pairEval F ∈ residualFiltration (τ := τ) U (shape f)) :
    fullDivisor (K := K) (α := α) (β := β) (γ := γ) m f ∣ clusterEval f F := by
  classical
  apply prod_pow_dvd_of_pairwise_prime_varying
  · intro e _
    exact collisionFactor_prime _ _ (edgePair_ne m f e).symm
  · intro e _ d _ hed
    apply collisionFactor_not_dvd_of_unordered_pairs_ne
      (edgePair_ne m f e).symm (edgePair_ne m f d)
    · intro hp
      exact hed (edgePair_injective m f (Prod.ext hp.1.symm hp.2.symm))
    · exact edgePair_not_reverse m f e d
  · intro e _
    rcases e with ij | (ud | xy)
    · change (X (Sum.inl ij.val.1) - X (Sum.inl ij.val.2)) ^
        (2 * min (blockSize f ij.val.1) (blockSize f ij.val.2)) ∣ _
      rw [clusterEval_eq]
      exact cluster_factor_dvd f _ _ ij.property.ne U (pairEval F)
        (functionalModel_pair_symmetry m D F hF) hG
    · change (X (Sum.inl ud.1.val) - X (Sum.inr ud.2)) ^ 1 ∣ _
      rw [pow_one]
      exact block_residual_dvd m D f ud.1.val ud.1.property.ge ud.2 F hF
    · change (X (eLabel xy.1) - X (fLabel xy.2)) ^ 1 ∣ _
      rw [pow_one]
      have hd : collisionFactor (K := K) (eLabel xy.1) (fLabel xy.2) ∣ pairEval F :=
        (collisionFactor_dvd_iff _ _ (by simp [eLabel, fLabel]) _).mpr (hnext xy.1 xy.2)
      have hm := map_dvd (residualEval (δ := Residual α β γ) f).toRingHom hd
      change residualEval f (collisionFactor (K := K) (eLabel xy.1) (fLabel xy.2)) ∣
        residualEval f (pairEval F) at hm
      rw [← clusterEval_eq] at hm
      simpa [residualEval, collisionFactor, eLabel, fLabel] using hm

end
end VOA.GordonFullDivisor
