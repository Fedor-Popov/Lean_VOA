/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.DeligneAuxiliaryCollision
import VOA.Commutative.P3ConductorDegree

/-! # Counting the degree of the Deligne auxiliary conductor -/

namespace VOA.DeligneAuxiliaryCollision

open VOA.CollisionCommonFactors
open VOA.P3ResidualWindowPreservation

noncomputable section

private abbrev PairKind (m d : ℕ) :=
  IncreasingPair (Fin m) ⊕ ((Fin m × Fin d) ⊕ IncreasingPair (Fin d))

private def splitPair {m d : ℕ} (ij : Pair m d) : PairKind m d :=
  if hj : ij.1.2.val < m then
    .inl ⟨(⟨ij.1.1.val, lt_trans ij.2 hj⟩, ⟨ij.1.2.val, hj⟩), ij.2⟩
  else if hi : ij.1.1.val < m then
    .inr (.inl (⟨ij.1.1.val, hi⟩, ⟨ij.1.2.val - m, by
      have h := ij.1.2.isLt
      omega⟩))
  else
    .inr (.inr ⟨(⟨ij.1.1.val - m, by
      have h := ij.1.1.isLt
      omega⟩, ⟨ij.1.2.val - m, by
      have h := ij.1.2.isLt
      omega⟩), by
      have h : ij.1.1.val < ij.1.2.val := ij.2
      change ij.1.1.val - m < ij.1.2.val - m
      omega⟩)

private def joinPair {m d : ℕ} : PairKind m d → Pair m d
  | .inl ij => ⟨(ij.1.1.castAdd d, ij.1.2.castAdd d), ij.2⟩
  | .inr (.inl ij) => ⟨(ij.1.castAdd d, ij.2.natAdd m), by
      have h := ij.1.isLt
      change ij.1.val < m + ij.2.val
      omega⟩
  | .inr (.inr ij) => ⟨(ij.1.1.natAdd m, ij.1.2.natAdd m), by
      change m + ij.1.1.val < m + ij.1.2.val
      exact Nat.add_lt_add_left ij.2 m⟩

private def pairKindEquiv (m d : ℕ) : Pair m d ≃ PairKind m d where
  toFun := splitPair
  invFun := joinPair
  left_inv ij := by
    by_cases hj : ij.1.2.val < m
    · apply Subtype.ext
      simp [splitPair, joinPair, hj]
    · by_cases hi : ij.1.1.val < m
      · apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;>
          simp [splitPair, joinPair, hj, hi] <;> omega
      · apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;>
          simp [splitPair, joinPair, hj, hi] <;> omega
  right_inv a := by
    rcases a with ij | (ij | ij)
    · simp [joinPair, splitPair, ij.1.2.isLt]
    · have hj : ¬m + ij.2.val < m := by omega
      simp [joinPair, splitPair, hj, ij.1.isLt]
    · have hi : ¬m + ij.1.1.val < m := by omega
      have hj : ¬m + ij.1.2.val < m := by omega
      simp [joinPair, splitPair, hi, hj]

private def kindOrder {m d : ℕ} : PairKind m d → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

private theorem order_joinPair {m d : ℕ} (a : PairKind m d) :
    order (joinPair a) = kindOrder a := by
  rcases a with ij | (ij | ij)
  · simp [joinPair, order, kindOrder, ij.1.2.isLt]
  · have hj : ¬m + ij.2.val < m := by omega
    simp [joinPair, order, kindOrder, hj, ij.1.isLt]
  · have hi : ¬m + ij.1.1.val < m := by omega
    have hj : ¬m + ij.1.2.val < m := by omega
    simp [joinPair, order, kindOrder, hi, hj]

/-- There is one factor for each mixed pair and two for each auxiliary pair. -/
theorem conductorDegree_eq (m d : ℕ) : conductorDegree m d = m * d + d * (d - 1) := by
  have hsum : (∑ ij : Pair m d, order ij) = ∑ a : PairKind m d, kindOrder a := by
    rw [← (pairKindEquiv m d).symm.sum_comp order]
    apply Finset.sum_congr rfl
    intro a _
    exact order_joinPair a
  rw [conductorDegree, hsum]
  simp only [PairKind, Fintype.sum_sum_type, kindOrder, Finset.sum_const_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, zero_add,
    Fintype.card_prod, Fintype.card_fin, card_increasingPair_fin]
  simp only [Nat.cast_id]
  rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self d).two_dvd]

/-- Adding the current and Casimir base conformal weights gives the exponent
used in the Deligne auxiliary character. -/
theorem auxiliaryConformalShift (m d : ℕ) :
    m + 2 * d + conductorDegree m d = m + d + d * (m + d) := by
  rw [conductorDegree_eq]
  cases d with
  | zero => simp
  | succ d => simp; ring

end

end VOA.DeligneAuxiliaryCollision

section AxiomAudit
#print axioms VOA.DeligneAuxiliaryCollision.conductorDegree_eq
#print axioms VOA.DeligneAuxiliaryCollision.auxiliaryConformalShift
end AxiomAudit
