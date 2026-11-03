/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonFunctionalRelabel
import VOA.Commutative.GordonPairedRelations

/-! # Canonical pair evaluations on a fixed three-species particle set -/

namespace VOA.GordonPairIndexing
open MvPolynomial VOA.GordonPairedEvaluation VOA.GordonPairedRelations
open VOA.GordonCommonFactors
noncomputable section

abbrev Original (a b c : ℕ) := Fin a ⊕ (Fin b ⊕ Fin c)
abbrev ResidualIndex (a R : ℕ) := {i : Fin a // R ≤ i.val}

/-- Split a species into its first R paired particles and the remaining particles. -/
def splitFin (a R : ℕ) (hR : R ≤ a) : Fin a ≃ Fin R ⊕ ResidualIndex a R where
  toFun i := if h : i.val < R then .inl ⟨i.val, h⟩ else .inr ⟨i, by omega⟩
  invFun := Sum.elim (fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hR⟩) Subtype.val
  left_inv i := by dsimp; split <;> rfl
  right_inv i := by
    rcases i with i | i
    · simp [i.isLt]
    · simp [show ¬ i.val.val < R by omega]

/-- The residual cardinality is exactly the original count minus the paired count. -/
theorem card_residualIndex (a R : ℕ) (hR : R ≤ a) :
    Fintype.card (ResidualIndex a R) = a - R := by
  have h := Fintype.card_congr (splitFin a R hR)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

def sourceEquiv (a b c R : ℕ) (ha : R ≤ a) (hb : R ≤ b) :
    Original a b c ≃ Source (Fin R) (ResidualIndex a R) (ResidualIndex b R) (Fin c) :=
  Equiv.sumCongr (splitFin a R ha) (Equiv.sumCongr (splitFin b R hb) (Equiv.refl _))

def originalColor (a b c : ℕ) : Original a b c → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 2
  | .inr (.inr _) => 1

theorem sourceEquiv_color (a b c R : ℕ) (ha : R ≤ a) (hb : R ≤ b) (i : Original a b c) :
    sourceColor (sourceEquiv a b c R ha hb i) = originalColor a b c i := by
  rcases i with i | (i | i)
  · simp only [sourceEquiv, Equiv.sumCongr_apply, Sum.map_inl, splitFin,
      Equiv.coe_fn_mk, sourceColor, originalColor]
    split <;> rfl
  · simp only [sourceEquiv, Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, splitFin,
      Equiv.coe_fn_mk, sourceColor, originalColor]
    split <;> rfl
  · rfl

/-- The compact literal R-pair evaluation index. -/
def pairedIndex (a b c R : ℕ) (ha : R ≤ a) (hb : R ≤ b) :
    Original a b c → Target (Fin R) (ResidualIndex a R) (ResidualIndex b R) (Fin c) :=
  pairIndex ∘ sourceEquiv a b c R ha hb

/-- Embed compact output labels back into the fixed source-label type. -/
def representative (a b c R : ℕ) (ha : R ≤ a) :
    Target (Fin R) (ResidualIndex a R) (ResidualIndex b R) (Fin c) → Original a b c
  | .inl i => .inl ⟨i.val, lt_of_lt_of_le i.isLt ha⟩
  | .inr (.inl i) => .inl i.val
  | .inr (.inr (.inl i)) => .inr (.inl i.val)
  | .inr (.inr (.inr i)) => .inr (.inr i)

/-- Identify the first R f-particles with the corresponding e-particles. -/
def mergeIndex (a b c R : ℕ) (ha : R ≤ a) : Original a b c → Original a b c
  | .inl i => .inl i
  | .inr (.inl i) => if h : i.val < R then .inl ⟨i.val, lt_of_lt_of_le h ha⟩ else .inr (.inl i)
  | .inr (.inr i) => .inr (.inr i)

theorem representative_pairedIndex (a b c R : ℕ) (ha : R ≤ a) (hb : R ≤ b) :
    representative a b c R ha ∘ pairedIndex a b c R ha hb = mergeIndex a b c R ha := by
  funext i
  rcases i with i | (i | i)
  · simp only [Function.comp_apply, pairedIndex, sourceEquiv, Equiv.sumCongr_apply,
      Sum.map_inl, splitFin, Equiv.coe_fn_mk, mergeIndex]
    split <;> rfl
  · simp only [Function.comp_apply, pairedIndex, sourceEquiv, Equiv.sumCongr_apply,
      Sum.map_inr, Sum.map_inl, splitFin, Equiv.coe_fn_mk, mergeIndex]
    split <;> rfl
  · rfl

theorem pairedIndex_zero_injective (a b c : ℕ) :
    Function.Injective (pairedIndex a b c 0 (Nat.zero_le _) (Nat.zero_le _)) := by
  have h := representative_pairedIndex a b c 0 (Nat.zero_le _) (Nat.zero_le _)
  have hm : mergeIndex a b c 0 (Nat.zero_le _) = id := by
    funext i
    rcases i with i | (i | i) <;> simp [mergeIndex]
  have hl : Function.LeftInverse (representative a b c 0 (Nat.zero_le _))
      (pairedIndex a b c 0 (Nat.zero_le _) (Nat.zero_le _)) := by
    intro i
    exact congrFun (h.trans hm) i
  exact hl.injective

end
end VOA.GordonPairIndexing
