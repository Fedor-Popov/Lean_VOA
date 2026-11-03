import VOA.DeligneAudit.D4LeviKSMixedZeroSlots

/-! Maximal-active mixed seeds with their zero-mode spectator blocks. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def rxMixedSourceEquiv (a b c : ℕ) :
    (Fin c ⊕ (Fin b ⊕ Fin a)) ⊕ Fin b ≃ PairSource a b c where
  toFun
    | Sum.inl (Sum.inl z) => Sum.inr (Sum.inr z)
    | Sum.inl (Sum.inr x) => Sum.inl x
    | Sum.inr y => Sum.inr (Sum.inl y)
  invFun
    | Sum.inl x => Sum.inl (Sum.inr x)
    | Sum.inr (Sum.inl y) => Sum.inr y
    | Sum.inr (Sum.inr z) => Sum.inl (Sum.inl z)
  left_inv := by
    intro t
    rcases t with (z | x) | y <;> rfl
  right_inv := by
    intro t
    rcases t with x | (y | z) <;> rfl

def ryMixedSourceEquiv (a b c : ℕ) :
    (Fin c ⊕ Fin b) ⊕ (Fin b ⊕ Fin a) ≃ PairSource a b c where
  toFun
    | Sum.inl (Sum.inl z) => Sum.inr (Sum.inr z)
    | Sum.inl (Sum.inr y) => Sum.inr (Sum.inl y)
    | Sum.inr x => Sum.inl x
  invFun
    | Sum.inl x => Sum.inr x
    | Sum.inr (Sum.inl y) => Sum.inl (Sum.inr y)
    | Sum.inr (Sum.inr z) => Sum.inl (Sum.inl z)
  left_inv := by
    intro t
    rcases t with (z | y) | x <;> rfl
  right_inv := by
    intro t
    rcases t with x | (y | z) <;> rfl

theorem rxMixedSeed_rename (a b c s : ℕ) :
    rxMixedSeed a b c s =
      rename (rxMixedSourceEquiv a b c)
        (rename Sum.inl (hsymm (Fin c ⊕ (Fin b ⊕ Fin a)) ℂ s)) := by
  simp only [rxMixedSeed, rename_rename]
  have hslot : rxMixedSlot a b c =
      (rxMixedSourceEquiv a b c) ∘ Sum.inl := by
    funext t
    rcases t with z | x <;> rfl
  rw [hslot]

theorem ryMixedSeed_rename (a b c s : ℕ) :
    ryMixedSeed a b c s =
      rename (ryMixedSourceEquiv a b c)
        (rename Sum.inl (hsymm (Fin c ⊕ Fin b) ℂ s)) := by
  simp only [ryMixedSeed, rename_rename]
  have hslot : ryMixedSlot a b c =
      (ryMixedSourceEquiv a b c) ∘ Sum.inl := by
    funext t
    rcases t with z | y <;> rfl
  rw [hslot]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rxMixedSeed_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c s : ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b c) (rxMixedSeed a b c s) =
      ((yOp ρ 0) ^ b)
        (xyzEvaluation ρ w
          (fun t : Fin c ⊕ (Fin b ⊕ Fin a) =>
            match t with
            | Sum.inl _ => 5
            | Sum.inr _ => 1)
          (hsymm (Fin c ⊕ (Fin b ⊕ Fin a)) ℂ s)) := by
  rw [rxMixedSeed_rename]
  rw [xyzEvaluation_rename_bijection]
  rw [xyzEvaluation_sum_zero_slots]
  have hshape :
      ((pairSourceShape a b c ∘ rxMixedSourceEquiv a b c) ∘ Sum.inl) =
        fun t : Fin c ⊕ (Fin b ⊕ Fin a) =>
          match t with
          | Sum.inl _ => 5
          | Sum.inr _ => 1 := by
    funext t
    rcases t with z | x <;> rfl
  rw [hshape]
  simp [rxMixedSourceEquiv, pairSourceShape, yOp, radicalColour,
    List.prod_replicate]

theorem ryMixedSeed_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c s : ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b c) (ryMixedSeed a b c s) =
      ((xOp ρ 0) ^ (a + b))
        (xyzEvaluation ρ w
          (fun t : Fin c ⊕ Fin b =>
            match t with
            | Sum.inl _ => 5
            | Sum.inr _ => 4)
          (hsymm (Fin c ⊕ Fin b) ℂ s)) := by
  rw [ryMixedSeed_rename]
  rw [xyzEvaluation_rename_bijection]
  rw [xyzEvaluation_sum_zero_slots]
  have hshape :
      ((pairSourceShape a b c ∘ ryMixedSourceEquiv a b c) ∘ Sum.inl) =
        fun t : Fin c ⊕ Fin b =>
          match t with
          | Sum.inl _ => 5
          | Sum.inr _ => 4 := by
    funext t
    rcases t with z | y <;> rfl
  rw [hshape]
  simp [ryMixedSourceEquiv, pairSourceShape, xOp, radicalColour,
    List.prod_replicate, Nat.add_comm]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rxMixedSeed_rename
#print axioms VOA.DeligneAudit.D4Levi.ryMixedSeed_rename
#print axioms VOA.DeligneAudit.D4Levi.rxMixedSeed_evaluation
#print axioms VOA.DeligneAudit.D4Levi.ryMixedSeed_evaluation
