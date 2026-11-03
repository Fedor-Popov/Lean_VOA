import VOA.DeligneAudit.D4LeviKSMixedTargetSeed

/-! The maximal-active Rx target polynomial is complete homogeneous in all target slots. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

def rxMixedTargetEquiv (a b c : ℕ) :
    (Fin c ⊕ (Fin b ⊕ Fin a)) ≃ PairTarget a b c where
  toFun := rxMixedTargetSlot a b c
  invFun
    | Sum.inl x => Sum.inr (Sum.inr x)
    | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl y)
    | Sum.inr (Sum.inr z) => Sum.inl z
  left_inv := by
    intro t
    rcases t with z | (y | x) <;> rfl
  right_inv := by
    intro t
    rcases t with x | (y | z) <;> rfl

theorem rxMixedTarget_eq_hsymm (a b c s : ℕ) :
    (rxMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) =
      hsymm (PairTarget a b c) ℂ s := by
  rw [rxMixedTarget_polynomial]
  exact rename_hsymm _ _ s (rxMixedTargetEquiv a b c)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rxMixedTarget_eq_hsymm
