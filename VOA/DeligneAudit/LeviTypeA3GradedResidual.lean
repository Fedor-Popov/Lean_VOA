import VOA.DeligneAudit.LeviTypeA3GradedBoxQuot

/-! A single explicit residual for the all-weight type-A₃ theorem. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

/-- The finite-key quotient inequality left by the graded box reduction. -/
def a3FixedKeyKS : Prop :=
  ∀ (a b c : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V),
    LocalWeylRel ρ w (weightABC a b c) →
      ∀ i : Fin ((a3KeyBox a b c).card),
        Module.finrank ℂ
          (a3KeyLayer ρ w (a3KeyEnum a b c i) ⧸
            (a3KeyPrefix ρ w (a3KeyEnum a b c) i.val).comap
              (a3KeyLayer ρ w (a3KeyEnum a b c i)).subtype) ≤
          a3EffectiveMultiplicity a b c (a3KeyEnum a b c i)

/-- Proving the fixed-key box residual completes `TypeABound`. -/
theorem a3_typeABound_of_fixedKeyKS (hKS : a3FixedKeyKS) : TypeABound := by
  intro a b c V _ _ ρ w h
  exact a3_all_weight_rank_of_ks ρ w a b c h (hKS a b c V ρ w h)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_typeABound_of_fixedKeyKS
