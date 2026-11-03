import VOA.DeligneAudit.LeviTypeA3GradedThreeTarget

/-! The sharp fixed-key target, including keys outside the three-count box. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Outside the three sharp colour counts, the required target is just the
higher-key Levi closure. -/
def a3EffectiveTarget (a b c : ℕ) (k : A3RadicalKey) : Submodule ℂ V :=
  if k.d₁ ≤ a ∧ k.d₂ ≤ b ∧ k.d₃ ≤ c then
    a3ThreeBoxTarget ρ w a b c k
  else a3HigherLeviClosure ρ w b c k

theorem a3_effective_rank_of_target (a b c : ℕ) (k : A3RadicalKey)
    (hspan : a3KeyLayer ρ w k ≤ a3EffectiveTarget ρ w a b c k) :
    Module.finrank ℂ
      (a3KeyLayer ρ w k ⧸
        (a3HigherLeviClosure ρ w b c k).comap (a3KeyLayer ρ w k).subtype) ≤
      a3EffectiveMultiplicity a b c k := by
  by_cases hs : k.d₁ ≤ a ∧ k.d₂ ≤ b ∧ k.d₃ ≤ c
  · have hspan' : a3KeyLayer ρ w k ≤ a3ThreeBoxTarget ρ w a b c k := by
      simpa only [a3EffectiveTarget, if_pos hs] using hspan
    simpa only [a3EffectiveMultiplicity, if_pos hs] using
      a3_key_rank_of_target ρ w a b c k hspan'
  · have hspan' : a3KeyLayer ρ w k ≤ a3HigherLeviClosure ρ w b c k := by
      simpa only [a3EffectiveTarget, if_neg hs] using hspan
    have hz := a3_quotient_finrank_le_finset
      (a3HigherLeviClosure ρ w b c k) (a3KeyLayer ρ w k)
      (∅ : Finset V) (by simpa using hspan')
    simpa only [a3EffectiveMultiplicity, if_neg hs, Finset.card_empty] using hz

/-- It remains to put each radical key layer in the effective target. -/
theorem a3_fixedKeyKS_of_effective_span
    (hspan : ∀ (a b c : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule bracketTable V) (w : V),
      LocalWeylRel ρ w (weightABC a b c) →
        ∀ k : A3RadicalKey,
          a3KeyLayer ρ w k ≤ a3EffectiveTarget ρ w a b c k) :
    a3FixedKeyKS := by
  intro a b c V _ _ ρ w h i
  have hp := a3OrderedPrefix_eq_higher ρ w a b c h i.val i.isLt
  rw [hp]
  exact a3_effective_rank_of_target ρ w a b c (a3KeyEnum a b c i)
    (hspan a b c V ρ w h (a3KeyEnum a b c i))

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_effective_rank_of_target
#print axioms VOA.DeligneAudit.A3Sector.a3_fixedKeyKS_of_effective_span
