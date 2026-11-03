import VOA.DeligneAudit.LeviTypeA3BoxAggregate
import VOA.DeligneAudit.LeviTypeA3OrderedStepRank

/-! Effective three-box multiplicities and their aggregate bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

/-- The fixed-degree part of the three-colour mode box. -/
noncomputable def a3ThreeBoxKeyTriples (a b c d₁ d₂ d₃ degree : ℕ) :=
  (a3ThreeBoxModeSet a b c d₁ d₂ d₃).filter
    (fun fg => a3BoxDegree fg = degree)

/-- Keys outside the binomial box contribute no effective multiplicity. -/
noncomputable def a3EffectiveMultiplicity (a b c : ℕ) (k : A3RadicalKey) : ℕ :=
  if k.d₁ ≤ a ∧ k.d₂ ≤ b ∧ k.d₃ ≤ c then
    (a3ThreeBoxKeyTriples a b c k.d₁ k.d₂ k.d₃ k.degree).card else 0

theorem a3_effective_support (a b c : ℕ) (k : A3RadicalKey)
    (hk : a3EffectiveMultiplicity a b c k ≠ 0) :
    k.d₁ ≤ a ∧ k.d₂ ≤ b ∧ k.d₃ ≤ c := by
  by_contra hn
  simp [a3EffectiveMultiplicity, hn] at hk

/-- The multiplicities of all degrees with fixed radical counts fit in one box. -/
theorem a3_effective_aggregate (a b c n : ℕ)
    (key : Fin n → A3RadicalKey) (hinj : Function.Injective key)
    (d₁ d₂ d₃ : ℕ) (h₁ : d₁ ≤ a) (h₂ : d₂ ≤ b) (h₃ : d₃ ≤ c) :
    (∑ i : Fin n,
      if (key i).d₁ = d₁ ∧ (key i).d₂ = d₂ ∧ (key i).d₃ = d₃ then
        a3EffectiveMultiplicity a b c (key i) else 0) ≤
      a.choose d₁ * b.choose d₂ * c.choose d₃ := by
  have hsum := a3_boxTriples_aggregate a b c n d₁ d₂ d₃ key hinj
  calc
    (∑ i : Fin n,
      if (key i).d₁ = d₁ ∧ (key i).d₂ = d₂ ∧ (key i).d₃ = d₃ then
        a3EffectiveMultiplicity a b c (key i) else 0) =
        ∑ i : Fin n,
          if (key i).d₁ = d₁ ∧ (key i).d₂ = d₂ ∧ (key i).d₃ = d₃ then
            (a3ThreeBoxKeyTriples a b c d₁ d₂ d₃ (key i).degree).card
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (key i).d₁ = d₁ ∧ (key i).d₂ = d₂ ∧
          (key i).d₃ = d₃
      · simp [hi, a3EffectiveMultiplicity, a3ThreeBoxKeyTriples, h₁, h₂, h₃]
      · simp [hi]
    _ ≤ (a3ThreeBoxModeSet a b c d₁ d₂ d₃).card := by
      simpa only [a3ThreeBoxKeyTriples] using hsum
    _ = a.choose d₁ * b.choose d₂ * c.choose d₃ :=
      a3ThreeBoxModeSet_card a b c d₁ d₂ d₃ h₁ h₂ h₃

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_effective_support
#print axioms VOA.DeligneAudit.A3Sector.a3_effective_aggregate
