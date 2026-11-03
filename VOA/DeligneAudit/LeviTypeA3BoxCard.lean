import VOA.DeligneAudit.LeviTypeA3ConversionGraded
import VOA.DeligneAudit.LeviTypeA2CertBoxCard

/-! The three radical mode boxes have the expected binomial product count. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

def a3ThreeBoxModeSet (a b c d₁ d₂ d₃ : ℕ) :
    Finset (((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ →₀ ℕ)) :=
  (a2BoxModeSet a d₁ ×ˢ a2BoxModeSet b d₂) ×ˢ a2BoxModeSet c d₃

theorem a3ThreeBoxModeSet_card (a b c d₁ d₂ d₃ : ℕ)
    (h₁ : d₁ ≤ a) (h₂ : d₂ ≤ b) (h₃ : d₃ ≤ c) :
    (a3ThreeBoxModeSet a b c d₁ d₂ d₃).card =
      a.choose d₁ * b.choose d₂ * c.choose d₃ := by
  rw [a3ThreeBoxModeSet, Finset.card_product,
    card_a2BoxModeSet_product a b d₁ d₂ h₁ h₂,
    card_a2BoxModeSet c d₃ h₃]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3ThreeBoxModeSet_card
