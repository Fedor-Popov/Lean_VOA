import VOA.DeligneAudit.D4LeviStepRank
import VOA.DeligneAudit.LeviTypeA2CertBoxCard
import Mathlib.Data.Nat.Choose.Multinomial

/-! The four multiplicity classes and the three mode boxes of the D4 count. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.Sl2Weyl

/-- The mode boxes for the unpaired X, Y, and Z letters. -/
def ksBoxTriples (m a b c : ℕ) :
    Finset (((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ →₀ ℕ)) :=
  (a2BoxModeSet (m - c - b) a ×ˢ a2BoxModeSet (m - c) b) ×ˢ
    a2BoxModeSet m c

noncomputable def ksBoxDegree
    (t : ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ →₀ ℕ)) : ℕ :=
  (Finsupp.weight om t.1.1).2 + (Finsupp.weight om t.1.2).2 +
    (Finsupp.weight om t.2).2

noncomputable def ksGradedBoxCount (m a b c d : ℕ) : ℕ :=
  ((ksBoxTriples m a b c).filter fun t => ksBoxDegree t = d).card

theorem ksBoxTriples_card (m a b c : ℕ)
    (ha : a ≤ m - c - b) (hb : b ≤ m - c) (hc : c ≤ m) :
    (ksBoxTriples m a b c).card =
      (m - c - b).choose a * (m - c).choose b * m.choose c := by
  simp [ksBoxTriples, Finset.card_product,
    card_a2BoxModeSet _ _ ha, card_a2BoxModeSet _ _ hb,
    card_a2BoxModeSet _ _ hc]

/-- The four classes have weights 16, 6, 6, and 1. -/
def ksClassWeight : Fin 4 → ℕ
  | 0 => 16
  | 1 => 6
  | 2 => 6
  | _ => 1

theorem ksClassWeight_sum : (∑ j : Fin 4, ksClassWeight j) = 29 := by
  decide

/-- Multinomial expansion of the numerical part of the D4 box count. -/
theorem ksWeightedMultinomial (m : ℕ) :
    (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m,
      Nat.multinomial Finset.univ k *
        ∏ j : Fin 4, ksClassWeight j ^ k j) = 29 ^ m := by
  have h := Finset.sum_pow_eq_sum_piAntidiag
    (Finset.univ : Finset (Fin 4)) ksClassWeight m
  simpa only [ksClassWeight_sum] using h.symm

/-- The four-colour multinomial is the product of the three box cardinalities. -/
theorem ksMultinomial_choose (a bp b c : ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin 4)) ![a, bp, b, c] =
      (a + bp + b + c).choose c * (a + bp + b).choose b *
        (a + bp).choose a := by
  rw [show (Finset.univ : Finset (Fin 4)) =
    insert 3 (insert 2 (insert 0 {1})) by decide]
  rw [Nat.multinomial_insert (by decide),
    Nat.multinomial_insert (by decide),
    Nat.multinomial_insert (by decide)]
  simp [Nat.multinomial_singleton]
  have h1 : c + (b + (a + bp)) = a + bp + b + c := by omega
  have h2 : b + (a + bp) = a + bp + b := by omega
  rw [h1, h2]
  ring

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBoxTriples_card
#print axioms VOA.DeligneAudit.D4Levi.ksClassWeight_sum
#print axioms VOA.DeligneAudit.D4Levi.ksWeightedMultinomial
#print axioms VOA.DeligneAudit.D4Levi.ksMultinomial_choose
