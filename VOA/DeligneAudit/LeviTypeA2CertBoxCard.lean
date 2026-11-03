import VOA.DeligneAudit.LeviTypeA2CertF2Defect
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-! Exact cardinality of the two-colour mode boxes. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

/-- Mode multiplicities of length `a` supported in the sl₂ box for weight `m`. -/
def a2BoxModeSet (m a : ℕ) : Finset (ℕ →₀ ℕ) :=
  (Finset.range (m - a + 1)).finsuppAntidiag a

theorem mem_a2BoxModeSet (m a : ℕ) (ha : a ≤ m) (f : ℕ →₀ ℕ) :
    f ∈ a2BoxModeSet m a ↔ Finsupp.degree f = a ∧ BoxP m f := by
  rw [a2BoxModeSet, Finset.mem_finsuppAntidiag']
  constructor
  · rintro ⟨hdegree, hsupp⟩
    have hd : Finsupp.degree f = a := by
      simpa [Finsupp.degree_apply] using hdegree
    refine ⟨hd, ?_⟩
    intro i hi
    have hir := hsupp hi
    simp only [Finset.mem_range] at hir
    omega
  · rintro ⟨hd, hbox⟩
    constructor
    · simpa [Finsupp.degree_apply] using hd
    · intro i hi
      have h := hbox i hi
      simp only [Finset.mem_range]
      omega

theorem card_a2BoxModeSet (m a : ℕ) (ha : a ≤ m) :
    (a2BoxModeSet m a).card = m.choose a := by
  rw [a2BoxModeSet, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_range]
  have h : m - a + 1 + a - 1 = m := by omega
  rw [h]

theorem card_a2BoxModeSet_product (p q a b : ℕ)
    (ha : a ≤ p) (hb : b ≤ q) :
    (a2BoxModeSet p a ×ˢ a2BoxModeSet q b).card =
      p.choose a * q.choose b := by
  rw [Finset.card_product, card_a2BoxModeSet p a ha,
    card_a2BoxModeSet q b hb]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.mem_a2BoxModeSet
#print axioms VOA.DeligneAudit.A3Sector.card_a2BoxModeSet
#print axioms VOA.DeligneAudit.A3Sector.card_a2BoxModeSet_product
