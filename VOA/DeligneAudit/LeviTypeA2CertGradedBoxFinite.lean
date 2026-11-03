import VOA.DeligneAudit.LeviTypeA2CertGradedKeySpan
import VOA.DeligneAudit.LeviTypeA2CertBoxCard

/-! Finite two-colour box generators at a fixed radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Pairs of box monomials whose total mode degree is `d`. -/
noncomputable def a2TwoBoxKeyPairs (p q a b d : ℕ) :
    Finset ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) :=
  (a2BoxModeSet p a ×ˢ a2BoxModeSet q b).filter
    (fun fg => (Finsupp.weight om fg.1).2 +
      (Finsupp.weight om fg.2).2 = d)

private theorem a2_weight_first (f : ℕ →₀ ℕ) :
    (Finsupp.weight om f).1 = Finsupp.degree f := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
    Prod.fst_sum, om]

noncomputable def a2TwoBoxValue
    (fg : (ℕ →₀ ℕ) × (ℕ →₀ ℕ)) : V :=
  (Sl2Weyl.evAlg (fun i => ρ.op 3 i)
      (VOA.DeligneAudit.A2.CVRoots.sl2_first ρ).hFF
      (MvPolynomial.monomial fg.1 1) *
    Sl2Weyl.evAlg (fun i => ρ.op 5 i) (by
      intro i j
      apply sub_eq_zero.mp
      simp [op_comm_end, Fin.sum_univ_eight,
        VOA.AffineSl3.bracketTable])
      (MvPolynomial.monomial fg.2 1)) w

noncomputable def a2TwoBoxKeyVectors (p q a b d : ℕ) : Finset V := by
  classical
  exact (a2TwoBoxKeyPairs p q a b d).image (a2TwoBoxValue ρ w)

/-- The two-box span at one key has an explicit finite generating set. -/
theorem a2TwoBoxKeySpan_le_finite (p q a b d : ℕ)
    (ha : a ≤ p) (hb : b ≤ q) :
    a2TwoBoxKeySpan ρ w p q a b d ≤
      Submodule.span ℂ (a2TwoBoxKeyVectors ρ w p q a b d : Set V) := by
  classical
  unfold a2TwoBoxKeySpan
  rw [iSup_le_iff]
  intro d₁
  rw [iSup_le_iff]
  intro d₂
  rw [iSup_le_iff]
  intro hd
  rw [a2TwoBoxSpan, Submodule.span_le]
  intro v hv
  obtain ⟨f, g, hfp, hgq, hfw, hgw, rfl⟩ := hv
  have hfa : Finsupp.degree f = a := by
    rw [← a2_weight_first]
    simp [hfw]
  have hgb : Finsupp.degree g = b := by
    rw [← a2_weight_first]
    simp [hgw]
  have hpair : (f, g) ∈ a2TwoBoxKeyPairs p q a b d := by
    simp only [a2TwoBoxKeyPairs, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨(mem_a2BoxModeSet p a ha f).mpr ⟨hfa, hfp⟩,
      (mem_a2BoxModeSet q b hb g).mpr ⟨hgb, hgq⟩⟩, ?_⟩
    rw [hfw, hgw]
    exact hd
  apply Submodule.subset_span
  change a2TwoBoxValue ρ w (f, g) ∈
    (a2TwoBoxKeyVectors ρ w p q a b d : Set V)
  exact Finset.mem_image.mpr ⟨(f, g), hpair, rfl⟩

theorem a2TwoBoxKeyVectors_card_le (p q a b d : ℕ) :
    (a2TwoBoxKeyVectors ρ w p q a b d).card ≤
      (a2TwoBoxKeyPairs p q a b d).card := by
  classical
  exact Finset.card_image_le

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2TwoBoxKeySpan_le_finite
#print axioms VOA.DeligneAudit.A3Sector.a2TwoBoxKeyVectors_card_le
