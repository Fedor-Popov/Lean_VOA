import VOA.DeligneAudit.LeviTypeA2CertGradedHighCount

/-! Aggregate key multiplicity from the disjoint degree fibers. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

/-- Effective multiplicity: keys beyond the F₂ box have zero quotient. -/
noncomputable def a2EffectiveMultiplicity (p q : ℕ) (k : A2RadicalKey) : ℕ :=
  if k.d₂ ≤ q then
    (a2TwoBoxKeyPairs p q k.d₁ k.d₂ k.degree).card else 0

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2_key_quot_finrank_le_effective (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    (ha : k.d₁ ≤ p) :
    let F := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    let S := a2KeyLayer ρ w k
    Module.finrank ℂ (S ⧸ F.comap S.subtype) ≤
      a2EffectiveMultiplicity p q k := by
  by_cases hb : k.d₂ ≤ q
  · simpa only [a2EffectiveMultiplicity, if_pos hb] using
      a2_key_quot_finrank_le_boxPairs ρ w p q h k ha hb
  · have hzero := a2_key_quot_finrank_zero_of_second_gt ρ w p q h k
      (by omega)
    simpa only [a2EffectiveMultiplicity, if_neg hb, hzero] using
      (Nat.le_refl 0)

/-- The effective multiplicities over all keys of fixed counts fit
inside the product of the two finite sl₂ boxes. -/
theorem a2_effective_aggregate (p q n : ℕ)
    (key : Fin n → A2RadicalKey) (hinj : Function.Injective key) :
    A2AggregateKeyMultiplicity p q n
      (fun i => (key i).d₁) (fun i => (key i).d₂)
      (fun i => a2EffectiveMultiplicity p q (key i)) := by
  intro a ha b hb
  have ha' : a ≤ p := by
    have := Finset.mem_range.mp ha
    omega
  have hb' : b ≤ q := by
    have := Finset.mem_range.mp hb
    omega
  have hsum := a2_boxPairs_aggregate p q n a b key hinj
  calc
    (∑ i : Fin n,
      if (key i).d₁ = a ∧ (key i).d₂ = b then
        a2EffectiveMultiplicity p q (key i) else 0) =
        ∑ i : Fin n,
          if (key i).d₁ = a ∧ (key i).d₂ = b then
            (a2TwoBoxKeyPairs p q a b (key i).degree).card else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (key i).d₁ = a ∧ (key i).d₂ = b
      · rw [if_pos hi, if_pos hi]
        simp [a2EffectiveMultiplicity, hi.1, hi.2, hb']
      · simp [hi]
    _ ≤ (a2BoxModeSet p a ×ˢ a2BoxModeSet q b).card := hsum
    _ = p.choose a * q.choose b :=
      card_a2BoxModeSet_product p q a b ha' hb'

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_quot_finrank_le_effective
#print axioms VOA.DeligneAudit.A3Sector.a2_effective_aggregate
