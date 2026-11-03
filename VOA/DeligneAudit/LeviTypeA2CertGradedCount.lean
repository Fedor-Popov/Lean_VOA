import VOA.DeligneAudit.LeviTypeA2CertGradedKS
import VOA.DeligneAudit.LeviTypeA2CertOrderedStepRank

/-! The ordered key budget is at most the A₂ binomial count. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

theorem a2KeyOrbitLength_le_power (q : ℕ) (k : A2RadicalKey) :
    a2KeyOrbitLength q k ≤ 2 ^ (q + k.d₁ - k.d₂) := by
  by_cases hk : a2KeyHeight q k < 0
  · simp [a2KeyOrbitLength, hk]
  · have heq : (a2KeyHeight q k).toNat = q + k.d₁ - k.d₂ := by
      dsimp [a2KeyHeight] at hk ⊢
      omega
    simp [a2KeyOrbitLength, hk, heq]

/-- Effective key multiplicities have support in the binomial box. -/
theorem a2EffectiveMultiplicity_support (p q : ℕ) (k : A2RadicalKey)
    (ha : k.d₁ ≤ p) (hn : a2EffectiveMultiplicity p q k ≠ 0) :
    k.d₁ ≤ p ∧ k.d₂ ≤ q := by
  refine ⟨ha, ?_⟩
  by_contra hb
  simp [a2EffectiveMultiplicity, hb] at hn

/-- The ordered orbit lengths times effective multiplicities fit
under `a2LeviCount`, hence under `3^p 3^q`. -/
theorem a2_ordered_key_count (p q : ℕ) :
    (∑ i : Fin ((a2KeyBox p q).card),
      a2KeyOrbitLength q (a2KeyEnum p q i) *
        a2EffectiveMultiplicity p q (a2KeyEnum p q i)) ≤
      a2LeviCount p q := by
  let n := (a2KeyBox p q).card
  let key := a2KeyEnum p q
  have hsupport : ∀ i : Fin n,
      a2EffectiveMultiplicity p q (key i) ≠ 0 →
        (key i).d₁ ≤ p ∧ (key i).d₂ ≤ q := by
    intro i hi
    have hmem := a2KeyEnum_mem p q i
    have ha : (key i).d₁ ≤ p := by
      simp only [a2KeyBox, Finset.mem_biUnion,
        Finset.mem_image] at hmem
      obtain ⟨a, ha, b, _, d, _, hkey⟩ := hmem
      have heq : a = (key i).d₁ := by
        simpa using congrArg A2RadicalKey.d₁ hkey
      have := Finset.mem_range.mp ha
      omega
    exact a2EffectiveMultiplicity_support p q (key i) ha hi
  have hcount := a2_count_of_aggregate_multiplicity p q n
    (fun i => (key i).d₁) (fun i => (key i).d₂)
    (fun i => a2KeyOrbitLength q (key i))
    (fun i => a2EffectiveMultiplicity p q (key i))
    hsupport (fun i => a2KeyOrbitLength_le_power q (key i))
    (a2_effective_aggregate p q n key (a2KeyEnum_injective p q))
  exact hcount

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyOrbitLength_le_power
#print axioms VOA.DeligneAudit.A3Sector.a2EffectiveMultiplicity_support
#print axioms VOA.DeligneAudit.A3Sector.a2_ordered_key_count
