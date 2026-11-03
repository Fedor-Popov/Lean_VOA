import VOA.DeligneAudit.LeviTypeA3GradedCount

/-! The concrete ordered key budget from the three-box multiplicities. -/

namespace VOA.DeligneAudit.A3Sector

/-- The effective multiplicities on the finite ordered key box obey the
type-A₃ binomial budget. -/
theorem a3_ordered_key_count (a b c : ℕ) :
    (∑ i : Fin ((a3KeyBox a b c).card),
      a3KeyOrbitLength b c (a3KeyEnum a b c i) *
        a3EffectiveMultiplicity a b c (a3KeyEnum a b c i)) ≤
      leviCount a b c := by
  let key := a3KeyEnum a b c
  exact a3_count_of_aggregate_multiplicity a b c
    (a3KeyBox a b c).card
    (fun i => (key i).d₁) (fun i => (key i).d₂) (fun i => (key i).d₃)
    (fun i => a3KeyOrbitLength b c (key i))
    (fun i => a3EffectiveMultiplicity a b c (key i))
    (fun i hi => a3_effective_support a b c (key i) hi)
    (fun i => a3KeyOrbitLength_le_power b c (key i))
    (fun x hx y hy z hz => a3_effective_aggregate a b c
      (a3KeyBox a b c).card key (a3KeyEnum_injective a b c)
      x y z (by have := Finset.mem_range.mp hx; omega)
      (by have := Finset.mem_range.mp hy; omega)
      (by have := Finset.mem_range.mp hz; omega))

/-- Numerical form of the ordered effective key budget. -/
theorem a3_ordered_key_count_power (a b c : ℕ) :
    (∑ i : Fin ((a3KeyBox a b c).card),
      a3KeyOrbitLength b c (a3KeyEnum a b c i) *
        a3EffectiveMultiplicity a b c (a3KeyEnum a b c i)) ≤
      4 ^ a * 6 ^ b * 4 ^ c := by
  simpa only [leviCount_eq] using a3_ordered_key_count a b c

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_ordered_key_count
#print axioms VOA.DeligneAudit.A3Sector.a3_ordered_key_count_power
