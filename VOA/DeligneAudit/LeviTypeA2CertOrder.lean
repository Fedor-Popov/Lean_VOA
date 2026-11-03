import VOA.DeligneAudit.LeviTypeA2CertStepOrbits

/-! Descending enumeration of the finite radical key box. -/

namespace VOA.DeligneAudit.A3Sector

/-- Weak order whose strict part is descending height-degree key order. -/
def a2KeyDescLE (q : ℕ) (a b : A2RadicalKey) : Prop :=
  a = b ∨ a2KeyLess q b a

instance (q : ℕ) : IsTrans A2RadicalKey (a2KeyDescLE q) where
  trans := by
    intro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (a2KeyLess_trans q hbc hab)

instance (q : ℕ) : Std.Antisymm (a2KeyDescLE q) where
  antisymm := by
    intro a b hab hba
    rcases hab with hab | hab
    · exact hab
    rcases hba with hba | hba
    · exact hba.symm
    · exact False.elim ((a2KeyLess_irrefl q a)
        (a2KeyLess_trans q hba hab))

instance (q : ℕ) : Std.Total (a2KeyDescLE q) where
  total := by
    intro a b
    rcases a2KeyLess_trichotomy q a b with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

noncomputable instance (q : ℕ) : DecidableRel (a2KeyDescLE q) :=
  Classical.decRel _

/-- All potentially nonzero keys, ordered from highest to lowest. -/
noncomputable def a2OrderedKeys (p q : ℕ) : List A2RadicalKey :=
  (a2KeyBox p q).sort (a2KeyDescLE q)

theorem mem_a2OrderedKeys (p q : ℕ) (k : A2RadicalKey) :
    k ∈ a2OrderedKeys p q ↔ k ∈ a2KeyBox p q := by
  simpa only [a2OrderedKeys] using
    (Finset.mem_sort (s := a2KeyBox p q) (r := a2KeyDescLE q))

theorem length_a2OrderedKeys (p q : ℕ) :
    (a2OrderedKeys p q).length = (a2KeyBox p q).card := by
  simpa only [a2OrderedKeys] using
    (Finset.length_sort (s := a2KeyBox p q) (r := a2KeyDescLE q))

theorem pairwise_a2OrderedKeys (p q : ℕ) :
    (a2OrderedKeys p q).Pairwise (a2KeyDescLE q) := by
  simpa only [a2OrderedKeys] using
    (Finset.pairwise_sort (a2KeyBox p q) (a2KeyDescLE q))

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.mem_a2OrderedKeys
#print axioms VOA.DeligneAudit.A3Sector.length_a2OrderedKeys
#print axioms VOA.DeligneAudit.A3Sector.pairwise_a2OrderedKeys
