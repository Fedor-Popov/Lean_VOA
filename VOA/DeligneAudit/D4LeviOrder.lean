import VOA.DeligneAudit.D4LeviHigher

/-! Finite ordered search boxes for six-count radical keys. -/

namespace VOA.DeligneAudit.D4Levi

/-- A finite box with a common bound on six letter counts and total mode degree. -/
def keyBox (n d : ℕ) : Finset RadicalKey :=
  (Finset.range (n + 1)).biUnion fun e =>
    (Finset.range (n + 1)).biUnion fun x =>
      (Finset.range (n + 1)).biUnion fun u =>
        (Finset.range (n + 1)).biUnion fun up =>
          (Finset.range (n + 1)).biUnion fun y =>
            (Finset.range (n + 1)).biUnion fun z =>
              (Finset.range (d + 1)).image fun degree =>
                ⟨e, x, u, up, y, z, degree⟩

theorem mem_keyBox (n d : ℕ) (k : RadicalKey)
    (he : k.e ≤ n) (hx : k.x ≤ n) (hu : k.u ≤ n)
    (hup : k.up ≤ n) (hy : k.y ≤ n) (hz : k.z ≤ n)
    (hd : k.degree ≤ d) : k ∈ keyBox n d := by
  unfold keyBox
  apply Finset.mem_biUnion.mpr
  refine ⟨k.e, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.x, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.u, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.up, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.y, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.z, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨k.degree, Finset.mem_range.mpr (by omega), by cases k; rfl⟩

def keyDescLE (m : ℕ) (a b : RadicalKey) : Prop :=
  a = b ∨ keyLess m b a

instance (m : ℕ) : IsTrans RadicalKey (keyDescLE m) where
  trans := by
    intro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (keyLess_trans m hbc hab)

instance (m : ℕ) : Std.Antisymm (keyDescLE m) where
  antisymm := by
    intro a b hab hba
    rcases hab with hab | hab
    · exact hab
    rcases hba with hba | hba
    · exact hba.symm
    · exact False.elim ((keyLess_irrefl m a)
        (keyLess_trans m hba hab))

instance (m : ℕ) : Std.Total (keyDescLE m) where
  total := by
    intro a b
    rcases keyLess_trichotomy m a b with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

noncomputable instance (m : ℕ) : DecidableRel (keyDescLE m) :=
  Classical.decRel _

/-- A finite key box in descending Levi-weight order. -/
noncomputable def orderedKeys (m n d : ℕ) : List RadicalKey :=
  (keyBox n d).sort (keyDescLE m)

theorem mem_orderedKeys (m n d : ℕ) (k : RadicalKey) :
    k ∈ orderedKeys m n d ↔ k ∈ keyBox n d := by
  simpa only [orderedKeys] using
    (Finset.mem_sort (s := keyBox n d) (r := keyDescLE m))

theorem pairwise_orderedKeys (m n d : ℕ) :
    (orderedKeys m n d).Pairwise (keyDescLE m) := by
  simpa only [orderedKeys] using
    (Finset.pairwise_sort (keyBox n d) (keyDescLE m))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.mem_keyBox
#print axioms VOA.DeligneAudit.D4Levi.mem_orderedKeys
#print axioms VOA.DeligneAudit.D4Levi.pairwise_orderedKeys
