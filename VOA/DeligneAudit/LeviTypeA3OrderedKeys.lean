import VOA.DeligneAudit.LeviTypeA3Prefix
import VOA.DeligneAudit.LeviTypeA3FiniteBox

/-! Descending enumeration of the global finite radical key box. -/

namespace VOA.DeligneAudit.A3Sector

noncomputable def a3GlobalOrderedKeys (a b c : ℕ) : List A3RadicalKey :=
  (a3KeyBox a b c).sort (a3KeyDescLE b c)

theorem a3GlobalOrderedKeys_mem (a b c : ℕ) (k : A3RadicalKey) :
    k ∈ a3GlobalOrderedKeys a b c ↔ k ∈ a3KeyBox a b c := by
  simpa only [a3GlobalOrderedKeys] using
    (Finset.mem_sort (s := a3KeyBox a b c) (r := a3KeyDescLE b c))

theorem a3GlobalOrderedKeys_length (a b c : ℕ) :
    (a3GlobalOrderedKeys a b c).length = (a3KeyBox a b c).card := by
  simpa only [a3GlobalOrderedKeys] using
    (Finset.length_sort (s := a3KeyBox a b c) (r := a3KeyDescLE b c))

theorem a3GlobalOrderedKeys_pairwise (a b c : ℕ) :
    (a3GlobalOrderedKeys a b c).Pairwise (a3KeyDescLE b c) := by
  simpa only [a3GlobalOrderedKeys] using
    (Finset.pairwise_sort (a3KeyBox a b c) (a3KeyDescLE b c))

noncomputable def a3KeyEnum (a b c : ℕ) :
    Fin ((a3KeyBox a b c).card) → A3RadicalKey := fun j =>
  (a3GlobalOrderedKeys a b c).get
    (Fin.cast (a3GlobalOrderedKeys_length a b c).symm j)

theorem a3KeyEnum_mem (a b c : ℕ)
    (j : Fin ((a3KeyBox a b c).card)) :
    a3KeyEnum a b c j ∈ a3KeyBox a b c := by
  apply (a3GlobalOrderedKeys_mem a b c _).mp
  simpa only [a3KeyEnum] using
    (List.get_mem (a3GlobalOrderedKeys a b c)
      (Fin.cast (a3GlobalOrderedKeys_length a b c).symm j))

theorem a3KeyEnum_cover (a b c : ℕ) (x : A3RadicalKey)
    (hx : x ∈ a3KeyBox a b c) :
    ∃ j : Fin ((a3KeyBox a b c).card), a3KeyEnum a b c j = x := by
  have hx' : x ∈ a3GlobalOrderedKeys a b c :=
    (a3GlobalOrderedKeys_mem a b c x).mpr hx
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx'
  refine ⟨Fin.cast (a3GlobalOrderedKeys_length a b c) j, ?_⟩
  simpa [a3KeyEnum] using hj

theorem a3KeyEnum_descending (a b c : ℕ)
    (i j : Fin ((a3KeyBox a b c).card)) (hij : i < j) :
    a3KeyLess b c (a3KeyEnum a b c j) (a3KeyEnum a b c i) := by
  let i' := Fin.cast (a3GlobalOrderedKeys_length a b c).symm i
  let j' := Fin.cast (a3GlobalOrderedKeys_length a b c).symm j
  have hlt : i' < j' := by simpa [i', j'] using hij
  have hrel := (List.pairwise_iff_get.mp
    (a3GlobalOrderedKeys_pairwise a b c)) i' j' hlt
  have hne : i' ≠ j' := ne_of_lt hlt
  have hnodup : (a3GlobalOrderedKeys a b c).Nodup := by
    change ((a3KeyBox a b c).sort (a3KeyDescLE b c)).Nodup
    exact Finset.sort_nodup (a3KeyBox a b c) (a3KeyDescLE b c)
  have hval : (a3GlobalOrderedKeys a b c).get i' ≠
      (a3GlobalOrderedKeys a b c).get j' := by
    intro heq
    exact hne (List.nodup_iff_injective_get.mp hnodup heq)
  rcases hrel with heq | hless
  · exact False.elim (hval heq)
  · exact hless

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3GlobalOrderedKeys_mem
#print axioms VOA.DeligneAudit.A3Sector.a3GlobalOrderedKeys_length
#print axioms VOA.DeligneAudit.A3Sector.a3GlobalOrderedKeys_pairwise
#print axioms VOA.DeligneAudit.A3Sector.a3KeyEnum_mem
#print axioms VOA.DeligneAudit.A3Sector.a3KeyEnum_cover
#print axioms VOA.DeligneAudit.A3Sector.a3KeyEnum_descending
