import VOA.DeligneAudit.D4LeviGlobalBox

/-! A descending enumeration of the all-depth D4 radical key box. -/

namespace VOA.DeligneAudit.D4Levi

def globalKeyBox (m : ℕ) : Finset RadicalKey :=
  keyBox (6 * m) (2 * m * (6 * m))

noncomputable def globalOrderedKeys (m : ℕ) : List RadicalKey :=
  orderedKeys m (6 * m) (2 * m * (6 * m))

theorem globalOrderedKeys_mem (m : ℕ) (k : RadicalKey) :
    k ∈ globalOrderedKeys m ↔ k ∈ globalKeyBox m := by
  exact mem_orderedKeys m (6 * m) (2 * m * (6 * m)) k

theorem globalOrderedKeys_length (m : ℕ) :
    (globalOrderedKeys m).length = (globalKeyBox m).card := by
  simpa only [globalOrderedKeys, globalKeyBox, orderedKeys] using
    (Finset.length_sort (s := keyBox (6 * m) (2 * m * (6 * m)))
      (r := keyDescLE m))

theorem globalOrderedKeys_pairwise (m : ℕ) :
    (globalOrderedKeys m).Pairwise (keyDescLE m) := by
  exact pairwise_orderedKeys m (6 * m) (2 * m * (6 * m))

noncomputable def keyEnum (m : ℕ) :
    Fin (globalKeyBox m).card → RadicalKey := fun j =>
  (globalOrderedKeys m).get (Fin.cast (globalOrderedKeys_length m).symm j)

theorem keyEnum_mem (m : ℕ) (j : Fin (globalKeyBox m).card) :
    keyEnum m j ∈ globalKeyBox m := by
  apply (globalOrderedKeys_mem m _).mp
  simpa only [keyEnum] using
    (List.get_mem (globalOrderedKeys m)
      (Fin.cast (globalOrderedKeys_length m).symm j))

theorem keyEnum_cover (m : ℕ) (k : RadicalKey)
    (hk : k ∈ globalKeyBox m) :
    ∃ j : Fin (globalKeyBox m).card, keyEnum m j = k := by
  have hk' : k ∈ globalOrderedKeys m :=
    (globalOrderedKeys_mem m k).mpr hk
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hk'
  refine ⟨Fin.cast (globalOrderedKeys_length m) j, ?_⟩
  simpa [keyEnum] using hj

theorem keyEnum_descending (m : ℕ)
    (i j : Fin (globalKeyBox m).card) (hij : i < j) :
    keyLess m (keyEnum m j) (keyEnum m i) := by
  let i' := Fin.cast (globalOrderedKeys_length m).symm i
  let j' := Fin.cast (globalOrderedKeys_length m).symm j
  have hlt : i' < j' := by simpa [i', j'] using hij
  have hrel := (List.pairwise_iff_get.mp (globalOrderedKeys_pairwise m)) i' j' hlt
  have hne : i' ≠ j' := ne_of_lt hlt
  have hnodup : (globalOrderedKeys m).Nodup := by
    change ((globalKeyBox m).sort (keyDescLE m)).Nodup
    exact Finset.sort_nodup (globalKeyBox m) (keyDescLE m)
  have hval : (globalOrderedKeys m).get i' ≠
      (globalOrderedKeys m).get j' := by
    intro heq
    exact hne (List.nodup_iff_injective_get.mp hnodup heq)
  rcases hrel with heq | hless
  · exact False.elim (hval heq)
  · exact hless

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.globalOrderedKeys_mem
#print axioms VOA.DeligneAudit.D4Levi.globalOrderedKeys_length
#print axioms VOA.DeligneAudit.D4Levi.keyEnum_cover
#print axioms VOA.DeligneAudit.D4Levi.keyEnum_descending
