import VOA.DeligneAudit.D4LeviKSRzRawMonomial

/-! Canonical block order for the labelled Rz source word. -/

namespace VOA.DeligneAudit.D4Levi

theorem rz_univ_sum_perm {A B : Type*} [Fintype A] [Fintype B]
    :
    (Finset.univ.toList : List (A ⊕ B)).Perm
      ((Finset.univ.toList : List A).map Sum.inl ++
        (Finset.univ.toList : List B).map Sum.inr) := by
  classical
  have hn : ((Finset.univ.toList : List A).map Sum.inl ++
      (Finset.univ.toList : List B).map Sum.inr).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨(Finset.nodup_toList _).map (by
        intro x y h; exact Sum.inl.inj h),
      (Finset.nodup_toList _).map (by
        intro x y h; exact Sum.inr.inj h), ?_⟩
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, h⟩ := List.mem_map.mp hy
    cases h
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hn).2
  intro t
  rcases t with a | b <;> simp

theorem rz_univ_fin_add_perm (k l : ℕ) :
    (Finset.univ.toList : List (Fin (k + l))).Perm
      ((Finset.univ.toList : List (Fin k)).map (Fin.castAdd l) ++
        (Finset.univ.toList : List (Fin l)).map (Fin.natAdd k)) := by
  classical
  have hn : ((Finset.univ.toList : List (Fin k)).map (Fin.castAdd l) ++
      (Finset.univ.toList : List (Fin l)).map (Fin.natAdd k)).Nodup := by
    have hperm := rz_univ_sum_perm (A := Fin k) (B := Fin l)
    have hmap : ((Finset.univ.toList : List (Fin k ⊕ Fin l)).map
        finSumFinEquiv).Nodup :=
      (Finset.nodup_toList _).map finSumFinEquiv.injective
    have hn' := (hperm.map finSumFinEquiv).nodup_iff.mp hmap
    simpa [List.map_append, List.map_map, finSumFinEquiv] using hn'
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hn).2
  intro t
  constructor
  · intro _
    rcases finSumFinEquiv.surjective t with ⟨q, rfl⟩
    rcases q with i | j <;> simp [finSumFinEquiv]
  · simp

theorem rz_source_univ_perm (a b k l : ℕ) :
    (Finset.univ.toList : List (PairSource a b (k + l))).Perm
      ((Finset.univ.toList : List (Fin b ⊕ Fin a)).map Sum.inl ++
        (Finset.univ.toList : List (Fin b)).map (Sum.inr ∘ Sum.inl) ++
        (Finset.univ.toList : List (Fin k)).map
          (Sum.inr ∘ Sum.inr ∘ Fin.castAdd l) ++
        (Finset.univ.toList : List (Fin l)).map
          (Sum.inr ∘ Sum.inr ∘ Fin.natAdd k)) := by
  classical
  have h1 := rz_univ_sum_perm (A := Fin b ⊕ Fin a)
    (B := Fin b ⊕ Fin (k + l))
  have h2 := rz_univ_sum_perm (A := Fin b) (B := Fin (k + l))
  have h3 := rz_univ_fin_add_perm k l
  have h12 :
      (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map Sum.inl) ++
        (Finset.univ.toList : List (Fin b ⊕ Fin (k + l))).map Sum.inr).Perm
      (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map Sum.inl) ++
        (Finset.univ.toList : List (Fin b)).map (Sum.inr ∘ Sum.inl) ++
        (Finset.univ.toList : List (Fin (k + l))).map
          (Sum.inr ∘ Sum.inr)) := by
    simpa [List.map_append, List.map_map, Function.comp_def,
      List.append_assoc] using (h2.map Sum.inr).append_left
        ((Finset.univ.toList : List (Fin b ⊕ Fin a)).map Sum.inl)
  have h23 :
      (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map Sum.inl) ++
        (Finset.univ.toList : List (Fin b)).map (Sum.inr ∘ Sum.inl) ++
        (Finset.univ.toList : List (Fin (k + l))).map
          (Sum.inr ∘ Sum.inr)).Perm
      ((Finset.univ.toList : List (Fin b ⊕ Fin a)).map Sum.inl ++
        (Finset.univ.toList : List (Fin b)).map (Sum.inr ∘ Sum.inl) ++
        (Finset.univ.toList : List (Fin k)).map
          (Sum.inr ∘ Sum.inr ∘ Fin.castAdd l) ++
        (Finset.univ.toList : List (Fin l)).map
          (Sum.inr ∘ Sum.inr ∘ Fin.natAdd k)) := by
    simpa only [List.map_append, List.map_map, Function.comp_def,
      ← List.append_assoc] using (h3.map (Sum.inr ∘ Sum.inr)).append_left
        (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map Sum.inl) ++
          (Finset.univ.toList : List (Fin b)).map (Sum.inr ∘ Sum.inl))
  exact h1.trans (h12.trans h23)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_univ_sum_perm
#print axioms VOA.DeligneAudit.D4Levi.rz_univ_fin_add_perm
#print axioms VOA.DeligneAudit.D4Levi.rz_source_univ_perm
