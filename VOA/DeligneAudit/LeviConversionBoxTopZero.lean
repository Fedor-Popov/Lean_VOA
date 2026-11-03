import VOA.DeligneAudit.LeviConversionBoxTopSum

/-! Normalize the uncontracted `a` word for an all-zero positional choice. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

private theorem splitAt_perm {ι : Type*} [DecidableEq ι]
    (l : List ι) (T : Finset ι) :
    List.Perm ((splitAt l T).1 ++ (splitAt l T).2) l := by
  induction l with
  | nil => simp [splitAt]
  | cons x xs ih =>
    by_cases hx : x ∈ T
    · simpa [splitAt, hx] using (List.perm_middle.trans (ih.cons x))
    · simpa [splitAt, hx] using (ih.cons x)

private theorem pairwise_a {A : Type*} [Ring A] (a : ℕ → A)
    (haa : ∀ i j, a i * a j = a j * a i) (l : List ℕ) :
    (l.map a).Pairwise Commute := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.pairwise_cons]
    constructor
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      exact (commute_iff_eq _ _).2 (haa x t)
    · exact ih

/-- All-zero contractions leave precisely the original `a` multiset.
The order can be normalized because the `a` modes commute pairwise. -/
theorem selected_aWord_zero {A : Type*} [Ring A] (a : ℕ → A)
    (haa : ∀ i j, a i * a j = a j * a i)
    (xs : List ℕ) (k : ℕ)
    (T : Finset (Fin (xs ++ List.replicate k 0).length))
    (hT : T ∈ (Finset.univ : Finset (Fin (xs ++ List.replicate k 0).length)).powersetCard k)
    (hzero : T ⊆ zeroPositions
      (fun i : Fin (xs ++ List.replicate k 0).length =>
        (xs ++ List.replicate k 0).get i)) :
    aWord a ((splitAt (List.finRange (xs ++ List.replicate k 0).length) T).1.map
      (xs ++ List.replicate k 0).get) = aWord a xs := by
  let L := xs ++ List.replicate k 0
  let p := splitAt (List.finRange L.length) T
  have hpos : List.Perm (p.1 ++ p.2) (List.finRange L.length) :=
    splitAt_perm (List.finRange L.length) T
  have hmap : List.Perm (p.1.map L.get ++ p.2.map L.get) L := by
    simpa only [List.map_append, List.map_get_finRange] using hpos.map L.get
  have hselected : p.2.map L.get = List.replicate k 0 :=
    selected_modes_zero L k T hT hzero
  have hperm : List.Perm (p.1.map L.get) xs :=
    (List.perm_append_right_iff (List.replicate k 0)).mp (by
      simpa [hselected, L] using hmap)
  have hp := (hperm.map a).prod_eq' (pairwise_a a haa (p.1.map L.get))
  exact hp

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.selected_aWord_zero
