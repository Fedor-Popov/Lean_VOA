import VOA.DeligneAudit.LeviTypeA2CertGradedLower

/-! Length and mode-degree conservation for positional Wick choices. -/

namespace VOA.DeligneAudit.LeviConversion

private theorem splitAt_perm_graded {ι : Type*} [DecidableEq ι]
    (l : List ι) (T : Finset ι) :
    List.Perm ((splitAt l T).1 ++ (splitAt l T).2) l := by
  induction l with
  | nil => simp [splitAt]
  | cons x xs ih =>
    by_cases hx : x ∈ T
    · simpa [splitAt, hx] using (List.perm_middle.trans (ih.cons x))
    · simpa [splitAt, hx] using (ih.cons x)

/-- Partitioning by positions preserves the total number of letters and
their mode sum, even when modes repeat. -/
theorem splitAt_mode_length_sum (l : List ℕ)
    (T : Finset (Fin l.length)) :
    let p := splitAt (List.finRange l.length) T
    (p.1.map l.get).length + (p.2.map l.get).length = l.length ∧
      (p.1.map l.get).sum + (p.2.map l.get).sum = l.sum := by
  let p := splitAt (List.finRange l.length) T
  have h := splitAt_perm_graded (List.finRange l.length) T
  have hmap : List.Perm (p.1.map l.get ++ p.2.map l.get) l := by
    simpa only [List.map_append, List.map_get_finRange] using h.map l.get
  constructor
  · simpa only [List.length_append] using hmap.length_eq
  · simpa only [List.sum_append] using hmap.sum_eq

end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.splitAt_mode_length_sum
