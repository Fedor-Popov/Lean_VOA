import VOA.DeligneAudit.D4LeviKSWordPresentation

/-! Explicit fixed-colour words for full Wick contractions. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion

/-- Every top contraction chooses Y positions and allocates the added
    current degree among exactly `k` Z positions. -/
noncomputable def topWords (k s : ℕ) (bases : List ℕ) :
    List (List (Fin 6 × ℕ)) :=
  (choices bases).flatMap fun p =>
    if p.2.length = k then
      (modeAllocations p.2 s).map fun zs =>
        (p.1.map fun r => ((4 : Fin 6), r)) ++
          (zs.map fun r => ((5 : Fin 6), r))
    else []

theorem choices_length_sum (bases : List ℕ)
    (p : List ℕ × List ℕ) (hp : p ∈ choices bases) :
    p.1.length + p.2.length = bases.length := by
  induction bases generalizing p with
  | nil =>
      simp [choices] at hp
      obtain rfl := hp
      rfl
  | cons x xs ih =>
      simp only [choices, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have hh := ih q hq
        simp only [Prod.fst, Prod.snd, List.length_cons] at *
        omega
      · have hh := ih q hq
        simp only [Prod.fst, Prod.snd, List.length_cons] at *
        omega

theorem modeAllocations_length (bases : List ℕ) (s : ℕ)
    (zs : List ℕ) (hz : zs ∈ modeAllocations bases s) :
    zs.length = bases.length := by
  induction bases generalizing s zs with
  | nil =>
      simp [modeAllocations] at hz
      rcases hz with ⟨rfl, rfl⟩
      rfl
  | cons x xs ih =>
      simp only [modeAllocations, List.mem_flatMap, List.mem_map] at hz
      obtain ⟨q, hq, ys, hys, rfl⟩ := hz
      simp [ih q.2 ys hys]

theorem topWords_colour_counts (k s : ℕ) (bases : List ℕ)
    (l : List (Fin 6 × ℕ)) (hl : l ∈ topWords k s bases) :
    ∃ p ∈ choices bases, ∃ zs ∈ modeAllocations p.2 s,
      p.2.length = k ∧
      l = (p.1.map fun r => ((4 : Fin 6), r)) ++
        (zs.map fun r => ((5 : Fin 6), r)) := by
  simp only [topWords, List.mem_flatMap] at hl
  obtain ⟨p, hp, hrest⟩ := hl
  split_ifs at hrest with hk
  · obtain ⟨zs, hzs, rfl⟩ := List.mem_map.mp hrest
    exact ⟨p, hp, zs, hzs, hk, rfl⟩
  · simp at hrest

/-- Every word in a full top contraction has the same colour list. -/
theorem topWords_colour_shape (k s : ℕ) (bases : List ℕ)
    (l : List (Fin 6 × ℕ)) (hl : l ∈ topWords k s bases) :
    l.map Prod.fst =
      List.replicate (bases.length - k) (4 : Fin 6) ++
        List.replicate k (5 : Fin 6) := by
  obtain ⟨p, hp, zs, hzs, hk, rfl⟩ := topWords_colour_counts k s bases l hl
  have hlen := choices_length_sum bases p hp
  have hzslen := modeAllocations_length p.2 s zs hzs
  have hp_len : p.1.length = bases.length - k := by omega
  have hz_len : zs.length = k := by omega
  simp only [List.map_append, List.map_map, Function.comp_def,
    Prod.fst, List.map_const']
  rw [hp_len, hz_len]

/-- The full Wick coefficient is a finite list of individual mode words. -/
theorem topSum_eq_allocated_words {A : Type*} [Ring A]
    (a b : ℕ → A) (k s : ℕ) (bases : List ℕ) :
    topSum a b k s bases =
      ((choices bases).map fun p =>
        if p.2.length = k then
          ((modeAllocations p.2 s).map fun zs =>
            aWord a p.1 * (zs.map b).prod).sum
        else 0).sum := by
  rw [topSum_eq_shiftedWordCoeff]
  congr 1
  apply List.map_congr_left
  intro p hp
  split_ifs <;> simp [shiftedWordCoeff_eq_allocations,
    List.sum_map_mul_left]

noncomputable def topWordOp {A : Type*} [Ring A]
    (a b : ℕ → A) (l : List (Fin 6 × ℕ)) : A :=
  (l.map fun p => if p.1 = 4 then a p.2 else b p.2).prod

theorem topWordOp_allocation {A : Type*} [Ring A]
    (a b : ℕ → A) (ys zs : List ℕ) :
    topWordOp a b ((ys.map fun r => ((4 : Fin 6), r)) ++
      (zs.map fun r => ((5 : Fin 6), r))) =
      aWord a ys * (zs.map b).prod := by
  simp [topWordOp, aWord, List.map_append, List.prod_append,
    List.map_map, Function.comp_def]

/-- The endomorphism-valued top contraction is exactly the sum over the
    explicit fixed-shape mode words. -/
theorem topSum_eq_topWords {A : Type*} [Ring A]
    (a b : ℕ → A) (k s : ℕ) (bases : List ℕ) :
    topSum a b k s bases =
      ((topWords k s bases).map (topWordOp a b)).sum := by
  rw [topSum_eq_allocated_words]
  simp only [topWords, List.flatMap_def, List.map_flatten,
    List.sum_flatten, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  split_ifs
  · simp only [List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro zs hzs
    exact (topWordOp_allocation a b p.1 zs).symm
  · rfl

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.topWords_colour_counts
#print axioms VOA.DeligneAudit.D4Levi.choices_length_sum
#print axioms VOA.DeligneAudit.D4Levi.modeAllocations_length
#print axioms VOA.DeligneAudit.D4Levi.topWords_colour_shape
#print axioms VOA.DeligneAudit.D4Levi.topSum_eq_allocated_words
#print axioms VOA.DeligneAudit.D4Levi.topWordOp_allocation
#print axioms VOA.DeligneAudit.D4Levi.topSum_eq_topWords
