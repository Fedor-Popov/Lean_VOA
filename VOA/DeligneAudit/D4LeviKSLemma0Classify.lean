import VOA.DeligneAudit.D4LeviKSLemma0Steps

/-! Every derivative summand replaces exactly one radical letter. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl

/-- The two kinds of summand in the f₃ derivative. -/
theorem threeWords_mem_cases (r : ℕ) (l q : List (Fin 6 × ℕ))
    (hq : q ∈ threeWords r l) :
    (∃ pre post s, l = pre ++ (1, s) :: post ∧
      q = pre ++ (3, r + s) :: post) ∨
    (∃ pre post s, l = pre ++ (2, s) :: post ∧
      q = pre ++ (4, r + s) :: post) := by
  induction l generalizing q with
  | nil => simp [threeWords] at hq
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      simp only [threeWords, List.mem_append, List.mem_map] at hq
      rcases hq with hhead | ⟨q', hq', rfl⟩
      · by_cases hj1 : j = 1
        · subst j
          simp at hhead
          subst q
          exact Or.inl ⟨[], l, s, by simp, by simp⟩
        · by_cases hj2 : j = 2
          · subst j
            simp [hj1] at hhead
            subst q
            exact Or.inr ⟨[], l, s, by simp, by simp⟩
          · simp [hj1, hj2] at hhead
      · rcases ih q' hq' with ⟨pre, post, t, hl, hq'⟩ |
          ⟨pre, post, t, hl, hq'⟩
        · left
          exact ⟨(j, s) :: pre, post, t, by simp [hl], by simp [hq']⟩
        · right
          exact ⟨(j, s) :: pre, post, t, by simp [hl], by simp [hq']⟩
/-- The two kinds of summand in the f₄ derivative. -/
theorem fourWords_mem_cases (r : ℕ) (l q : List (Fin 6 × ℕ))
    (hq : q ∈ fourWords r l) :
    (∃ pre post s, l = pre ++ (1, s) :: post ∧
      q = pre ++ (2, r + s) :: post) ∨
    (∃ pre post s, l = pre ++ (3, s) :: post ∧
      q = pre ++ (4, r + s) :: post) := by
  induction l generalizing q with
  | nil => simp [fourWords] at hq
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      simp only [fourWords, List.mem_append, List.mem_map] at hq
      rcases hq with hhead | ⟨q', hq', rfl⟩
      · by_cases hj1 : j = 1
        · subst j
          simp at hhead
          subst q
          exact Or.inl ⟨[], l, s, by simp, by simp⟩
        · by_cases hj3 : j = 3
          · subst j
            simp [hj1] at hhead
            subst q
            exact Or.inr ⟨[], l, s, by simp, by simp⟩
          · simp [hj1, hj3] at hhead
      · rcases ih q' hq' with ⟨pre, post, t, hl, hq'⟩ |
          ⟨pre, post, t, hl, hq'⟩
        · left
          exact ⟨(j, s) :: pre, post, t, by simp [hl], by simp [hq']⟩
        · right
          exact ⟨(j, s) :: pre, post, t, by simp [hl], by simp [hq']⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.DeligneAudit.DeligneSector.D4.fD4 V) (w : V)

/-- Each f₃ summand is smaller, the original word, or strictly higher. -/
theorem three_term_trichotomy (m r : ℕ) (rest q : List (Fin 6 × ℕ))
    (hq : q ∈ threeWords r rest) :
    (wordKey ((1, 0) :: q) = wordKey ((3, r) :: rest) ∧
      lemmaZeroMeasure (wordKey ((3, r) :: rest)) ((1, 0) :: q) <
        lemmaZeroMeasure (wordKey ((3, r) :: rest)) ((3, r) :: rest)) ∨
    radicalWord ρ w ((1, 0) :: q) = radicalWord ρ w ((3, r) :: rest) ∨
    keyLess m (wordKey ((3, r) :: rest)) (wordKey ((1, 0) :: q)) := by
  rcases threeWords_mem_cases r rest q hq with
    ⟨pre, post, s, hr, hq'⟩ | ⟨pre, post, s, hr, hq'⟩
  · subst rest
    subst q
    by_cases hs : s = 0
    · subst s
      exact Or.inr (Or.inl (by simpa using
        three_xzero_replacement_word ρ w r pre post))
    · left
      exact ⟨three_x_replacement_key r s pre post,
        three_x_replacement_measure _ r s pre post (Nat.pos_of_ne_zero hs)⟩
  · subst rest
    subst q
    exact Or.inr (Or.inr (three_u_replacement_higher m r s pre post))

/-- The f₄ companion classifies every replacement summand. -/
theorem four_term_trichotomy (m r : ℕ) (rest q : List (Fin 6 × ℕ))
    (hq : q ∈ fourWords r rest) :
    (wordKey ((1, 0) :: q) = wordKey ((2, r) :: rest) ∧
      lemmaZeroMeasure (wordKey ((2, r) :: rest)) ((1, 0) :: q) <
        lemmaZeroMeasure (wordKey ((2, r) :: rest)) ((2, r) :: rest)) ∨
    radicalWord ρ w ((1, 0) :: q) = radicalWord ρ w ((2, r) :: rest) ∨
    keyLess m (wordKey ((2, r) :: rest)) (wordKey ((1, 0) :: q)) := by
  rcases fourWords_mem_cases r rest q hq with
    ⟨pre, post, s, hr, hq'⟩ | ⟨pre, post, s, hr, hq'⟩
  · subst rest
    subst q
    by_cases hs : s = 0
    · subst s
      exact Or.inr (Or.inl (by simpa using
        four_xzero_replacement_word ρ w r pre post))
    · left
      exact ⟨four_x_replacement_key r s pre post,
        four_x_replacement_measure _ r s pre post (Nat.pos_of_ne_zero hs)⟩
  · subst rest
    subst q
    exact Or.inr (Or.inr (four_up_replacement_higher m r s pre post))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.threeWords_mem_cases
#print axioms VOA.DeligneAudit.D4Levi.fourWords_mem_cases
#print axioms VOA.DeligneAudit.D4Levi.three_term_trichotomy
#print axioms VOA.DeligneAudit.D4Levi.four_term_trichotomy
