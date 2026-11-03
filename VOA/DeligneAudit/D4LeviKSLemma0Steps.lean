import VOA.DeligneAudit.D4LeviKSLemma0Perm

/-! Explicit replacement-word expansions for the two D4 Levi derivatives. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Replace one X by U' or one U by Y, preserving all other letters. -/
def threeWords (r : ℕ) : List (Fin 6 × ℕ) → List (List (Fin 6 × ℕ))
  | [] => []
  | (j, s) :: l =>
      (if j = 1 then [[(3, r + s)] ++ l]
       else if j = 2 then [[(4, r + s)] ++ l] else []) ++
        (threeWords r l).map (fun q => (j, s) :: q)

/-- Replace one X by U or one U' by Y. -/
def fourWords (r : ℕ) : List (Fin 6 × ℕ) → List (List (Fin 6 × ℕ))
  | [] => []
  | (j, s) :: l =>
      (if j = 1 then [[(2, r + s)] ++ l]
       else if j = 3 then [[(4, r + s)] ++ l] else []) ++
        (fourWords r l).map (fun q => (j, s) :: q)

/-- The total number of the two middle radical colours. -/
def cntUU (l : List (Fin 6 × ℕ)) : ℕ :=
  l.countP (fun p => p.1 = 2) + l.countP (fun p => p.1 = 3)

/-- The number of X letters with strictly positive current mode. -/
def posX (l : List (Fin 6 × ℕ)) : ℕ :=
  l.countP (fun p => p.1 = 1 ∧ 0 < p.2)

/-- The well-founded measure for the general U/U' elimination. -/
def lemmaZeroMeasure (k : RadicalKey) (l : List (Fin 6 × ℕ)) : ℕ :=
  cntUU l * (k.x + 1) + posX l

theorem posX_le_xCount (l : List (Fin 6 × ℕ)) :
    posX l ≤ l.countP (fun p => p.1 = 1) := by
  induction l with
  | nil => simp [posX]
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      by_cases hj : j = 1
      · subst j
        by_cases hs : 0 < s
        · simpa [posX, hs] using Nat.add_le_add_left ih 1
        · simpa [posX, hs] using Nat.le_trans ih (Nat.le_succ _)
      · simpa [posX, hj] using ih

theorem posX_le_keyX (k : RadicalKey) (l : List (Fin 6 × ℕ))
    (hk : wordKey l = k) : posX l ≤ k.x := by
  simpa [← hk, wordKey] using posX_le_xCount l

/-- Replacing a selected U' by a zero-mode X raises Levi height by two. -/
theorem xzero_higher_up (m : ℕ) (r : ℕ) (rest : List (Fin 6 × ℕ)) :
    keyLess m (wordKey ((3, r) :: rest)) (wordKey ((1, 0) :: rest)) := by
  left
  simp only [keyHeight, wordKey, List.countP_cons, List.map_cons, List.sum_cons]
  simp

/-- The same strictly higher source key for a selected U. -/
theorem xzero_higher_u (m : ℕ) (r : ℕ) (rest : List (Fin 6 × ℕ)) :
    keyLess m (wordKey ((2, r) :: rest)) (wordKey ((1, 0) :: rest)) := by
  left
  simp only [keyHeight, wordKey, List.countP_cons, List.map_cons, List.sum_cons]
  simp

theorem fThreeDerivative_eq_sum (r : ℕ) (l : List (Fin 6 × ℕ)) :
    fThreeDerivative ρ r l w =
      -((threeWords r l).map (radicalWord ρ w)).sum := by
  induction l with
  | nil => simp [fThreeDerivative, threeWords]
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      simp only [fThreeDerivative, threeWords, List.map_append, List.sum_append]
      have hmap :
          ρ.op (radicalColour j) s
            ((threeWords r l).map (radicalWord ρ w)).sum =
          ((threeWords r l).map fun q =>
            radicalWord ρ w ((j, s) :: q)).sum := by
        simpa only [List.map_map, Function.comp_def, radicalWord,
          List.map_cons, wordOp] using
          (map_list_sum (ρ.op (radicalColour j) s)
            ((threeWords r l).map (radicalWord ρ w)))
      rw [ih, map_neg, hmap]
      by_cases hj1 : j = 1
      · subst j
        have hh : fThreeLetter ρ r (1, s)
            (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) w) =
            -radicalWord ρ w ((3, r + s) :: l) := by
          simp [fThreeLetter, radicalColour, radicalWord, wordOp]
          rfl
        rw [hh]
        simp only [if_true, List.singleton_append, List.map_singleton, List.sum_singleton,
          List.map_map, Function.comp_def]
        abel_nf
      · by_cases hj2 : j = 2
        · subst j
          have hh : fThreeLetter ρ r (2, s)
              (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) w) =
              -radicalWord ρ w ((4, r + s) :: l) := by
            simp [fThreeLetter, radicalColour, radicalWord, wordOp]
            rfl
          rw [hh]
          simp only [hj1, if_false, if_true, List.singleton_append, List.map_singleton,
            List.sum_singleton,
            List.map_map, Function.comp_def]
          abel_nf
        · simp [fThreeLetter, hj1, hj2, List.map_map, Function.comp_def]

theorem fFourDerivative_eq_sum (r : ℕ) (l : List (Fin 6 × ℕ)) :
    fFourDerivative ρ r l w =
      -((fourWords r l).map (radicalWord ρ w)).sum := by
  induction l with
  | nil => simp [fFourDerivative, fourWords]
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      simp only [fFourDerivative, fourWords, List.map_append, List.sum_append]
      have hmap :
          ρ.op (radicalColour j) s
            ((fourWords r l).map (radicalWord ρ w)).sum =
          ((fourWords r l).map fun q =>
            radicalWord ρ w ((j, s) :: q)).sum := by
        simpa only [List.map_map, Function.comp_def, radicalWord,
          List.map_cons, wordOp] using
          (map_list_sum (ρ.op (radicalColour j) s)
            ((fourWords r l).map (radicalWord ρ w)))
      rw [ih, map_neg, hmap]
      by_cases hj1 : j = 1
      · subst j
        have hh : fFourLetter ρ r (1, s)
            (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) w) =
            -radicalWord ρ w ((2, r + s) :: l) := by
          simp [fFourLetter, radicalColour, radicalWord, wordOp]
          rfl
        rw [hh]
        simp only [if_true, List.singleton_append, List.map_singleton, List.sum_singleton,
          List.map_map, Function.comp_def]
        abel_nf
      · by_cases hj3 : j = 3
        · subst j
          have hh : fFourLetter ρ r (3, s)
              (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) w) =
              -radicalWord ρ w ((4, r + s) :: l) := by
            simp [fFourLetter, radicalColour, radicalWord, wordOp]
            rfl
          rw [hh]
          simp only [hj1, if_false, if_true, List.singleton_append, List.map_singleton,
            List.sum_singleton,
            List.map_map, Function.comp_def]
          abel_nf
        · simp [fFourLetter, hj1, hj3, List.map_map, Function.comp_def]

/-- The f₃ relation after moving a selected U' letter to the front. -/
theorem fThree_selected_up_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (l rest : List (Fin 6 × ℕ)) (r : ℕ)
    (hp : l.Perm ((3, r) :: rest)) (hk : wordKey l = k) :
    -radicalWord ρ w l +
      ρ.op (22 : Fin 28) 0 (fThreeDerivative ρ r rest w) ∈
        higherOrbit ρ w m k := by
  have hkey : wordKey ((3, r) :: rest) = k :=
    (wordKey_perm hp).symm.trans hk
  have hless : keyLess m k (wordKey ((1, 0) :: rest)) := by
    rw [← hkey]
    exact xzero_higher_up m r rest
  have hf := fThree_xzero_higher ρ w m h k r rest hless
  change -radicalWord ρ w ((3, r) :: rest) +
    ρ.op (22 : Fin 28) 0 (fThreeDerivative ρ r rest w) ∈
      higherOrbit ρ w m k at hf
  rwa [← radicalWord_perm ρ w hp] at hf

/-- The f₄ relation after moving a selected U letter to the front. -/
theorem fFour_selected_u_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (l rest : List (Fin 6 × ℕ)) (r : ℕ)
    (hp : l.Perm ((2, r) :: rest)) (hk : wordKey l = k) :
    -radicalWord ρ w l +
      ρ.op (22 : Fin 28) 0 (fFourDerivative ρ r rest w) ∈
        higherOrbit ρ w m k := by
  have hkey : wordKey ((2, r) :: rest) = k :=
    (wordKey_perm hp).symm.trans hk
  have hless : keyLess m k (wordKey ((1, 0) :: rest)) := by
    rw [← hkey]
    exact xzero_higher_u m r rest
  have hf := fFour_xzero_higher ρ w m h k r rest hless
  change -radicalWord ρ w ((2, r) :: rest) +
    ρ.op (22 : Fin 28) 0 (fFourDerivative ρ r rest w) ∈
      higherOrbit ρ w m k at hf
  rwa [← radicalWord_perm ρ w hp] at hf

/-- An X-to-U' derivative term stays at the selected U' key. -/
theorem three_x_replacement_key (r s : ℕ)
    (pre post : List (Fin 6 × ℕ)) :
    wordKey ((1, 0) :: pre ++ (3, r + s) :: post) =
      wordKey ((3, r) :: pre ++ (1, s) :: post) := by
  simp [wordKey, RadicalKey.mk.injEq, List.countP_append,
    List.map_append, List.sum_append]
  omega

/-- A positive-mode X derivative strictly lowers the prescribed measure. -/
theorem three_x_replacement_measure (k : RadicalKey) (r s : ℕ)
    (pre post : List (Fin 6 × ℕ)) (hs : 0 < s) :
    lemmaZeroMeasure k ((1, 0) :: pre ++ (3, r + s) :: post) <
      lemmaZeroMeasure k ((3, r) :: pre ++ (1, s) :: post) := by
  simp [lemmaZeroMeasure, cntUU, posX, List.countP_append, hs]
  nlinarith

/-- A U-to-Y derivative term has a strictly higher key. -/
theorem three_u_replacement_higher (m r s : ℕ)
    (pre post : List (Fin 6 × ℕ)) :
    keyLess m (wordKey ((3, r) :: pre ++ (2, s) :: post))
      (wordKey ((1, 0) :: pre ++ (4, r + s) :: post)) := by
  simp [keyLess, keyHeight, wordKey, List.countP_append,
    List.map_append, List.sum_append]
  omega

/-- An X-to-U derivative term stays at the selected U key. -/
theorem four_x_replacement_key (r s : ℕ)
    (pre post : List (Fin 6 × ℕ)) :
    wordKey ((1, 0) :: pre ++ (2, r + s) :: post) =
      wordKey ((2, r) :: pre ++ (1, s) :: post) := by
  simp [wordKey, RadicalKey.mk.injEq, List.countP_append,
    List.map_append, List.sum_append]
  omega

/-- A positive-mode X derivative also lowers the f₄ measure. -/
theorem four_x_replacement_measure (k : RadicalKey) (r s : ℕ)
    (pre post : List (Fin 6 × ℕ)) (hs : 0 < s) :
    lemmaZeroMeasure k ((1, 0) :: pre ++ (2, r + s) :: post) <
      lemmaZeroMeasure k ((2, r) :: pre ++ (1, s) :: post) := by
  simp [lemmaZeroMeasure, cntUU, posX, List.countP_append, hs]
  nlinarith

/-- A U'-to-Y derivative term has a strictly higher key. -/
theorem four_up_replacement_higher (m r s : ℕ)
    (pre post : List (Fin 6 × ℕ)) :
    keyLess m (wordKey ((2, r) :: pre ++ (3, s) :: post))
      (wordKey ((1, 0) :: pre ++ (4, r + s) :: post)) := by
  simp [keyLess, keyHeight, wordKey, List.countP_append,
    List.map_append, List.sum_append]
  omega

/-- A zero-mode X derivative gives the original selected U' word. -/
theorem three_xzero_replacement_word (r : ℕ)
    (pre post : List (Fin 6 × ℕ)) :
    radicalWord ρ w ((1, 0) :: pre ++ (3, r) :: post) =
      radicalWord ρ w ((3, r) :: pre ++ (1, 0) :: post) := by
  apply radicalWord_perm ρ w
  apply List.perm_iff_count.mpr
  intro p
  simp only [List.count_cons, List.count_append]
  omega

/-- The same zero-mode permutation for a selected U word. -/
theorem four_xzero_replacement_word (r : ℕ)
    (pre post : List (Fin 6 × ℕ)) :
    radicalWord ρ w ((1, 0) :: pre ++ (2, r) :: post) =
      radicalWord ρ w ((2, r) :: pre ++ (1, 0) :: post) := by
  apply radicalWord_perm ρ w
  apply List.perm_iff_count.mpr
  intro p
  simp only [List.count_cons, List.count_append]
  omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fThreeDerivative_eq_sum
#print axioms VOA.DeligneAudit.D4Levi.fFourDerivative_eq_sum
#print axioms VOA.DeligneAudit.D4Levi.posX_le_xCount
#print axioms VOA.DeligneAudit.D4Levi.posX_le_keyX
#print axioms VOA.DeligneAudit.D4Levi.xzero_higher_up
#print axioms VOA.DeligneAudit.D4Levi.xzero_higher_u
#print axioms VOA.DeligneAudit.D4Levi.fThree_selected_up_higher
#print axioms VOA.DeligneAudit.D4Levi.fFour_selected_u_higher
#print axioms VOA.DeligneAudit.D4Levi.three_x_replacement_key
#print axioms VOA.DeligneAudit.D4Levi.three_x_replacement_measure
#print axioms VOA.DeligneAudit.D4Levi.three_u_replacement_higher
#print axioms VOA.DeligneAudit.D4Levi.four_x_replacement_key
#print axioms VOA.DeligneAudit.D4Levi.four_x_replacement_measure
#print axioms VOA.DeligneAudit.D4Levi.four_up_replacement_higher
#print axioms VOA.DeligneAudit.D4Levi.three_xzero_replacement_word
#print axioms VOA.DeligneAudit.D4Levi.four_xzero_replacement_word
