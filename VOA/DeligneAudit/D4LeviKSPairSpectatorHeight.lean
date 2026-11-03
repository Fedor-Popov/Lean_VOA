import VOA.DeligneAudit.D4LeviKSPairSpectatorSource

/-! Height bookkeeping for every path in the f₃ conversion tree. -/

namespace VOA.DeligneAudit.D4Levi

/-- Every nonzero f₃ word conversion lowers Levi height by exactly two. -/
theorem threeWords_height (m r : ℕ)
    {l q : List (Fin 6 × ℕ)} (hq : q ∈ threeWords r l) :
    keyHeight m (wordKey q) + 2 = keyHeight m (wordKey l) := by
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
          conv_lhs => rw [keyHeight_cons]
          conv_rhs => rw [keyHeight_cons]
          norm_num [keyHeight, wordKey]
        · by_cases hj2 : j = 2
          · subst j
            simp [hj1] at hhead
            subst q
            conv_lhs => rw [keyHeight_cons]
            conv_rhs => rw [keyHeight_cons]
            norm_num [keyHeight, wordKey]
          · simp [hj1, hj2] at hhead
      · conv_lhs => rw [keyHeight_cons]
        conv_rhs => rw [keyHeight_cons]
        have ht := ih hq'
        omega

/-- After `n` conversions, every branch has height lower by `2n`. -/
theorem threeWordsIter_height (m : ℕ) (rs : List ℕ)
    {l q : List (Fin 6 × ℕ)} (hq : q ∈ threeWordsIter rs l) :
    keyHeight m (wordKey q) + 2 * rs.length =
      keyHeight m (wordKey l) := by
  induction rs generalizing l q with
  | nil =>
      simp [threeWordsIter] at hq
      subst q
      simp
  | cons r rs ih =>
      simp only [threeWordsIter, List.mem_flatMap] at hq
      rcases hq with ⟨u, hu, hqu⟩
      have hstep := threeWords_height m r hu
      have htail := ih hqu
      simp only [List.length_cons]
      omega

/-- The initial XZ/U word has exactly `2b` more height than the final
    symmetric XY key. -/
theorem pairXZ_uZero_height (m a b c deg : ℕ)
    (d : PairXZ a b c →₀ ℕ) :
    keyHeight m (wordKey
      (shapedModes (pairXZRecolourShape a b c 0)
        Finset.univ.toList d ++ uZeroWord b)) =
      keyHeight m (pairFinalKey a b c deg) + 2 * b := by
  simp only [keyHeight, pairFinalKey, wordKey, List.countP_append]
  rw [pairXZShape_zero_x_count, pairXZShape_zero_y_count,
    pairXZShape_zero_z_count, pairXZShape_zero_e_count]
  simp [uZeroWord, List.countP_replicate]
  omega

/-- Any branch with fewer than `b` total conversions remains strictly
    above the final key. -/
theorem pairXZ_uZero_partial_higher (m a b c deg : ℕ)
    (d : PairXZ a b c →₀ ℕ) (rs : List ℕ)
    (hn : rs.length < b) {q : List (Fin 6 × ℕ)}
    (hq : q ∈ threeWordsIter rs
      (shapedModes (pairXZRecolourShape a b c 0)
        Finset.univ.toList d ++ uZeroWord b)) :
    keyLess m (pairFinalKey a b c deg) (wordKey q) := by
  left
  have hconv := threeWordsIter_height m rs hq
  have hsource := pairXZ_uZero_height m a b c deg d
  omega

theorem pairKeyHeight_append (m : ℕ)
    (l q : List (Fin 6 × ℕ)) :
    keyHeight m (wordKey (l ++ q)) =
      keyHeight m (wordKey l) + keyHeight 0 (wordKey q) := by
  simp [keyHeight, wordKey, List.countP_append]
  ring

/-- Even when the f₃ derivatives are split between the XZ operator and
    the U spectator, every term before the final transfer is a higher key. -/
theorem pairXZ_uZero_split_higher (m a b c deg : ℕ)
    (d : PairXZ a b c →₀ ℕ) (xs us : List ℕ)
    (hn : xs.length + us.length < b)
    {qx qu : List (Fin 6 × ℕ)}
    (hx : qx ∈ threeWordsIter xs
      (shapedModes (pairXZRecolourShape a b c 0)
        Finset.univ.toList d))
    (hu : qu ∈ threeWordsIter us (uZeroWord b)) :
    keyLess m (pairFinalKey a b c deg) (wordKey (qx ++ qu)) := by
  left
  have hxa := threeWordsIter_height m xs hx
  have hua := threeWordsIter_height 0 us hu
  have hbase := pairXZ_uZero_height m a b c deg d
  rw [pairKeyHeight_append] at hbase ⊢
  have huZero : keyHeight 0 (wordKey (uZeroWord b)) = 0 := by
    simp [keyHeight, wordKey, uZeroWord, List.countP_replicate]
  rw [huZero] at hbase
  omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.threeWords_height
#print axioms VOA.DeligneAudit.D4Levi.threeWordsIter_height
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_uZero_height
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_uZero_partial_higher
#print axioms VOA.DeligneAudit.D4Levi.pairKeyHeight_append
#print axioms VOA.DeligneAudit.D4Levi.pairXZ_uZero_split_higher
