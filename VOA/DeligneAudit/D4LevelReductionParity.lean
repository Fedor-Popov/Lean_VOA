import VOA.DeligneAudit.D4LevelReductionEmpty
import VOA.DeligneAudit.D4LeviKSLemma0StepProof

/-! Elimination of odd Levi levels by the two outer lowering currents. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The finite key box contains every nonzero orbit of a saturated module. -/
theorem keyOrbit_le_levelFiltration_of_sat (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ) (k : RadicalKey)
    (hκ : keyAlphaGrade m k = κ) (hp : p ≤ keyLeviLevel m k) :
    keyOrbit ρ w k ≤ levelFiltration ρ w m κ p := by
  by_cases hk : keyLayer ρ w k = ⊥
  · rw [keyOrbit_eq_bot_of_keyLayer_bot ρ w k hk]
    exact bot_le
  · exact keyOrbit_le_levelFiltration ρ w m κ p k
      (keyBox_contains_nonzero_global ρ w m h k hk) hκ hp

/-- Counting middle letters and positive-mode X letters terminates polarization. -/
def middleLetterMeasure (l : List (Fin 6 × ℕ)) : ℕ := cntUU l + posX l

theorem middleLetterMeasure_perm {l q : List (Fin 6 × ℕ)} (h : l.Perm q) :
    middleLetterMeasure l = middleLetterMeasure q := by
  simp [middleLetterMeasure, cntUU, posX, h.countP_eq]

private theorem sum_mem_mod_copies (N : Submodule ℂ V) (v : V) (L : List V)
    (h : ∀ x ∈ L, x ∈ N ∨ x = v) :
    ∃ n : ℕ, L.sum - (n : ℂ) • v ∈ N := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
      obtain ⟨n, hn⟩ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      rcases h x (by simp) with hx | hx
      · refine ⟨n, ?_⟩
        convert N.add_mem hx hn using 1
        simp only [List.sum_cons]
        abel
      · subst x
        refine ⟨n + 1, ?_⟩
        convert hn using 1
        push_cast
        simp only [add_smul, one_smul, List.sum_cons]
        abel

private theorem mem_of_negative_sum_relation (N : Submodule ℂ V) (v s : V)
    (hrel : -v - s ∈ N) (n : ℕ) (hs : s - (n : ℂ) • v ∈ N) : v ∈ N := by
  have hscaled : -((n + 1 : ℕ) : ℂ) • v ∈ N := by
    convert N.add_mem hrel hs using 1
    push_cast
    simp only [add_smul, one_smul, neg_smul]
    abel
  have hne : (-((n + 1 : ℕ) : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
  have hi := N.smul_mem (-((n + 1 : ℕ) : ℂ))⁻¹ hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using hi

/-- Derivative summands preserve the level and either decrease the measure or repeat the word. -/
theorem outerThree_replacement_cases (m r : ℕ) (rest q : List (Fin 6 × ℕ))
    (hq : q ∈ threeWords r rest) :
    (keyAlphaGrade m (wordKey ((1, 0) :: q)) =
        keyAlphaGrade m (wordKey ((3, r) :: rest)) ∧
      keyLeviLevel m (wordKey ((1, 0) :: q)) =
        keyLeviLevel m (wordKey ((3, r) :: rest)) ∧
      middleLetterMeasure ((1, 0) :: q) < middleLetterMeasure ((3, r) :: rest)) ∨
    radicalWord ρ w ((1, 0) :: q) = radicalWord ρ w ((3, r) :: rest) := by
  rcases threeWords_mem_cases r rest q hq with
    ⟨pre, post, s, hr, hq⟩ | ⟨pre, post, s, hr, hq⟩
  · subst rest
    subst q
    by_cases hs : s = 0
    · subst s
      right
      simpa using three_xzero_replacement_word ρ w r pre post
    · left
      have hk := three_x_replacement_key r s pre post
      refine ⟨congrArg (keyAlphaGrade m) hk, congrArg (keyLeviLevel m) hk, ?_⟩
      simp [middleLetterMeasure, cntUU, posX, List.countP_append,
        Nat.pos_of_ne_zero hs]
      omega
  · subst rest
    subst q
    left
    simp [keyAlphaGrade, keyLeviLevel, keyDepth, wordKey, List.countP_append,
      middleLetterMeasure, cntUU, posX]
    omega

/-- Polarization absorbs a selected middle letter once all smaller terms are absorbed. -/
theorem outerThree_word_mem_next (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (r : ℕ) (rest : List (Fin 6 × ℕ))
    (hκ : keyAlphaGrade m (wordKey ((3, r) :: rest)) = κ)
    (hp : keyLeviLevel m (wordKey ((3, r) :: rest)) = p)
    (hsmall : ∀ q, keyAlphaGrade m (wordKey q) = κ →
      keyLeviLevel m (wordKey q) = p →
      middleLetterMeasure q < middleLetterMeasure ((3, r) :: rest) →
      radicalWord ρ w q ∈ levelFiltration ρ w m κ (p + 1)) :
    radicalWord ρ w ((3, r) :: rest) ∈ levelFiltration ρ w m κ (p + 1) := by
  let N := levelFiltration ρ w m κ (p + 1)
  let v := radicalWord ρ w ((3, r) :: rest)
  let L := (threeWords r rest).map (fun q => radicalWord ρ w ((1, 0) :: q))
  have hL : ∀ x ∈ L, x ∈ N ∨ x = v := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rcases outerThree_replacement_cases ρ w m r rest q hq with ⟨hg, hl, hm⟩ | heq
    · exact Or.inl (hsmall _ (hg.trans hκ) (hl.trans hp) hm)
    · exact Or.inr heq
  obtain ⟨n, hn⟩ := sum_mem_mod_copies N v L hL
  have hsource : radicalWord ρ w ((1, 0) :: rest) ∈ N := by
    apply keyOrbit_le_levelFiltration_of_sat ρ w m h κ (p + 1) _ _ _
      (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _))
    · simp [keyAlphaGrade, keyDepth, wordKey] at hκ ⊢
      omega
    · simp [keyLeviLevel, wordKey] at hp ⊢
      omega
  have hderiv := levelFiltration_stable ρ w m κ (p + 1) 17 r
    (by exact ⟨7, rfl⟩) hsource
  change ρ.op (17 : Fin 28) r (radicalWord ρ w ((1, 0) :: rest)) ∈ N at hderiv
  rw [fThree_radicalWord ρ w m h r ((1, 0) :: rest)] at hderiv
  have hmap : ρ.op (22 : Fin 28) 0
      (((threeWords r rest).map (radicalWord ρ w)).sum) = L.sum := by
    simpa only [L, List.map_map, Function.comp_def, radicalWord,
      List.map_cons, wordOp, radicalColour] using
      (map_list_sum (ρ.op (22 : Fin 28) 0)
        ((threeWords r rest).map (radicalWord ρ w)))
  have hrel : -v - L.sum ∈ N := by
    simpa only [fThreeDerivative, fThreeLetter, if_true, zero_add, add_zero,
      LinearMap.neg_apply, fThreeDerivative_eq_sum ρ w r rest,
      map_neg, show radicalColour 1 = 22 from rfl, hmap, sub_eq_add_neg] using hderiv
  exact mem_of_negative_sum_relation N v L.sum hrel n hn

/-- Derivative summands preserve the level and either decrease the measure or repeat the word. -/
theorem outerFour_replacement_cases (m r : ℕ) (rest q : List (Fin 6 × ℕ))
    (hq : q ∈ fourWords r rest) :
    (keyAlphaGrade m (wordKey ((1, 0) :: q)) =
        keyAlphaGrade m (wordKey ((2, r) :: rest)) ∧
      keyLeviLevel m (wordKey ((1, 0) :: q)) =
        keyLeviLevel m (wordKey ((2, r) :: rest)) ∧
      middleLetterMeasure ((1, 0) :: q) < middleLetterMeasure ((2, r) :: rest)) ∨
    radicalWord ρ w ((1, 0) :: q) = radicalWord ρ w ((2, r) :: rest) := by
  rcases fourWords_mem_cases r rest q hq with
    ⟨pre, post, s, hr, hq⟩ | ⟨pre, post, s, hr, hq⟩
  · subst rest
    subst q
    by_cases hs : s = 0
    · subst s
      right
      simpa using four_xzero_replacement_word ρ w r pre post
    · left
      have hk := four_x_replacement_key r s pre post
      refine ⟨congrArg (keyAlphaGrade m) hk, congrArg (keyLeviLevel m) hk, ?_⟩
      simp [middleLetterMeasure, cntUU, posX, List.countP_append,
        Nat.pos_of_ne_zero hs]
      omega
  · subst rest
    subst q
    left
    simp [keyAlphaGrade, keyLeviLevel, keyDepth, wordKey, List.countP_append,
      middleLetterMeasure, cntUU, posX]
    omega

/-- Polarization absorbs a selected middle letter once all smaller terms are absorbed. -/
theorem outerFour_word_mem_next (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (r : ℕ) (rest : List (Fin 6 × ℕ))
    (hκ : keyAlphaGrade m (wordKey ((2, r) :: rest)) = κ)
    (hp : keyLeviLevel m (wordKey ((2, r) :: rest)) = p)
    (hsmall : ∀ q, keyAlphaGrade m (wordKey q) = κ →
      keyLeviLevel m (wordKey q) = p →
      middleLetterMeasure q < middleLetterMeasure ((2, r) :: rest) →
      radicalWord ρ w q ∈ levelFiltration ρ w m κ (p + 1)) :
    radicalWord ρ w ((2, r) :: rest) ∈ levelFiltration ρ w m κ (p + 1) := by
  let N := levelFiltration ρ w m κ (p + 1)
  let v := radicalWord ρ w ((2, r) :: rest)
  let L := (fourWords r rest).map (fun q => radicalWord ρ w ((1, 0) :: q))
  have hL : ∀ x ∈ L, x ∈ N ∨ x = v := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rcases outerFour_replacement_cases ρ w m r rest q hq with ⟨hg, hl, hm⟩ | heq
    · exact Or.inl (hsmall _ (hg.trans hκ) (hl.trans hp) hm)
    · exact Or.inr heq
  obtain ⟨n, hn⟩ := sum_mem_mod_copies N v L hL
  have hsource : radicalWord ρ w ((1, 0) :: rest) ∈ N := by
    apply keyOrbit_le_levelFiltration_of_sat ρ w m h κ (p + 1) _ _ _
      (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _))
    · simp [keyAlphaGrade, keyDepth, wordKey] at hκ ⊢
      omega
    · simp [keyLeviLevel, wordKey] at hp ⊢
      omega
  have hderiv := levelFiltration_stable ρ w m κ (p + 1) 16 r
    (by exact ⟨12, rfl⟩) hsource
  change ρ.op (16 : Fin 28) r (radicalWord ρ w ((1, 0) :: rest)) ∈ N at hderiv
  rw [fFour_radicalWord ρ w m h r ((1, 0) :: rest)] at hderiv
  have hmap : ρ.op (22 : Fin 28) 0
      (((fourWords r rest).map (radicalWord ρ w)).sum) = L.sum := by
    simpa only [L, List.map_map, Function.comp_def, radicalWord,
      List.map_cons, wordOp, radicalColour] using
      (map_list_sum (ρ.op (22 : Fin 28) 0)
        ((fourWords r rest).map (radicalWord ρ w)))
  have hrel : -v - L.sum ∈ N := by
    simpa only [fFourDerivative, fFourLetter, if_true, zero_add, add_zero,
      LinearMap.neg_apply, fFourDerivative_eq_sum ρ w r rest,
      map_neg, show radicalColour 1 = 22 from rfl, hmap, sub_eq_add_neg] using hderiv
  exact mem_of_negative_sum_relation N v L.sum hrel n hn

/-- Every radical word at an odd level belongs to the next Levi filtration term. -/
theorem radicalWord_mem_next_of_odd (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (hodd : (p - κ) % 2 ≠ 0) (l : List (Fin 6 × ℕ))
    (hκ : keyAlphaGrade m (wordKey l) = κ)
    (hp : keyLeviLevel m (wordKey l) = p) :
    radicalWord ρ w l ∈ levelFiltration ρ w m κ (p + 1) := by
  have H (n : ℕ) : ∀ q : List (Fin 6 × ℕ), middleLetterMeasure q = n →
      keyAlphaGrade m (wordKey q) = κ → keyLeviLevel m (wordKey q) = p →
      radicalWord ρ w q ∈ levelFiltration ρ w m κ (p + 1) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hn hg hl
        have hnonzero : cntUU q ≠ 0 := by
          intro hz
          simp only [cntUU] at hz
          simp only [keyAlphaGrade, keyLeviLevel, keyDepth, wordKey,
            Nat.cast_add] at hg hl
          omega
        by_cases hup : 0 < q.countP (fun x => x.1 = 3)
        · obtain ⟨⟨j, r⟩, hmem, hj⟩ := List.countP_pos_iff.mp hup
          have hj' : j = 3 := of_decide_eq_true hj
          subst j
          have hperm := List.perm_cons_erase hmem
          have hkey := wordKey_perm hperm
          have hmeasure := middleLetterMeasure_perm hperm
          rw [radicalWord_perm ρ w hperm]
          apply outerThree_word_mem_next ρ w m h κ p r (q.erase (3, r))
            (by rwa [← hkey]) (by rwa [← hkey])
          intro t htκ htp ht
          apply ih (middleLetterMeasure t) (by omega) t rfl htκ htp
        · have hu : 0 < q.countP (fun x => x.1 = 2) := by
            simp only [cntUU] at hnonzero
            omega
          obtain ⟨⟨j, r⟩, hmem, hj⟩ := List.countP_pos_iff.mp hu
          have hj' : j = 2 := of_decide_eq_true hj
          subst j
          have hperm := List.perm_cons_erase hmem
          have hkey := wordKey_perm hperm
          have hmeasure := middleLetterMeasure_perm hperm
          rw [radicalWord_perm ρ w hperm]
          apply outerFour_word_mem_next ρ w m h κ p r (q.erase (2, r))
            (by rwa [← hkey]) (by rwa [← hkey])
          intro t htκ htp ht
          apply ih (middleLetterMeasure t) (by omega) t rfl htκ htp
  exact H (middleLetterMeasure l) l rfl hκ hp

/-- Containment of the exact key layer extends to its entire Levi orbit. -/
theorem keyOrbit_le_levelFiltration_of_layer (m : ℕ) (κ p : ℤ) (k : RadicalKey)
    (h : keyLayer ρ w k ≤ levelFiltration ρ w m κ p) :
    keyOrbit ρ w k ≤ levelFiltration ρ w m κ p := by
  rw [keyOrbit, Submodule.span_le]
  rintro z ⟨l, r, hl, hr, rfl⟩
  have hword : wordOp ρ (l ++ r.map fun a => (radicalColour a.1, a.2)) w =
      wordOp ρ l (radicalWord ρ w r) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
        simp only [List.cons_append, wordOp]
        simp only [List.forall_cons] at hl
        rw [ih hl.2]
  rw [hword]
  clear hword
  have hm : radicalWord ρ w r ∈ levelFiltration ρ w m κ p :=
    h (hr ▸ radicalWord_mem_key ρ w r)
  induction l with
  | nil => exact hm
  | cons a l ih =>
      simp only [List.forall_cons] at hl
      exact levelFiltration_stable ρ w m κ p a.1 a.2 hl.1 (ih hl.2)

/-- Odd coroot levels have no associated graded piece in a saturated D4 module. -/
theorem levelFiltration_eq_next_of_odd (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (hodd : (p - κ) % 2 ≠ 0) :
    levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    apply iSup_le
    intro hκ
    apply iSup_le
    intro hp
    by_cases heq : keyLeviLevel m k = p
    · apply keyOrbit_le_levelFiltration_of_layer
      rw [keyLayer, Submodule.span_le]
      rintro v ⟨l, hl, rfl⟩
      exact radicalWord_mem_next_of_odd ρ w m h κ p hodd l
        (by rwa [hl]) (by rwa [hl])
    · exact keyOrbit_le_levelFiltration ρ w m κ (p + 1) k hk hκ (by omega)
  · exact levelFiltration_antitone ρ w m κ (by omega)

/-- The universal coinvariant at an odd level is zero-dimensional, for every multiplicity. -/
theorem universalLevel_finrank_zero_of_odd (m : ℕ) (κ p : ℤ)
    (hodd : (p - κ) % 2 ≠ 0) : Module.finrank ℂ (UniversalLevelPiece m κ p) = 0 := by
  exact truncatedLevel_finrank_zero_of_eq_next _ _ m κ p
    (levelFiltration_eq_next_of_odd _ _ m
      (univG_sat D4sector.f (ravFam D4sector m 0)) κ p hodd)

/-- All universal odd-level truncation bounds hold. -/
theorem levelTruncationBound_of_odd (m : ℕ) (κ p : ℤ)
    (hodd : (p - κ) % 2 ≠ 0) : LevelTruncationBound m κ p := by
  change Module.finrank ℂ (UniversalLevelPiece m κ p) ≤ _
  rw [universalLevel_finrank_zero_of_odd m κ p hodd]
  exact Nat.zero_le _

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.keyOrbit_le_levelFiltration_of_sat
#print axioms VOA.DeligneAudit.D4LevelReduction.middleLetterMeasure_perm
#print axioms VOA.DeligneAudit.D4LevelReduction.outerThree_replacement_cases
#print axioms VOA.DeligneAudit.D4LevelReduction.outerFour_replacement_cases
#print axioms VOA.DeligneAudit.D4LevelReduction.outerThree_word_mem_next
#print axioms VOA.DeligneAudit.D4LevelReduction.outerFour_word_mem_next

#print axioms VOA.DeligneAudit.D4LevelReduction.radicalWord_mem_next_of_odd

#print axioms VOA.DeligneAudit.D4LevelReduction.keyOrbit_le_levelFiltration_of_layer

#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_eq_next_of_odd

#print axioms VOA.DeligneAudit.D4LevelReduction.universalLevel_finrank_zero_of_odd

#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_odd
