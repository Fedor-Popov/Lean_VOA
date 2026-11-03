import VOA.DeligneAudit.D4LevelReductionModeGeneration

/-! Elimination of the two middle radical colours modulo higher Levi levels. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

private theorem sum_mem_mod_repeated_vector (N : Submodule ℂ V) (v : V) (L : List V)
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

private theorem mem_of_negative_repeated_relation (N : Submodule ℂ V) (v s : V)
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

/-- Polarization absorbs a selected middle letter once all smaller terms are absorbed. -/
theorem outerThree_word_mem_invariant (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (N : Submodule ℂ V) (hN : ∀ e s, IsLevi e → N ≤ N.comap (ρ.op e s))
    (hnext : levelFiltration ρ w m κ (p + 1) ≤ N)
    (r : ℕ) (rest : List (Fin 6 × ℕ))
    (hκ : keyAlphaGrade m (wordKey ((3, r) :: rest)) = κ)
    (hp : keyLeviLevel m (wordKey ((3, r) :: rest)) = p)
    (hsmall : ∀ q, keyAlphaGrade m (wordKey q) = κ →
      keyLeviLevel m (wordKey q) = p →
      middleLetterMeasure q < middleLetterMeasure ((3, r) :: rest) →
      radicalWord ρ w q ∈ N) :
    radicalWord ρ w ((3, r) :: rest) ∈ N := by
  let v := radicalWord ρ w ((3, r) :: rest)
  let L := (threeWords r rest).map (fun q => radicalWord ρ w ((1, 0) :: q))
  have hL : ∀ x ∈ L, x ∈ N ∨ x = v := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rcases outerThree_replacement_cases ρ w m r rest q hq with ⟨hg, hl, hm⟩ | heq
    · exact Or.inl (hsmall _ (hg.trans hκ) (hl.trans hp) hm)
    · exact Or.inr heq
  obtain ⟨n, hn⟩ := sum_mem_mod_repeated_vector N v L hL
  have hsource : radicalWord ρ w ((1, 0) :: rest) ∈ N := by
    apply hnext
    apply keyOrbit_le_levelFiltration_of_sat ρ w m h κ (p + 1) _ _ _
      (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _))
    · simp [keyAlphaGrade, keyDepth, wordKey] at hκ ⊢
      omega
    · simp [keyLeviLevel, wordKey] at hp ⊢
      omega
  have hderiv := hN 17 r
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
  exact mem_of_negative_repeated_relation N v L.sum hrel n hn

/-- Polarization absorbs a selected middle letter once all smaller terms are absorbed. -/
theorem outerFour_word_mem_invariant (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (N : Submodule ℂ V) (hN : ∀ e s, IsLevi e → N ≤ N.comap (ρ.op e s))
    (hnext : levelFiltration ρ w m κ (p + 1) ≤ N)
    (r : ℕ) (rest : List (Fin 6 × ℕ))
    (hκ : keyAlphaGrade m (wordKey ((2, r) :: rest)) = κ)
    (hp : keyLeviLevel m (wordKey ((2, r) :: rest)) = p)
    (hsmall : ∀ q, keyAlphaGrade m (wordKey q) = κ →
      keyLeviLevel m (wordKey q) = p →
      middleLetterMeasure q < middleLetterMeasure ((2, r) :: rest) →
      radicalWord ρ w q ∈ N) :
    radicalWord ρ w ((2, r) :: rest) ∈ N := by
  let v := radicalWord ρ w ((2, r) :: rest)
  let L := (fourWords r rest).map (fun q => radicalWord ρ w ((1, 0) :: q))
  have hL : ∀ x ∈ L, x ∈ N ∨ x = v := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rcases outerFour_replacement_cases ρ w m r rest q hq with ⟨hg, hl, hm⟩ | heq
    · exact Or.inl (hsmall _ (hg.trans hκ) (hl.trans hp) hm)
    · exact Or.inr heq
  obtain ⟨n, hn⟩ := sum_mem_mod_repeated_vector N v L hL
  have hsource : radicalWord ρ w ((1, 0) :: rest) ∈ N := by
    apply hnext
    apply keyOrbit_le_levelFiltration_of_sat ρ w m h κ (p + 1) _ _ _
      (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _))
    · simp [keyAlphaGrade, keyDepth, wordKey] at hκ ⊢
      omega
    · simp [keyLeviLevel, wordKey] at hp ⊢
      omega
  have hderiv := hN 16 r
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
  exact mem_of_negative_repeated_relation N v L.sum hrel n hn

/-- Three-colour membership extends to every radical word at the same grade and level. -/
theorem radicalWord_mem_of_threeColour (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (N : Submodule ℂ V) (hN : ∀ e r, IsLevi e → N ≤ N.comap (ρ.op e r))
    (hnext : levelFiltration ρ w m κ (p + 1) ≤ N)
    (hxyz : ∀ l : List (Fin 6 × ℕ),
      (∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5) →
      keyAlphaGrade m (wordKey l) = κ → keyLeviLevel m (wordKey l) = p →
      radicalWord ρ w l ∈ N) (l : List (Fin 6 × ℕ))
    (hκ : keyAlphaGrade m (wordKey l) = κ)
    (hp : keyLeviLevel m (wordKey l) = p) :
    radicalWord ρ w l ∈ N := by
  have H (n : ℕ) : ∀ q : List (Fin 6 × ℕ), middleLetterMeasure q = n →
      keyAlphaGrade m (wordKey q) = κ → keyLeviLevel m (wordKey q) = p →
      radicalWord ρ w q ∈ N := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hn hg hl
        by_cases he : 0 < q.countP (fun t => t.1 = 0)
        · rw [radicalWord_zero_of_E ρ w m h q he]
          exact N.zero_mem
        by_cases hnonzero : cntUU q = 0
        · apply hxyz q _ hg hl
          intro t ht
          have hnot (i : Fin 6) (hz : q.countP (fun s => s.1 = i) = 0) : t.1 ≠ i := by
            intro hi
            have hh : 0 < q.countP (fun s => s.1 = i) :=
              List.countP_pos_iff.mpr ⟨t, ht, by simpa using hi⟩
            omega
          have hzero : q.countP (fun t => t.1 = 0) = 0 := by omega
          have hmid : q.countP (fun t => t.1 = 2) = 0 ∧
              q.countP (fun t => t.1 = 3) = 0 := by
            simp only [cntUU] at hnonzero
            omega
          have h0 := hnot 0 hzero
          have h2 := hnot 2 hmid.1
          have h3 := hnot 3 hmid.2
          rcases t with ⟨i, s⟩
          fin_cases i <;> simp_all
        by_cases hup : 0 < q.countP (fun x => x.1 = 3)
        · obtain ⟨⟨j, r⟩, hmem, hj⟩ := List.countP_pos_iff.mp hup
          have hj' : j = 3 := of_decide_eq_true hj
          subst j
          have hperm := List.perm_cons_erase hmem
          have hkey := wordKey_perm hperm
          have hmeasure := middleLetterMeasure_perm hperm
          rw [radicalWord_perm ρ w hperm]
          apply outerThree_word_mem_invariant ρ w m h κ p N hN hnext r (q.erase (3, r))
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
          apply outerFour_word_mem_invariant ρ w m h κ p N hN hnext r (q.erase (2, r))
            (by rwa [← hkey]) (by rwa [← hkey])
          intro t htκ htp ht
          apply ih (middleLetterMeasure t) (by omega) t rfl htκ htp
  exact H (middleLetterMeasure l) l rfl hκ hp


/-- Containment of an exact key layer extends to its full reductive orbit. -/
theorem keyOrbit_le_leviInvariant (N : Submodule ℂ V)
    (hN : ∀ e r, IsLevi e → N ≤ N.comap (ρ.op e r)) (k : RadicalKey)
    (hk : keyLayer ρ w k ≤ N) : keyOrbit ρ w k ≤ N := by
  rw [keyOrbit, Submodule.span_le]
  rintro z ⟨l, r, hl, hr, rfl⟩
  have hm := hk (hr ▸ radicalWord_mem_key ρ w r)
  induction l with
  | nil => exact hm
  | cons q l ih =>
      simp only [List.forall_cons] at hl
      exact hN q.1 q.2 hl.1 (ih hl.2)

/-- Three-colour words generate an entire Levi level modulo its next filtration term. -/
theorem levelFiltration_le_of_threeColour (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (N : Submodule ℂ V) (hN : ∀ e r, IsLevi e → N ≤ N.comap (ρ.op e r))
    (hnext : levelFiltration ρ w m κ (p + 1) ≤ N)
    (hxyz : ∀ l : List (Fin 6 × ℕ),
      (∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5) →
      keyAlphaGrade m (wordKey l) = κ → keyLeviLevel m (wordKey l) = p →
      radicalWord ρ w l ∈ N) : levelFiltration ρ w m κ p ≤ N := by
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  apply iSup_le
  intro hg
  apply iSup_le
  intro hp
  by_cases heq : keyLeviLevel m k = p
  · apply keyOrbit_le_leviInvariant ρ w N hN k
    rw [keyLayer, Submodule.span_le]
    rintro v ⟨l, hl, rfl⟩
    exact radicalWord_mem_of_threeColour ρ w m h κ p N hN hnext hxyz l
      (by rwa [hl]) (by rwa [hl])
  · exact (keyOrbit_le_levelFiltration ρ w m κ (p + 1) k hk hg (by omega)).trans hnext

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.outerThree_word_mem_invariant
#print axioms VOA.DeligneAudit.D4LevelReduction.outerFour_word_mem_invariant
#print axioms VOA.DeligneAudit.D4LevelReduction.radicalWord_mem_of_threeColour
#print axioms VOA.DeligneAudit.D4LevelReduction.keyOrbit_le_leviInvariant
#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_le_of_threeColour
