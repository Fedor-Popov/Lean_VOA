import VOA.DeligneAudit.D4LeviKSLemma0Classify

/-! The measure-lowering subspace for D4 Lemma 0. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Exact-key words whose elimination measure is below a prescribed bound. -/
def measureLowerSpan (k : RadicalKey) (bound : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List (Fin 6 × ℕ),
    wordKey l = k ∧ lemmaZeroMeasure k l < bound ∧ v = radicalWord ρ w l}

/-- The target of one induction step: lower measure plus higher Levi keys. -/
def lemmaZeroStepSpace (k : RadicalKey) (bound : ℕ) : Submodule ℂ V :=
  measureLowerSpan ρ w k bound ⊔ higherOrbit ρ w m k

private theorem sum_mod_copies (N : Submodule ℂ V) (v : V) (L : List V)
    (h : ∀ x ∈ L, x ∈ N ∨ x = v) :
    ∃ n : ℕ, L.sum - (n : ℂ) • v ∈ N := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, y ∈ N ∨ y = v := by
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)
      obtain ⟨n, hn⟩ := ih htail
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

private theorem mem_of_neg_add_copies (N : Submodule ℂ V) (v s : V)
    (hrel : -v - s ∈ N) (n : ℕ) (hs : s - (n : ℂ) • v ∈ N) :
    v ∈ N := by
  have hscaled : -((n + 1 : ℕ) : ℂ) • v ∈ N := by
    convert N.add_mem hrel hs using 1
    push_cast
    simp only [add_smul, one_smul, neg_smul]
    abel
  have hne : (-((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
  have hi := N.smul_mem (-((n + 1 : ℕ) : ℂ))⁻¹ hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using hi

/-- S1 for a word with the selected U' already at the front. -/
theorem three_step_cons
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (rest : List (Fin 6 × ℕ)) :
    radicalWord ρ w ((3, r) :: rest) ∈
      lemmaZeroStepSpace ρ w m (wordKey ((3, r) :: rest))
        (lemmaZeroMeasure (wordKey ((3, r) :: rest)) ((3, r) :: rest)) := by
  let l := (3, r) :: rest
  let k := wordKey l
  let v := radicalWord ρ w l
  let N := lemmaZeroStepSpace ρ w m k (lemmaZeroMeasure k l)
  let L := (threeWords r rest).map (fun q => radicalWord ρ w ((1, 0) :: q))
  have hterm (q : List (Fin 6 × ℕ)) (hq : q ∈ threeWords r rest) :
      radicalWord ρ w ((1, 0) :: q) ∈ N ∨
        radicalWord ρ w ((1, 0) :: q) = v := by
    rcases three_term_trichotomy ρ w m r rest q hq with
      ⟨hk, hm⟩ | hv | hh
    · left
      exact Submodule.mem_sup_left
        (Submodule.subset_span ⟨(1, 0) :: q, hk, hm, rfl⟩)
    · exact Or.inr hv
    · left
      exact Submodule.mem_sup_right
        (keyOrbit_le_higher ρ w m k (wordKey ((1, 0) :: q)) hh
          (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _)))
  have hL : ∀ x ∈ L, x ∈ N ∨ x = v := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hterm q hq
  obtain ⟨n, hn⟩ := sum_mod_copies N v L hL
  have hmap :
      ρ.op (22 : Fin 28) 0
        (((threeWords r rest).map (radicalWord ρ w)).sum) = L.sum := by
    simpa only [L, List.map_map, Function.comp_def, radicalWord,
      List.map_cons, wordOp, radicalColour] using
      (map_list_sum (ρ.op (22 : Fin 28) 0)
        ((threeWords r rest).map (radicalWord ρ w)))
  have hsource := fThree_xzero_higher ρ w m h k r rest
    (xzero_higher_up m r rest)
  have hrel : -v - L.sum ∈ N := by
    rw [fThreeDerivative_eq_sum ρ w r rest, map_neg, hmap] at hsource
    have hv : ρ.op (25 : Fin 28) r (radicalWord ρ w rest) = v := rfl
    rw [hv] at hsource
    simpa only [sub_eq_add_neg] using
      (Submodule.mem_sup_right hsource : -v + -L.sum ∈ N)
  exact mem_of_neg_add_copies N v L.sum hrel n hn

/-- S2 for a word with the selected U already at the front. -/
theorem four_step_cons
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (rest : List (Fin 6 × ℕ)) :
    radicalWord ρ w ((2, r) :: rest) ∈
      lemmaZeroStepSpace ρ w m (wordKey ((2, r) :: rest))
        (lemmaZeroMeasure (wordKey ((2, r) :: rest)) ((2, r) :: rest)) := by
  let l := (2, r) :: rest
  let k := wordKey l
  let v := radicalWord ρ w l
  let N := lemmaZeroStepSpace ρ w m k (lemmaZeroMeasure k l)
  let L := (fourWords r rest).map (fun q => radicalWord ρ w ((1, 0) :: q))
  have hterm (q : List (Fin 6 × ℕ)) (hq : q ∈ fourWords r rest) :
      radicalWord ρ w ((1, 0) :: q) ∈ N ∨
        radicalWord ρ w ((1, 0) :: q) = v := by
    rcases four_term_trichotomy ρ w m r rest q hq with
      ⟨hk, hm⟩ | hv | hh
    · left
      exact Submodule.mem_sup_left
        (Submodule.subset_span ⟨(1, 0) :: q, hk, hm, rfl⟩)
    · exact Or.inr hv
    · left
      exact Submodule.mem_sup_right
        (keyOrbit_le_higher ρ w m k (wordKey ((1, 0) :: q)) hh
          (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w _)))
  have hL : ∀ x ∈ L, x ∈ N ∨ x = v := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hterm q hq
  obtain ⟨n, hn⟩ := sum_mod_copies N v L hL
  have hmap :
      ρ.op (22 : Fin 28) 0
        (((fourWords r rest).map (radicalWord ρ w)).sum) = L.sum := by
    simpa only [L, List.map_map, Function.comp_def, radicalWord,
      List.map_cons, wordOp, radicalColour] using
      (map_list_sum (ρ.op (22 : Fin 28) 0)
        ((fourWords r rest).map (radicalWord ρ w)))
  have hsource := fFour_xzero_higher ρ w m h k r rest
    (xzero_higher_u m r rest)
  have hrel : -v - L.sum ∈ N := by
    rw [fFourDerivative_eq_sum ρ w r rest, map_neg, hmap] at hsource
    have hv : ρ.op (24 : Fin 28) r (radicalWord ρ w rest) = v := rfl
    rw [hv] at hsource
    simpa only [sub_eq_add_neg] using
      (Submodule.mem_sup_right hsource : -v + -L.sum ∈ N)
  exact mem_of_neg_add_copies N v L.sum hrel n hn

/-- The induction measure is unchanged by permuting radical letters. -/
theorem lemmaZeroMeasure_perm (k : RadicalKey)
    {l₁ l₂ : List (Fin 6 × ℕ)} (hp : l₁.Perm l₂) :
    lemmaZeroMeasure k l₁ = lemmaZeroMeasure k l₂ := by
  simp [lemmaZeroMeasure, cntUU, posX, hp.countP_eq]

/-- S1: a selected U' reduces to smaller-measure words and higher keys. -/
theorem three_step
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (l : List (Fin 6 × ℕ)) (hk : wordKey l = k)
    (r : ℕ) (hr : (3, r) ∈ l) :
    radicalWord ρ w l ∈ lemmaZeroStepSpace ρ w m k
      (lemmaZeroMeasure k l) := by
  let rest := l.erase (3, r)
  have hp : l.Perm ((3, r) :: rest) := List.perm_cons_erase hr
  have hkey := wordKey_perm hp
  have hmeasure := lemmaZeroMeasure_perm (wordKey l) hp
  have hword := radicalWord_perm ρ w hp
  have hs := three_step_cons ρ w m h r rest
  rw [← hkey, ← hmeasure, ← hword] at hs
  simpa only [hk] using hs

/-- S2: a selected U reduces to smaller-measure words and higher keys. -/
theorem four_step
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (l : List (Fin 6 × ℕ)) (hk : wordKey l = k)
    (r : ℕ) (hr : (2, r) ∈ l) :
    radicalWord ρ w l ∈ lemmaZeroStepSpace ρ w m k
      (lemmaZeroMeasure k l) := by
  let rest := l.erase (2, r)
  have hp : l.Perm ((2, r) :: rest) := List.perm_cons_erase hr
  have hkey := wordKey_perm hp
  have hmeasure := lemmaZeroMeasure_perm (wordKey l) hp
  have hword := radicalWord_perm ρ w hp
  have hs := four_step_cons ρ w m h r rest
  rw [← hkey, ← hmeasure, ← hword] at hs
  simpa only [hk] using hs

/-- S3: every exact-key radical word reduces to XYZ and higher keys. -/
theorem lemmaZero_word
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (l : List (Fin 6 × ℕ)) (hk : wordKey l = k) :
    radicalWord ρ w l ∈ xyzSpan ρ w k ⊔ higherOrbit ρ w m k := by
  let N := xyzSpan ρ w k ⊔ higherOrbit ρ w m k
  have H (n : ℕ) : ∀ q : List (Fin 6 × ℕ),
      wordKey q = k → lemmaZeroMeasure k q = n → radicalWord ρ w q ∈ N := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hq hn
        by_cases hzero : cntUU q = 0
        · have hu : q.countP (fun p => p.1 = 2) = 0 := by
            simp only [cntUU] at hzero
            omega
          have hup : q.countP (fun p => p.1 = 3) = 0 := by
            simp only [cntUU] at hzero
            omega
          have hku : k.u = 0 := by simpa [← hq, wordKey] using hu
          have hkup : k.up = 0 := by simpa [← hq, wordKey] using hup
          have hmem : radicalWord ρ w q ∈ keyLayer ρ w k := by
            simpa only [hq] using radicalWord_mem_key ρ w q
          exact Submodule.mem_sup_left
            (keyLayer_le_xyzSpan_of_no_U ρ w m h k hku hkup hmem)
        · have hsmall : measureLowerSpan ρ w k n ≤ N := by
            rw [measureLowerSpan, Submodule.span_le]
            rintro v ⟨t, ht, hm, rfl⟩
            exact ih (lemmaZeroMeasure k t) hm t ht rfl
          have htransfer : lemmaZeroStepSpace ρ w m k n ≤ N := by
            exact sup_le hsmall le_sup_right
          by_cases hup : 0 < q.countP (fun p => p.1 = 3)
          · obtain ⟨⟨j, r⟩, hmem, hj⟩ := List.countP_pos_iff.mp hup
            have hj' : j = 3 := of_decide_eq_true hj
            subst j
            have hs := three_step ρ w m h k q hq r hmem
            rw [hn] at hs
            exact htransfer hs
          · have hucount : 0 < q.countP (fun p => p.1 = 2) := by
              have hz : q.countP (fun p => p.1 = 3) = 0 :=
                Nat.eq_zero_of_not_pos hup
              simp only [cntUU, hz, add_zero] at hzero
              omega
            obtain ⟨⟨j, r⟩, hmem, hj⟩ :=
              List.countP_pos_iff.mp hucount
            have hj' : j = 2 := of_decide_eq_true hj
            subst j
            have hs := four_step ρ w m h k q hq r hmem
            rw [hn] at hs
            exact htransfer hs
  exact H (lemmaZeroMeasure k l) l hk rfl

/-- S4: every exact key layer is generated by XYZ words modulo higher keys. -/
theorem keyLayer_le_xyzSpan_sup_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) :
    keyLayer ρ w k ≤ xyzSpan ρ w k ⊔ higherOrbit ρ w m k := by
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hk, rfl⟩
  exact lemmaZero_word ρ w m h k l hk

/-- S4 at an enumerated key, with the actual filtration prefix. -/
theorem keyLayer_le_xyzSpan_sup_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : ℕ) (hi : i < (globalKeyBox m).card) :
    keyLayer ρ w (keyEnum m ⟨i, hi⟩) ≤
      xyzSpan ρ w (keyEnum m ⟨i, hi⟩) ⊔ keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi]
  exact keyLayer_le_xyzSpan_sup_higher ρ w m h _

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.three_step_cons
#print axioms VOA.DeligneAudit.D4Levi.four_step_cons
#print axioms VOA.DeligneAudit.D4Levi.lemmaZeroMeasure_perm
#print axioms VOA.DeligneAudit.D4Levi.three_step
#print axioms VOA.DeligneAudit.D4Levi.four_step
#print axioms VOA.DeligneAudit.D4Levi.lemmaZero_word
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_xyzSpan_sup_higher
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_xyzSpan_sup_prefix
