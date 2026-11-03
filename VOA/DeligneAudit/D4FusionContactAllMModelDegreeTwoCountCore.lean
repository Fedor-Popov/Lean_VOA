import VOA.DeligneAudit.D4FusionContactM2CountBound

/-! Current-degree refinement of the m=2 normal-word count. The current degree
of a word in the 18 letters is its number of odd letters (mode one under
`varIndex`). The stem recursion of `enumerateFrom` is refined degree by degree;
the existing kernel-checked stem flags are reused, so no `Avoids` test is
re-evaluated. -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

/-- The current degree of a normal word: its number of mode-one letters. -/
def wordCurrentDeg (w : List (Fin 18)) : ℕ := (w.map fun v => v.val % 2).sum

/-- The number of words of current degree b in a list. -/
def degCount (L : List (List (Fin 18))) (b : ℕ) : ℕ :=
  L.countP fun w => decide (wordCurrentDeg w = b)

theorem degCount_of_flags (leaders : List (List (Fin 18))) (fuel lower : ℕ)
    (stem : List (Fin 18)) (flags : Fin 18 → Bool) (counts : Fin 18 → Fin 5 → ℕ)
    (hflags : ∀ v, (lower ≤ v.val ∧ Avoids leaders (stem ++ [v])) ↔ flags v = true)
    (hcounts : ∀ v, flags v = true → ∀ b : Fin 5,
      degCount (enumerateFrom leaders fuel v.val (stem ++ [v])) b.val = counts v b)
    (b : Fin 5) :
    degCount (enumerateFrom leaders (fuel + 1) lower stem) b.val =
      ((List.finRange 18).map fun v => if flags v = true then counts v b else 0).sum +
        (if wordCurrentDeg stem = b.val then 1 else 0) := by
  unfold degCount
  rw [enumerateFrom, List.countP_cons, List.countP_flatMap]
  refine congrArg₂ (· + ·) (congrArg List.sum (List.map_congr_left ?_)) ?_
  · intro v _
    by_cases h : flags v = true
    · rw [Function.comp_apply, if_pos ((hflags v).mpr h), if_pos h]
      exact hcounts v h b
    · rw [Function.comp_apply, if_neg (fun hc => h ((hflags v).mp hc)), if_neg h]
      rfl
  · by_cases h : wordCurrentDeg stem = b.val <;> simp [h]

theorem degCount_leaf (leaders : List (List (Fin 18))) (lower : ℕ) (w : List (Fin 18))
    (b : ℕ) :
    degCount (enumerateFrom leaders 0 lower w) b = if wordCurrentDeg w = b then 1 else 0 := by
  unfold degCount
  rw [enumerateFrom]
  by_cases h : wordCurrentDeg w = b <;> simp [h]

/-- A one-step stem: every child is a leaf. -/
theorem degCount_fuel_one (leaders : List (List (Fin 18))) (lower : ℕ)
    (stem : List (Fin 18)) (flags : Fin 18 → Bool)
    (hflags : ∀ v, (lower ≤ v.val ∧ Avoids leaders (stem ++ [v])) ↔ flags v = true)
    (b : Fin 5) :
    degCount (enumerateFrom leaders 1 lower stem) b.val =
      ((List.finRange 18).map fun v => if flags v = true then
          (if wordCurrentDeg (stem ++ [v]) = b.val then 1 else 0) else 0).sum +
        (if wordCurrentDeg stem = b.val then 1 else 0) :=
  degCount_of_flags leaders 0 lower stem flags
    (fun v c => if wordCurrentDeg (stem ++ [v]) = c.val then 1 else 0) hflags
    (fun v _ c => degCount_leaf leaders v.val (stem ++ [v]) c.val) b

/-- Every enumerated word extends its stem by at most `fuel` letters. -/
theorem length_le_of_mem_enumerateFrom (leaders : List (List (Fin 18))) :
    ∀ (fuel lower : ℕ) (stem w : List (Fin 18)),
      w ∈ enumerateFrom leaders fuel lower stem → w.length ≤ stem.length + fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro lower stem w hw
      rw [enumerateFrom, List.mem_singleton] at hw
      subst hw
      omega
  | succ fuel ih =>
      intro lower stem w hw
      rw [enumerateFrom, List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hw
        split_ifs at hv with hc
        · have := ih v.val (stem ++ [v]) w hv
          simp only [List.length_append, List.length_singleton] at this
          omega
        · simp at hv

theorem wordCurrentDeg_le_length (w : List (Fin 18)) : wordCurrentDeg w ≤ w.length := by
  induction w with
  | nil => simp [wordCurrentDeg]
  | cons v w ih =>
      simp only [wordCurrentDeg, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      have := Nat.mod_lt v.val (show 0 < 2 by omega)
      omega

end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.degCount_of_flags
#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.degCount_fuel_one
#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.length_le_of_mem_enumerateFrom
