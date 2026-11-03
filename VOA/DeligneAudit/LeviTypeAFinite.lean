import VOA.DeligneAudit.LeviTypeA

/-! Finiteness of a fixed radical-letter layer from a uniform mode cutoff. -/

namespace VOA.DeligneAudit.LeviTypeA

noncomputable section

variable {A V : Type*} [Ring A] [AddCommGroup V] [Module A V]
  [Module ℂ V]

def radicalWord {n : ℕ} (F : Fin n → ℕ → A)
    (l : List (Fin n × ℕ)) : A :=
  (l.map fun p => F p.1 p.2).prod

def radicalLayer {n : ℕ} (F : Fin n → ℕ → A) (w : V)
    (j : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l : List (Fin n × ℕ),
    l.length = j ∧ z = radicalWord F l • w}

private theorem commute_radicalWord {n : ℕ} (F : Fin n → ℕ → A)
    (hcomm : ∀ i s j t, F i s * F j t = F j t * F i s)
    (i : Fin n) (s : ℕ) (l : List (Fin n × ℕ)) :
    F i s * radicalWord F l = radicalWord F l * F i s := by
  induction l with
  | nil => simp [radicalWord]
  | cons p l ih =>
    rcases p with ⟨j, t⟩
    change F i s * (F j t * radicalWord F l) =
      (F j t * radicalWord F l) * F i s
    calc
      F i s * (F j t * radicalWord F l) =
          (F i s * F j t) * radicalWord F l := by rw [mul_assoc]
      _ = (F j t * F i s) * radicalWord F l := by rw [hcomm]
      _ = F j t * (F i s * radicalWord F l) := by rw [mul_assoc]
      _ = F j t * (radicalWord F l * F i s) := by rw [ih]
      _ = (F j t * radicalWord F l) * F i s := by rw [mul_assoc]

omit [Module ℂ V] in
private theorem radicalWord_bad_zero {n B : ℕ} (F : Fin n → ℕ → A)
    (w : V) (hcomm : ∀ i s j t, F i s * F j t = F j t * F i s)
    (hcut : ∀ i s, B ≤ s → F i s • w = 0)
    (l : List (Fin n × ℕ))
    (hbad : ∃ p ∈ l, B ≤ p.2) : radicalWord F l • w = 0 := by
  induction l with
  | nil => simp at hbad
  | cons p l ih =>
    rcases p with ⟨i, s⟩
    rcases hbad with ⟨q, hq, hqs⟩
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · change (F i s * radicalWord F l) • w = 0
      rw [commute_radicalWord F hcomm i s l, mul_smul, hcut i s hqs]
      simp
    · change (F i s * radicalWord F l) • w = 0
      rw [mul_smul, ih ⟨q, hq, hqs⟩]
      simp

/-- A fixed-length radical layer is finite-dimensional when high modes kill
the cyclic vector and all radical letters commute. -/
theorem radicalLayer_finite {n B : ℕ} (F : Fin n → ℕ → A) (w : V)
    (hcomm : ∀ i s j t, F i s * F j t = F j t * F i s)
    (hcut : ∀ i s, B ≤ s → F i s • w = 0)
    (j : ℕ) : FiniteDimensional ℂ (radicalLayer F w j) := by
  let bounded : (Fin j → Fin n × Fin B) → V := fun q =>
    radicalWord F ((List.finRange j).map fun t => ((q t).1, (q t).2.val)) • w
  let D : Submodule ℂ V := Submodule.span ℂ (Set.range bounded)
  have hfinite : FiniteDimensional ℂ D :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range bounded)
  have hle : radicalLayer F w j ≤ D := by
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨l, hl, rfl⟩ := hz
    by_cases hgood : ∀ p ∈ l, p.2 < B
    · have hget (t : Fin l.length) : (l.get t).2 < B :=
        hgood (l.get t) (List.get_mem l t)
      let q : Fin l.length → Fin n × Fin B := fun t =>
        ((l.get t).1, ⟨(l.get t).2, hget t⟩)
      have hword : ((List.finRange l.length).map
          fun t => ((q t).1, (q t).2.val)) = l := by
        simp [q]
      have hmem : radicalWord F l • w ∈
          Submodule.span ℂ (Set.range (fun r : Fin l.length → Fin n × Fin B =>
            radicalWord F ((List.finRange l.length).map
              fun t => ((r t).1, (r t).2.val)) • w)) := by
        apply Submodule.subset_span
        exact ⟨q, by simp [hword]⟩
      cases hl
      exact hmem
    · have hbad : ∃ p ∈ l, B ≤ p.2 := by
        obtain ⟨p, hp⟩ := not_forall.mp hgood
        obtain ⟨hmem, hnot⟩ := Classical.not_imp.mp hp
        exact ⟨p, hmem, Nat.le_of_not_gt hnot⟩
      rw [radicalWord_bad_zero F w hcomm hcut l hbad]
      exact D.zero_mem
  letI : FiniteDimensional ℂ D := hfinite
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

end
end VOA.DeligneAudit.LeviTypeA

#print axioms VOA.DeligneAudit.LeviTypeA.radicalLayer_finite
