import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Perm.Basic

/-! Pure finite-list normal forms for the nine contact current colors.
Every word is permuted into its eight noncentral colors, then center
mode zero, then positive center modes. No module or source premise occurs. -/
namespace VOA.DeligneAudit.D4FusionContact

/-- Separate arbitrary current letters into noncentral letters, zero-mode
center letters, and strictly positive center modes, by a genuine permutation. -/
theorem exists_current_normal_form (l : List (Fin 9 × ℕ)) :
    ∃ (a : List (Fin 8 × ℕ)) (n : ℕ) (c : List ℕ),
      (∀ r ∈ c, 0 < r) ∧
      l.Perm (a.map (fun x => (x.1.castSucc, x.2)) ++
        (List.replicate n (8, 0) ++ c.map (fun r => (8, r)))) := by
  induction l with
  | nil => exact ⟨[], 0, [], by simp, .nil⟩
  | cons x l ih =>
      obtain ⟨a, n, c, hc, hp⟩ := ih
      obtain ⟨i, r⟩ := x
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rcases Nat.eq_zero_or_pos r with rfl | hr
        · refine ⟨a, n + 1, c, hc, ?_⟩
          apply (hp.cons (8, 0)).trans
          simpa only [List.replicate_succ, List.cons_append] using
            (List.perm_middle (a := ((8, 0) : Fin 9 × ℕ))
              (l₁ := a.map (fun x => (x.1.castSucc, x.2)))
              (l₂ := List.replicate n (8, 0) ++ c.map (fun r => (8, r)))).symm
        · refine ⟨a, n, r :: c, ?_, ?_⟩
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hr
            · exact hc t ht
          · apply (hp.cons (8, r)).trans
            simp only [List.map_cons]
            rw [← List.append_assoc, ← List.append_assoc]
            exact List.perm_middle.symm
      · refine ⟨(i, r) :: a, n, c, hc, ?_⟩
        simpa only [List.map_cons, List.cons_append] using hp.cons (i.castSucc, r)

/-- The partition of letters preserves their total number, directly from
its permutation witness; no normal-word independence is assumed. -/
theorem current_normal_form_length {l : List (Fin 9 × ℕ)}
    {a : List (Fin 8 × ℕ)} {n : ℕ} {c : List ℕ}
    (hp : l.Perm (a.map (fun x => (x.1.castSucc, x.2)) ++
      (List.replicate n (8, 0) ++ c.map (fun r => (8, r))))) :
    l.length = a.length + n + c.length := by
  simpa only [List.length_append, List.length_map, List.length_replicate,
    Nat.add_assoc] using hp.length_eq

end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.exists_current_normal_form
#print axioms VOA.DeligneAudit.D4FusionContact.current_normal_form_length
