import VOA.DeligneAudit.D4FusionContactCurrentFiltration

/-! Permuting actual radical current words changes only lower contact length.
The proof uses exact all-mode contact brackets and needs no highest-weight,
nilpotence, finite-dimensionality or presentation premise. -/
namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

/-- Radical current prefixes act by the actual concatenated word. -/
theorem currentRadicalWord_append (p s : List CurrentLetter) (v : V) :
    currentRadicalWord R (p ++ s) v =
      currentRadicalWord R p (currentRadicalWord R s v) := by
  simp only [currentRadicalWord, List.map_append, wordOp_append]

/-- Linearity in the vector is preserved by every current-word prefix. -/
theorem currentRadicalWord_sub (p : List CurrentLetter) (u v : V) :
    currentRadicalWord R p (u - v) =
      currentRadicalWord R p u - currentRadicalWord R p v := by
  induction p with
  | nil => rfl
  | cons x p ih =>
      change R.op (radIndex x.1) x.2 (currentRadicalWord R p (u - v)) = _
      rw [ih, map_sub]
      rfl

/-- An adjacent all-mode swap replaces its two letters by one actual
central current at the sum of their modes. -/
theorem current_adjacent_swap (a b : CurrentLetter) (s : List CurrentLetter) :
    currentRadicalWord R (a :: b :: s) w -
      currentRadicalWord R (b :: a :: s) w =
        (contactCoeff a.1 b.1 : ℂ) •
          currentRadicalWord R ((8, a.2 + b.2) :: s) w := by
  have hc := R.comm (radIndex a.1) (radIndex b.1) a.2 b.2
    (currentRadicalWord R s w)
  simpa only [currentRadicalWord, List.map_cons, wordOp, contact_table,
    ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hc

/-- A swap under an arbitrary radical prefix is one contact letter shorter. -/
theorem current_swap_mem (p s : List CurrentLetter) (a b : CurrentLetter) :
    currentRadicalWord R (p ++ a :: b :: s) w -
      currentRadicalWord R (p ++ b :: a :: s) w ∈
        currentPiece R w ((p ++ a :: b :: s).length - 1) := by
  have hb : currentRadicalWord R (a :: b :: s) w -
      currentRadicalWord R (b :: a :: s) w ∈ currentPiece R w (s.length + 1) := by
    rw [current_adjacent_swap]
    apply Submodule.smul_mem
    exact currentRadicalWord_mem R w ((8, a.2 + b.2) :: s) (by simp)
  have hp := current_prefix_mem R w p hb
  rw [currentRadicalWord_sub, ← currentRadicalWord_append,
    ← currentRadicalWord_append] at hp
  exact currentPiece_mono R w (by
    simp only [List.length_append, List.length_cons]
    omega) hp

/-- Any permutation of actual radical currents changes its source vector
by a term of strictly lower contact length, with no source relations. -/
theorem currentRadicalWord_perm_sub {l l' : List CurrentLetter} (h : l.Perm l') :
    currentRadicalWord R l w - currentRadicalWord R l' w ∈
      currentPiece R w (l.length - 1) := by
  induction h with
  | nil =>
      rw [sub_self]
      exact Submodule.zero_mem _
  | @cons a l l' h ih =>
      by_cases hz : l.length = 0
      · have hl : l = [] := List.eq_nil_of_length_eq_zero hz
        have hl' : l' = [] := List.eq_nil_of_length_eq_zero (h.length_eq.symm.trans hz)
        subst l
        subst l'
        rw [sub_self]
        exact Submodule.zero_mem _
      · change R.op (radIndex a.1) a.2 (currentRadicalWord R l w) -
          R.op (radIndex a.1) a.2 (currentRadicalWord R l' w) ∈ _
        rw [← map_sub]
        exact currentPiece_mono R w (by simp only [List.length_cons]; omega)
          (current_radical_mem R w a.1 a.2 ih)
  | swap a b s =>
      simpa only [List.nil_append] using current_swap_mem R w [] s b a
  | @trans l l' l'' h h' ih ih' =>
      have ht : currentRadicalWord R l' w - currentRadicalWord R l'' w ∈
          currentPiece R w (l.length - 1) := by
        rw [h.length_eq]
        exact ih'
      have he : currentRadicalWord R l w - currentRadicalWord R l'' w =
          (currentRadicalWord R l w - currentRadicalWord R l' w) +
            (currentRadicalWord R l' w - currentRadicalWord R l'' w) := by abel
      rw [he]
      exact Submodule.add_mem _ ih ht

/-- A genuinely vanishing reordered source word gives a lower-length
relation for its original order. -/
theorem currentRadicalWord_mem_of_perm_zero {l l' : List CurrentLetter}
    (h : l.Perm l') (hz : currentRadicalWord R l' w = 0) :
    currentRadicalWord R l w ∈ currentPiece R w (l.length - 1) := by
  simpa only [hz, sub_zero] using currentRadicalWord_perm_sub R w h

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.current_adjacent_swap
#print axioms VOA.DeligneAudit.D4FusionContact.currentRadicalWord_perm_sub
#print axioms VOA.DeligneAudit.D4FusionContact.currentRadicalWord_mem_of_perm_zero
