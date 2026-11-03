import VOA.DeligneAudit.D4FusionContactCurrentPolarization

/-! # A-current words and their lower-length raising commutators -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

abbrev ACurrentLetter := Fin 8 × ℕ

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def currentAWord : List ACurrentLetter → Module.End ℂ V
  | [] => 1
  | x :: l => currentRoot R x.1 x.2 * currentAWord l

theorem currentAWord_eq (l : List ACurrentLetter) (v : V) :
    currentAWord R l v =
      currentRadicalWord R (l.map fun x => (x.1.castSucc, x.2)) v := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change currentRoot R x.1 x.2 (currentAWord R l v) =
        currentRoot R x.1 x.2
          (currentRadicalWord R (l.map fun x => (x.1.castSucc, x.2)) v)
      exact congrArg (currentRoot R x.1 x.2) ih

theorem currentAWord_mem (w : V) (l : List ACurrentLetter) {d : ℕ} {v : V}
    (hv : v ∈ currentPiece R w d) : currentAWord R l v ∈ currentPiece R w (l.length+d) := by
  rw [currentAWord_eq]
  simpa only [List.length_map] using
    current_prefix_mem R w (l.map fun x => (x.1.castSucc,x.2)) hv

theorem current_center_AWord_comm (r : ℕ) (l : List ACurrentLetter) :
    currentCenter R r * currentAWord R l = currentAWord R l * currentCenter R r := by
  induction l with
  | nil => simp only [currentAWord, mul_one, one_mul]
  | cons x l ih =>
      simp only [currentAWord]
      rw [← mul_assoc, current_center_root_comm, mul_assoc, ih, ← mul_assoc]

variable {R} {w : V} {m : ℕ}

theorem current_raise_AWord_mem (h : HighestRel R w m) (i : Fin 8) (r : ℕ)
    (l : List ACurrentLetter) {d : ℕ} {v : V} (hv : v ∈ currentPiece R w d) :
    currentRaise R i r (currentAWord R l v) -
      currentAWord R l (currentRaise R i r v) ∈ currentPiece R w (d+l.length-1) := by
  induction l with
  | nil =>
      change currentRaise R i r v - currentRaise R i r v ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
  | cons x l ih =>
      have he : currentRaise R i r (currentAWord R (x::l) v) -
          currentAWord R (x::l) (currentRaise R i r v) =
          (currentRaise R i r (currentRoot R x.1 x.2 (currentAWord R l v)) -
            currentRoot R x.1 x.2 (currentRaise R i r (currentAWord R l v))) +
          currentRoot R x.1 x.2 (currentRaise R i r (currentAWord R l v) -
            currentAWord R l (currentRaise R i r v)) := by
        simp only [currentAWord, Module.End.mul_apply, map_sub]
        abel
      rw [he]
      have ht : d+(x::l).length-1 = d+l.length := by simp only [List.length_cons]; omega
      rw [ht]
      apply Submodule.add_mem
      · exact currentPiece_mono R w (by omega)
          (current_bracket_root_piece_mem h i x.1 r x.2 (currentAWord_mem R w l hv))
      · by_cases hz : d+l.length = 0
        · have hl : l = [] := List.length_eq_zero_iff.mp (by omega)
          subst l
          simp only [currentAWord, Module.End.one_apply, sub_self, map_zero]
          exact Submodule.zero_mem _
        · exact currentPiece_mono R w (by omega)
            (current_radical_mem R w x.1.castSucc x.2 ih)

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.current_raise_AWord_mem
