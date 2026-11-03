import VOA.DeligneAudit.D4FusionContactCurrentFiltration
import VOA.DeligneAudit.D4FusionContactCurrentSL2

/-!
# Actual current contact polarization operators

At the top contact length, positive-contact currents replace C_j by
A_(i,j+k). Their brackets with the eight A colors preserve the lower
piece. These are vector/submodule statements, not presumed graded actions.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def currentRoot (i : Fin 8) (r : ℕ) : Module.End ℂ V := R.op (radIndex i.castSucc) r

def currentRaise (i : Fin 8) (r : ℕ) : Module.End ℂ V :=
  (positiveSign i : ℂ) • R.op (positiveIndex i) r

theorem current_center_root_comm (i : Fin 8) (r s : ℕ) :
    currentCenter R r * currentRoot R i s = currentRoot R i s * currentCenter R r := by
  have hc := contact_comm (R := R) i.castSucc 8 s r
  have hz : contactCoeff i.castSucc 8 = 0 := by fin_cases i <;> rfl
  rw [show radIndex 8 = (27 : Fin 28) from rfl, hz, Int.cast_zero, zero_smul] at hc
  exact (sub_eq_zero.mp hc).symm

theorem current_raise_center_comm (i : Fin 8) (r s : ℕ) :
    currentRaise R i r * currentCenter R s - currentCenter R s * currentRaise R i r =
      currentRoot R i (r+s) := by
  ext v
  change (positiveSign i : ℂ) • R.op (positiveIndex i) r (R.op 27 s v) -
    R.op 27 s ((positiveSign i : ℂ) • R.op (positiveIndex i) r v) = _
  rw [map_smul, ← smul_sub, R.comm]
  simp only [Finset.smul_sum, smul_smul, positive_center, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

variable {R} {w : V} {m : ℕ}

theorem current_raise_kills (h : HighestRel R w m) (i : Fin 8) (r : ℕ) :
    currentRaise R i r w = 0 := by
  change (positiveSign i : ℂ) • R.op (positiveIndex i) r w = 0
  rw [h.raising _ (positiveIndex_range i) r, smul_zero]

theorem current_raise_mem (h : HighestRel R w m) (i : Fin 8) (r : ℕ)
    {d : ℕ} {v : V} (hv : v ∈ currentPiece R w d) :
    currentRaise R i r v ∈ currentPiece R w d := by
  change (positiveSign i : ℂ) • R.op (positiveIndex i) r v ∈ currentPiece R w d
  exact Submodule.smul_mem _ _ ((positive_current_piece_invariant h i r d) hv)

theorem current_bracket_root_word_mem (h : HighestRel R w m) (i j : Fin 8)
    (r s : ℕ) (l : List CurrentLetter) :
    currentRaise R i r (currentRoot R j s (currentRadicalWord R l w)) -
      currentRoot R j s (currentRaise R i r (currentRadicalWord R l w)) ∈
        currentPiece R w l.length := by
  change (positiveSign i : ℂ) • R.op (positiveIndex i) r
      (R.op (radIndex j.castSucc) s (currentRadicalWord R l w)) -
    R.op (radIndex j.castSucc) s
      ((positiveSign i : ℂ) • R.op (positiveIndex i) r (currentRadicalWord R l w)) ∈ _
  rw [map_smul, ← smul_sub, R.comm, Finset.smul_sum]
  apply Submodule.sum_mem
  intro c _
  by_cases hz : zeroGrade c
  · obtain ⟨k, rfl⟩ := (zeroGrade_iff_index c).mp hz
    exact Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (zero_current_word_mem h k (r+s) l))
  · rw [positive_rad_table i j c hz, zero_smul, smul_zero]
    exact Submodule.zero_mem _

theorem current_bracket_root_piece_mem (h : HighestRel R w m) (i j : Fin 8)
    (r s : ℕ) {d : ℕ} {v : V} (hv : v ∈ currentPiece R w d) :
    currentRaise R i r (currentRoot R j s v) -
      currentRoot R j s (currentRaise R i r v) ∈ currentPiece R w d := by
  let T : Module.End ℂ V := currentRaise R i r * currentRoot R j s -
    currentRoot R j s * currentRaise R i r
  change T v ∈ currentPiece R w d
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact currentPiece_mono R w hl (current_bracket_root_word_mem h i j r s l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.current_raise_center_comm
#print axioms VOA.DeligneAudit.D4FusionContact.current_bracket_root_piece_mem
