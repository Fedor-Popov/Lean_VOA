import VOA.DeligneAudit.D4FusionContactCore
import VOA.DeligneAudit.D4FusionContactGradingTable

/-! # The actual radical-word filtration and its zero-grade invariance -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def radicalWord (l : List (Fin 9)) (w : V) : V :=
  wordOp R (l.map fun i => (radIndex i, 0)) w

def piece (w : V) (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ l : List (Fin 9), l.length ≤ d ∧ u = radicalWord R l w}

theorem radicalWord_mem (w : V) (l : List (Fin 9)) {d : ℕ} (hl : l.length ≤ d) :
    radicalWord R l w ∈ piece R w d := Submodule.subset_span ⟨l, hl, rfl⟩

theorem generator_mem (w : V) (d : ℕ) : w ∈ piece R w d :=
  radicalWord_mem R w [] (by simp)

theorem piece_mono (w : V) {d e : ℕ} (hde : d ≤ e) : piece R w d ≤ piece R w e := by
  apply Submodule.span_le.mpr
  rintro u ⟨l, hl, rfl⟩
  exact radicalWord_mem R w l (hl.trans hde)

theorem radical_op_mem (w : V) (i : Fin 9) {d : ℕ} {v : V} (hv : v ∈ piece R w d) :
    R.op (radIndex i) 0 v ∈ piece R w (d + 1) := by
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact radicalWord_mem R w (i :: l) (by simp only [List.length_cons]; omega)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

variable {R} {w : V} {m : ℕ}

/-- Every zero-grade generator preserves the actual radical length
filtration. Its action on the highest vector is derived from the
source relations, not supplied as a separate filtration premise. -/
theorem zero_word_mem (h : HighestRel R w m) (i : Fin 10) (l : List (Fin 9)) :
    R.op (zeroIndex i) 0 (radicalWord R l w) ∈ piece R w l.length := by
  induction l with
  | nil =>
      have hc : ¬ active (zeroIndex i) :=
        zeroGrade_nonactive _ ((zeroGrade_iff_index _).mpr ⟨i, rfl⟩)
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (nonactive_hw h _ 0 hc).1
      change R.op (zeroIndex i) 0 w ∈ piece R w 0
      rw [← ha]
      exact Submodule.smul_mem _ a (generator_mem R w 0)
  | cons j l ih =>
      change R.op (zeroIndex i) 0 (R.op (radIndex j) 0 (radicalWord R l w)) ∈
        piece R w (l.length + 1)
      have hc := R.comm (zeroIndex i) (radIndex j) 0 0 (radicalWord R l w)
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro c _
        by_cases hca : active c
        · obtain ⟨k, rfl⟩ := (active_iff_index c).mp hca
          exact Submodule.smul_mem _ _ (radicalWord_mem R w (k :: l) (by simp))
        · rw [zero_rad_table i j c hca, zero_smul]
          exact Submodule.zero_mem _
      · exact radical_op_mem R w j ih

theorem zero_piece_invariant (h : HighestRel R w m) (i : Fin 10) (d : ℕ) :
    piece R w d ≤ (piece R w d).comap (R.op (zeroIndex i) 0) := by
  intro v hv
  change R.op (zeroIndex i) 0 v ∈ piece R w d
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact piece_mono R w hl (zero_word_mem h i l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

private theorem positive_support (i : Fin 8) (j : Fin 9) (c : Fin 28)
    (hc : ¬ active c) (hz : ¬ zeroGrade c) :
    contactF (positiveIndex i) (radIndex j) c = 0 := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change contactF (positiveIndex i) 27 c = 0
    have hh := positive_center i c
    have hci : c ≠ radIndex i.castSucc := by
      intro he
      subst c
      exact hc ((active_iff_index _).mpr ⟨i.castSucc, rfl⟩)
    rw [if_neg hci] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by fin_cases i <;> norm_num [positiveSign])
  · exact positive_rad_table i k c hz

/-- Positive contact roots preserve the actual radical length
filtration: their brackets have one radical term or a zero-grade term,
and the latter already preserves each lower filtration piece. -/
theorem positive_word_mem (h : HighestRel R w m) (i : Fin 8) (l : List (Fin 9)) :
    R.op (positiveIndex i) 0 (radicalWord R l w) ∈ piece R w l.length := by
  induction l with
  | nil =>
      change R.op (positiveIndex i) 0 w ∈ piece R w 0
      rw [h.raising _ (positiveIndex_range i) 0]
      exact Submodule.zero_mem _
  | cons j l ih =>
      change R.op (positiveIndex i) 0 (R.op (radIndex j) 0 (radicalWord R l w)) ∈
        piece R w (l.length + 1)
      have hh := R.comm (positiveIndex i) (radIndex j) 0 0 (radicalWord R l w)
      rw [sub_eq_iff_eq_add] at hh
      rw [hh]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro c _
        by_cases hca : active c
        · obtain ⟨k, rfl⟩ := (active_iff_index c).mp hca
          exact Submodule.smul_mem _ _ (radicalWord_mem R w (k :: l) (by simp))
        · by_cases hcz : zeroGrade c
          · obtain ⟨k, rfl⟩ := (zeroGrade_iff_index c).mp hcz
            exact Submodule.smul_mem _ _
              (piece_mono R w (by omega) (zero_word_mem h k l))
          · rw [positive_support i j c hca hcz, zero_smul]
            exact Submodule.zero_mem _
      · exact radical_op_mem R w j ih

theorem positive_piece_invariant (h : HighestRel R w m) (i : Fin 8) (d : ℕ) :
    piece R w d ≤ (piece R w d).comap (R.op (positiveIndex i) 0) := by
  intro v hv
  change R.op (positiveIndex i) 0 v ∈ piece R w d
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact piece_mono R w hl (positive_word_mem h i l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.zero_word_mem
#print axioms VOA.DeligneAudit.D4FusionContact.zero_piece_invariant
#print axioms VOA.DeligneAudit.D4FusionContact.positive_piece_invariant
