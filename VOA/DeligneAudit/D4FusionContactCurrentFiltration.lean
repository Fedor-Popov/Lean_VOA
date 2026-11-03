import VOA.DeligneAudit.D4FusionContactCore
import VOA.DeligneAudit.D4FusionContactGradingTable

/-!
# D₄ contact length with arbitrary current modes

This filtration counts radical letters, independently of their current
modes. Zero-grade and positive-contact currents preserve it by the actual
source relations and bracket table. No dimension bound is assumed.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

abbrev CurrentLetter := Fin 9 × ℕ

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def currentRadicalWord (l : List CurrentLetter) (w : V) : V :=
  wordOp R (l.map fun x => (radIndex x.1, x.2)) w

def currentPiece (w : V) (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ l : List CurrentLetter, l.length ≤ d ∧
    u = currentRadicalWord R l w}

theorem currentRadicalWord_mem (w : V) (l : List CurrentLetter) {d : ℕ}
    (hl : l.length ≤ d) : currentRadicalWord R l w ∈ currentPiece R w d :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem current_generator_mem (w : V) (d : ℕ) : w ∈ currentPiece R w d :=
  currentRadicalWord_mem R w [] (by simp)

theorem currentPiece_mono (w : V) {d e : ℕ} (hde : d ≤ e) :
    currentPiece R w d ≤ currentPiece R w e := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  exact currentRadicalWord_mem R w l (hl.trans hde)

theorem current_radical_mem (w : V) (i : Fin 9) (r : ℕ) {d : ℕ} {v : V}
    (hv : v ∈ currentPiece R w d) : R.op (radIndex i) r v ∈ currentPiece R w (d + 1) := by
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact currentRadicalWord_mem R w ((i,r) :: l) (by simp only [List.length_cons]; omega)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

/-- A radical prefix raises the length bound by its number of letters. -/
theorem current_prefix_mem (w : V) (l : List CurrentLetter) {d : ℕ} {v : V}
    (hv : v ∈ currentPiece R w d) :
    currentRadicalWord R l v ∈ currentPiece R w (l.length + d) := by
  induction l with
  | nil => simpa [currentRadicalWord, wordOp] using hv
  | cons x l ih =>
      exact currentPiece_mono R w (by simp only [List.length_cons]; omega)
        (current_radical_mem R w x.1 x.2 ih)

variable {R} {w : V} {m : ℕ}

theorem zero_current_word_mem (h : HighestRel R w m) (i : Fin 10) (k : ℕ)
    (l : List CurrentLetter) :
    R.op (zeroIndex i) k (currentRadicalWord R l w) ∈ currentPiece R w l.length := by
  induction l with
  | nil =>
      have hc : ¬ active (zeroIndex i) :=
        zeroGrade_nonactive _ ((zeroGrade_iff_index _).mpr ⟨i, rfl⟩)
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (nonactive_hw h _ k hc).1
      change R.op (zeroIndex i) k w ∈ currentPiece R w 0
      rw [← ha]
      exact Submodule.smul_mem _ a (current_generator_mem R w 0)
  | cons j l ih =>
      change R.op (zeroIndex i) k
        (R.op (radIndex j.1) j.2 (currentRadicalWord R l w)) ∈
        currentPiece R w (l.length + 1)
      have hc := R.comm (zeroIndex i) (radIndex j.1) k j.2 (currentRadicalWord R l w)
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro c _
        by_cases hca : active c
        · obtain ⟨t, rfl⟩ := (active_iff_index c).mp hca
          exact Submodule.smul_mem _ _
            (currentRadicalWord_mem R w ((t,k+j.2)::l) (by simp))
        · rw [zero_rad_table i j.1 c hca, zero_smul]
          exact Submodule.zero_mem _
      · exact current_radical_mem R w j.1 j.2 ih

theorem zero_current_piece_invariant (h : HighestRel R w m) (i : Fin 10) (k d : ℕ) :
    currentPiece R w d ≤ (currentPiece R w d).comap (R.op (zeroIndex i) k) := by
  intro v hv
  change R.op (zeroIndex i) k v ∈ currentPiece R w d
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact currentPiece_mono R w hl (zero_current_word_mem h i k l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

private theorem current_positive_support (i : Fin 8) (j : Fin 9) (c : Fin 28)
    (hc : ¬ active c) (hz : ¬ zeroGrade c) :
    contactF (positiveIndex i) (radIndex j) c = 0 := by
  refine Fin.lastCases ?_ (fun t => ?_) j
  · change contactF (positiveIndex i) 27 c = 0
    have hh := positive_center i c
    have hci : c ≠ radIndex i.castSucc := by
      intro he
      subst c
      exact hc ((active_iff_index _).mpr ⟨i.castSucc, rfl⟩)
    rw [if_neg hci] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by fin_cases i <;> norm_num [positiveSign])
  · exact positive_rad_table i t c hz

theorem positive_current_word_mem (h : HighestRel R w m) (i : Fin 8) (k : ℕ)
    (l : List CurrentLetter) :
    R.op (positiveIndex i) k (currentRadicalWord R l w) ∈ currentPiece R w l.length := by
  induction l with
  | nil =>
      change R.op (positiveIndex i) k w ∈ currentPiece R w 0
      rw [h.raising _ (positiveIndex_range i) k]
      exact Submodule.zero_mem _
  | cons j l ih =>
      change R.op (positiveIndex i) k
        (R.op (radIndex j.1) j.2 (currentRadicalWord R l w)) ∈
        currentPiece R w (l.length + 1)
      have hc := R.comm (positiveIndex i) (radIndex j.1) k j.2 (currentRadicalWord R l w)
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro c _
        by_cases hca : active c
        · obtain ⟨t, rfl⟩ := (active_iff_index c).mp hca
          exact Submodule.smul_mem _ _
            (currentRadicalWord_mem R w ((t,k+j.2)::l) (by simp))
        · by_cases hcz : zeroGrade c
          · obtain ⟨t, rfl⟩ := (zeroGrade_iff_index c).mp hcz
            exact Submodule.smul_mem _ _ (currentPiece_mono R w (by omega)
              (zero_current_word_mem h t (k+j.2) l))
          · rw [current_positive_support i j.1 c hca hcz, zero_smul]
            exact Submodule.zero_mem _
      · exact current_radical_mem R w j.1 j.2 ih

theorem positive_current_piece_invariant (h : HighestRel R w m) (i : Fin 8) (k d : ℕ) :
    currentPiece R w d ≤ (currentPiece R w d).comap (R.op (positiveIndex i) k) := by
  intro v hv
  change R.op (positiveIndex i) k v ∈ currentPiece R w d
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact currentPiece_mono R w hl (positive_current_word_mem h i k l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.zero_current_piece_invariant
#print axioms VOA.DeligneAudit.D4FusionContact.positive_current_piece_invariant
