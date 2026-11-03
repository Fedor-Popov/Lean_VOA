import VOA.DeligneAudit.D4FusionContactOperators
import VOA.DeligneAudit.D4FusionContactFiltration

/-! # Actual cubic radical-word reduction from the source center cube -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

theorem center_root_apply (i : Fin 8) (v : V) :
    center R (root R i v) = root R i (center R v) :=
  congrArg (fun T : Module.End ℂ V => T v) (center_root_comm R i)

theorem raise_center_apply (h : HighestRel R w m) (i : Fin 8) :
    raise R i (center R w) = root R i w := by
  have hc := congrArg (fun T : Module.End ℂ V => T w) (raise_center_comm R i)
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, raise_kills h i,
    map_zero, sub_zero] using hc

theorem raise_center_square_apply (h : HighestRel R w m) (i : Fin 8) :
    raise R i (center R (center R w)) = 2 • root R i (center R w) := by
  have hc := congrArg (fun T : Module.End ℂ V => T w) (raise_center_pow R i 1)
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    pow_one, raise_kills h i, map_zero, sub_zero, center_root_apply] using hc

theorem raise_piece_mem (h : HighestRel R w m) (i : Fin 8) {d : ℕ} {v : V}
    (hv : v ∈ piece R w d) : raise R i v ∈ piece R w d := by
  change (positiveSign i : ℂ) • R.op (positiveIndex i) 0 v ∈ piece R w d
  exact Submodule.smul_mem _ _ ((positive_piece_invariant h i d) hv)

theorem bracket_root_word_mem (h : HighestRel R w m) (i j : Fin 8) (l : List (Fin 9)) :
    raise R i (root R j (radicalWord R l w)) -
      root R j (raise R i (radicalWord R l w)) ∈ piece R w l.length := by
  change (positiveSign i : ℂ) •
      R.op (positiveIndex i) 0 (R.op (radIndex j.castSucc) 0 (radicalWord R l w)) -
    R.op (radIndex j.castSucc) 0
      ((positiveSign i : ℂ) • R.op (positiveIndex i) 0 (radicalWord R l w)) ∈ _
  rw [map_smul, ← smul_sub, R.comm, Finset.smul_sum]
  apply Submodule.sum_mem
  intro c _
  by_cases hz : zeroGrade c
  · obtain ⟨k, rfl⟩ := (zeroGrade_iff_index c).mp hz
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (zero_word_mem h k l))
  · rw [positive_rad_table i j c hz, zero_smul, smul_zero]
    exact Submodule.zero_mem _

theorem bracket_root_piece_mem (h : HighestRel R w m) (i j : Fin 8) {d : ℕ} {v : V}
    (hv : v ∈ piece R w d) :
    raise R i (root R j v) - root R j (raise R i v) ∈ piece R w d := by
  let T : Module.End ℂ V := raise R i * root R j - root R j * raise R i
  change T v ∈ piece R w d
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact piece_mono R w hl (bracket_root_word_mem h i j l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

private theorem center_mem_one : center R w ∈ piece R w 1 :=
  radicalWord_mem R w [8] (by decide)

private theorem center_square_mem_two : center R (center R w) ∈ piece R w 2 :=
  radicalWord_mem R w [8, 8] (by decide)

private theorem root_center_mem_two (i : Fin 8) :
    root R i (center R w) ∈ piece R w 2 :=
  radicalWord_mem R w [i.castSucc, 8] (by simp)

theorem root_root_center_mem_two (h : HighestRel R w m)
    (hC : (center R ^ 3) w = 0) (i j : Fin 8) :
    root R i (root R j (center R w)) ∈ piece R w 2 := by
  have hc := bracket_root_piece_mem h j i center_square_mem_two
  have hz : raise R j (root R i (center R (center R w))) = 0 := by
    have hh := congrArg (raise R j) (root_center_square_zero h hC i)
    simpa only [pow_two, Module.End.mul_apply, map_zero] using hh
  rw [hz, zero_sub] at hc
  have hp := Submodule.neg_mem _ hc
  simp only [neg_neg, raise_center_square_apply h j, map_nsmul] at hp
  rw [← Nat.cast_smul_eq_nsmul ℂ] at hp
  exact (Submodule.smul_mem_iff _ (by norm_num : (2 : ℂ) ≠ 0)).mp hp

theorem root_triple_mem_two (h : HighestRel R w m)
    (hC : (center R ^ 3) w = 0) (i j k : Fin 8) :
    root R i (root R j (root R k w)) ∈ piece R w 2 := by
  have htop := raise_piece_mem h k (root_root_center_mem_two h hC i j)
  have hc1 := bracket_root_piece_mem h k i (root_center_mem_two j)
  have hmid := Submodule.sub_mem _ htop hc1
  have he1 : raise R k (root R i (root R j (center R w))) -
      (raise R k (root R i (root R j (center R w))) -
        root R i (raise R k (root R j (center R w)))) =
      root R i (raise R k (root R j (center R w))) := by abel
  rw [he1] at hmid
  have hc2 := bracket_root_piece_mem h k j center_mem_one
  have hp := radical_op_mem R w i.castSucc hc2
  change root R i (raise R k (root R j (center R w)) -
    root R j (raise R k (center R w))) ∈ piece R w 2 at hp
  rw [map_sub, raise_center_apply h k] at hp
  have hs := Submodule.sub_mem _ hmid hp
  have he2 : root R i (raise R k (root R j (center R w))) -
      (root R i (raise R k (root R j (center R w))) - root R i (root R j (root R k w))) =
      root R i (root R j (root R k w)) := by abel
  rwa [he2] at hs

/-- Every actual cubic radical word lies in length at most two.
The only additional relation is the source center cube itself. -/
theorem cubic_mem_two (h : HighestRel R w m) (hC : (center R ^ 3) w = 0)
    (a b c : Fin 9) : radicalWord R [a, b, c] w ∈ piece R w 2 := by
  have hCCC : center R (center R (center R w)) = 0 := by
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply] using hC
  have hACC : ∀ i : Fin 8, root R i (center R (center R w)) ∈ piece R w 2 := by
    intro i
    have hz := root_center_square_zero h hC i
    simp only [pow_two, Module.End.mul_apply] at hz
    rw [hz]
    exact Submodule.zero_mem _
  refine Fin.lastCases ?_ (fun i => ?_) a
  · refine Fin.lastCases ?_ (fun j => ?_) b
    · refine Fin.lastCases ?_ (fun k => ?_) c
      · change center R (center R (center R w)) ∈ piece R w 2
        rw [hCCC]; exact Submodule.zero_mem _
      · change center R (center R (root R k w)) ∈ piece R w 2
        simpa only [center_root_apply] using hACC k
    · refine Fin.lastCases ?_ (fun k => ?_) c
      · change center R (root R j (center R w)) ∈ piece R w 2
        simpa only [center_root_apply] using hACC j
      · change center R (root R j (root R k w)) ∈ piece R w 2
        simpa only [center_root_apply] using root_root_center_mem_two h hC j k
  · refine Fin.lastCases ?_ (fun j => ?_) b
    · refine Fin.lastCases ?_ (fun k => ?_) c
      · exact hACC i
      · change root R i (center R (root R k w)) ∈ piece R w 2
        simpa only [center_root_apply] using root_root_center_mem_two h hC i k
    · refine Fin.lastCases ?_ (fun k => ?_) c
      · exact root_root_center_mem_two h hC i j
      · exact root_triple_mem_two h hC i j k

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.root_root_center_mem_two
#print axioms VOA.DeligneAudit.D4FusionContact.root_triple_mem_two
#print axioms VOA.DeligneAudit.D4FusionContact.cubic_mem_two
