import VOA.DeligneAudit.D4FusionContactPolynomialDerivationActionCore

/-! Actual zero-grade current actions and their one-letter derivation rule
on the restricted PBW graded cyclic module. Only HighestRel is assumed. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl

noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

private theorem radical_index_injective : Function.Injective radIndex := by decide +kernel

private theorem g0_sum_radical (g : Fin 10) (i : Fin 9) (r : ℕ) (v : V) :
    (∑ c : Fin 28, contactF (zeroIndex g) (radIndex i) c • R.op c r v) =
      ∑ t : Fin 9, contactF (zeroIndex g) (radIndex i) (radIndex t) •
        R.op (radIndex t) r v := by
  classical
  have hs : (∑ c : Fin 28, contactF (zeroIndex g) (radIndex i) c • R.op c r v) =
      ∑ c ∈ Finset.univ.image radIndex,
        contactF (zeroIndex g) (radIndex i) c • R.op c r v := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    have hna : ¬ active c := by
      intro ha
      obtain ⟨t, rfl⟩ := (active_iff_index c).mp ha
      exact hc (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
    rw [zero_rad_table g i c hna, zero_smul]
  rw [hs, Finset.sum_image]
  intro a _ b _ hab
  exact radical_index_injective hab

/-- The actual g0/radical commutator has precisely the nine radical terms. -/
theorem g0_current_comm (g : Fin 10) (i : Fin 9) (k r : ℕ) :
    R.op (zeroIndex g) k * R.op (radIndex i) r -
      R.op (radIndex i) r * R.op (zeroIndex g) k =
      ∑ t : Fin 9, contactF (zeroIndex g) (radIndex i) (radIndex t) •
        R.op (radIndex t) (k + r) := by
  ext v
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, g0_sum_radical R g i (k+r) v] using
      R.comm (zeroIndex g) (radIndex i) k r v

variable {R} {w : V} {m : ℕ}

/-- The actual zero-grade current descends without changing PBW length,
and is restricted to actual cyclic symbols. -/
def g0Gr (h : HighestRel R w m) (g : Fin 10) (k : ℕ) : Module.End ℂ (Gr R w) :=
  grPreservingOp R w (R.op (zeroIndex g) k)
    (fun n => zero_current_piece_invariant h g k n)

/-- Every g0 current has an actual scalar eigenvalue on the cyclic generator. -/
theorem g0Gr_generator_eigen (h : HighestRel R w m) (g : Fin 10) (k : ℕ) :
    ∃ a : ℂ, g0Gr h g k (grGenerator R w) = a • grGenerator R w := by
  have hna : ¬ active (zeroIndex g) :=
    zeroGrade_nonactive _ ((zeroGrade_iff_index _).mpr ⟨g, rfl⟩)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (nonactive_hw h _ k hna).1
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change (grPreservingOp R w (R.op (zeroIndex g) k)
    (fun n => zero_current_piece_invariant h g k n) (grWord R w []) : AmbientGr R w) = _
  rw [grPreservingOp_grWord]
  change symbol R w 0 (R.op (zeroIndex g) k w) = a • symbol R w 0 w
  rw [← ha, map_smul]

/-- Positive modes of g0 kill the generator, by the actual source relations. -/
theorem g0Gr_generator_pos (h : HighestRel R w m) (g : Fin 10) (k : ℕ) (hk : 1 ≤ k) :
    g0Gr h g k (grGenerator R w) = 0 := by
  have hna : ¬ active (zeroIndex g) :=
    zeroGrade_nonactive _ ((zeroGrade_iff_index _).mpr ⟨g, rfl⟩)
  have hz := (nonactive_hw h (zeroIndex g) k hna).2 hk
  apply Subtype.ext
  change (grPreservingOp R w (R.op (zeroIndex g) k)
    (fun n => zero_current_piece_invariant h g k n) (grWord R w []) : AmbientGr R w) = 0
  rw [grPreservingOp_grWord]
  change symbol R w 0 (R.op (zeroIndex g) k w) = 0
  rw [hz, map_zero]

/-- The g0 action replaces one radical current by its checked linear
combination, with the source current modes added. -/
theorem g0Gr_comm (h : HighestRel R w m) (g : Fin 10) (i : Fin 9) (k r : ℕ) :
    g0Gr h g k * grOp R w i r - grOp R w i r * g0Gr h g k =
      ∑ t : Fin 9, contactF (zeroIndex g) (radIndex i) (radIndex t) •
        grOp R w t (k + r) := by
  apply LinearMap.ext_on_range (grWord_span_top R w)
  intro l
  apply Subtype.ext
  change (((grPreservingOp R w (R.op (zeroIndex g) k)
    (fun n => zero_current_piece_invariant h g k n) * grOp R w i r -
      grOp R w i r * grPreservingOp R w (R.op (zeroIndex g) k)
        (fun n => zero_current_piece_invariant h g k n)) (grWord R w l)) : AmbientGr R w) = _
  rw [grPreservingOp_comm_word]
  have hc := congrArg (fun T : Module.End ℂ V => T (nword R w l))
    (g0_current_comm R g i k r)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at hc
  rw [hc, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, grOp_grWord]
  rfl

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.g0Gr_generator_eigen
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.g0Gr_comm
