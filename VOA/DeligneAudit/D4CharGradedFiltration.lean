import VOA.DeligneAudit.D4CharGradedKeys

/-! The finite key filtration in each exact degree, and its dimension telescoping formula. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 D4Levi LeviKeyFiltration

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Intersect the ordered key filtration with the requested exact current degree. -/
def gradedKeyPrefix (ρ : CurrentModule D4sector.f V) (w : V) (n N i : ℕ) :
    Submodule ℂ V := cycDeg ρ w N ⊓ keyPrefix ρ w n i

theorem gradedKeyPrefix_zero (ρ : CurrentModule D4sector.f V) (w : V) (n N : ℕ) :
    gradedKeyPrefix ρ w n N 0 = ⊥ := by
  simp [gradedKeyPrefix, keyPrefix_zero]

theorem gradedKeyPrefix_mono (ρ : CurrentModule D4sector.f V) (w : V) (n N i : ℕ)
    (hi : i < (globalKeyBox n).card) :
    gradedKeyPrefix ρ w n N i ≤ gradedKeyPrefix ρ w n N (i + 1) :=
  inf_le_inf le_rfl (keyPrefix_mono ρ w n i hi)

theorem gradedKeyPrefix_top (n : ℕ) (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N : ℕ) :
    gradedKeyPrefix ρ w n N (globalKeyBox n).card = cycDeg ρ w N := by
  rw [gradedKeyPrefix, keyPrefix_top ρ w n h]
  exact inf_eq_left.mpr (d4_cycDeg_le_cyclic ρ w N)

theorem gradedKeyPrefix_finite (n : ℕ) (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N i : ℕ) :
    FiniteDimensional ℂ (gradedKeyPrefix ρ w n N i) := by
  haveI := d4_cycDeg_finite n ρ w h N
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (show gradedKeyPrefix ρ w n N i ≤ cycDeg ρ w N from inf_le_left))
    (Submodule.inclusion_injective _)

/-- On the universal module, degree projection preserves every key prefix. -/
theorem projUG_keyPrefix (R : RelSpec 28) (n N i : ℕ) :
    (keyPrefix (univRepG D4sector.f R) (wUG D4sector.f R) n i).map
      (projUG D4sector.f R N) =
        gradedKeyPrefix (univRepG D4sector.f R) (wUG D4sector.f R) n N i := by
  apply le_antisymm
  · simp only [keyPrefix, Submodule.map_iSup, projUG_keyOrbit]
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact (gradedKeyOrbit_le _ _ _ _).trans
      (inf_le_inf le_rfl (le_iSup_of_le j (le_iSup_of_le hj le_rfl)))
  · intro v hv
    exact ⟨v, hv.2, projUG_cyc D4sector.f R N hv.1⟩

/-- There is no loss of grading when adding the next key orbit in the universal module. -/
theorem gradedKeyPrefix_univ_step (R : RelSpec 28) (n N i : ℕ)
    (hi : i < (globalKeyBox n).card) :
    gradedKeyPrefix (univRepG D4sector.f R) (wUG D4sector.f R) n N (i + 1) =
      gradedKeyPrefix (univRepG D4sector.f R) (wUG D4sector.f R) n N i ⊔
        gradedKeyOrbit (univRepG D4sector.f R) (wUG D4sector.f R)
          (keyEnum n ⟨i, hi⟩) N := by
  rw [← projUG_keyPrefix R n N (i + 1), keyPrefix_step _ _ n i hi]
  rw [Submodule.map_sup, projUG_keyPrefix, projUG_keyOrbit]

/-- The exact degree has exactly the sum of the ranks of its finite graded key quotients.
The sharp type-A bounds on these quotients are the remaining L1 input. -/
theorem d4_degree_finrank_eq_steps (n : ℕ) (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N : ℕ) :
    Module.finrank ℂ (cycDeg ρ w N) =
      ∑ i ∈ Finset.range (globalKeyBox n).card,
        Module.finrank ℂ (StepQuot (gradedKeyPrefix ρ w n N) i) := by
  let F := gradedKeyPrefix ρ w n N
  have hf (i : ℕ) : FiniteDimensional ℂ (F i) := gradedKeyPrefix_finite n ρ w h N i
  have hs (i : ℕ) (hi : i < (globalKeyBox n).card) :
      Module.finrank ℂ (F (i + 1)) =
        Module.finrank ℂ (F i) + Module.finrank ℂ (StepQuot F i) := by
    let T : Submodule ℂ (F (i + 1)) := (F i).comap (F (i + 1)).subtype
    have hm : T.map (F (i + 1)).subtype = F i := by
      exact (Submodule.map_comap_subtype (p := F (i + 1)) (p' := F i)).trans
        (inf_eq_right.mpr (gradedKeyPrefix_mono ρ w n N i hi))
    have he : Module.finrank ℂ T = Module.finrank ℂ (F i) := by
      rw [← Submodule.finrank_map_subtype_eq, hm]
    haveI := hf (i + 1)
    calc
      _ = Module.finrank ℂ (StepQuot F i) + Module.finrank ℂ T :=
        T.finrank_quotient_add_finrank.symm
      _ = _ := by rw [he, Nat.add_comm]
  have hp (j : ℕ) (hj : j ≤ (globalKeyBox n).card) :
      Module.finrank ℂ (F j) =
        ∑ i ∈ Finset.range j, Module.finrank ℂ (StepQuot F i) := by
    induction j with
    | zero => simp [F, gradedKeyPrefix_zero]
    | succ j ih =>
        rw [Finset.sum_range_succ, hs j (by omega), ih (by omega)]
  have hh := hp (globalKeyBox n).card le_rfl
  have ht : F (globalKeyBox n).card = cycDeg ρ w N := gradedKeyPrefix_top n ρ w h N
  rw [ht] at hh
  exact hh

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gradedKeyPrefix_zero
#print axioms VOA.DeligneAudit.D4Char.gradedKeyPrefix_mono
#print axioms VOA.DeligneAudit.D4Char.gradedKeyPrefix_top
#print axioms VOA.DeligneAudit.D4Char.gradedKeyPrefix_finite
#print axioms VOA.DeligneAudit.D4Char.projUG_keyPrefix
#print axioms VOA.DeligneAudit.D4Char.gradedKeyPrefix_univ_step
#print axioms VOA.DeligneAudit.D4Char.d4_degree_finrank_eq_steps
