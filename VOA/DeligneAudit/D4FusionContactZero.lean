import VOA.DeligneAudit.D4FusionContactTruncation

/-! # The actual D₄ multiplicity-zero source bound -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorGraded
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V}

theorem localWeyl_zero_kills (h : LocalWeylRelG D4sector R w 0) :
    ∀ (c : Fin 28) r, R.op c r w = 0 := by
  have hH := highestRel_of_localWeyl h
  intro c r
  by_cases hc : c.val < 4
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hH.cartan_zero c hc
    · exact hH.cartan_pos c hc r hr
  by_cases he : c.val < 16
  · exact hH.raising c (by omega) r
  obtain ⟨i, rfl⟩ := negativeIndex_covers c (by omega)
  exact negative_high_zero hH (fun i => h.fusion _ (negativeIndex_range i)) i r (by omega)

private theorem zero_word (h : LocalWeylRelG D4sector R w 0)
    (c : Fin 28) (r : ℕ) (l : List (Fin 28 × ℕ)) : wordOp R ((c,r)::l) w = 0 := by
  exact wordOp_eq_zero_of_mem R (contact_truncIdeal 0)
    (fun a n _ => localWeyl_zero_kills h a n) ((c,r)::l) ⟨(c,r), by simp, by omega⟩

theorem localWeyl_zero_degree_le (h : LocalWeylRelG D4sector R w 0) :
    cycDeg R w 0 ≤ Submodule.span ℂ ({w} : Set V) := by
  rw [cycDeg, Submodule.span_le]
  rintro _ ⟨l, _, rfl⟩
  cases l with
  | nil =>
      change w ∈ Submodule.span ℂ ({w} : Set V)
      exact Submodule.subset_span (by simp)
  | cons x l =>
      rw [zero_word h x.1 x.2 l]
      exact Submodule.zero_mem _

theorem localWeyl_zero_cycDeg_eq_bot (h : LocalWeylRelG D4sector R w 0)
    (d : ℕ) (hd : 1 ≤ d) : cycDeg R w d = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [cycDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  cases l with
  | nil => have : d = 0 := hl.symm; omega
  | cons x l => rw [zero_word h x.1 x.2 l]; exact Submodule.zero_mem _

theorem localWeyl_zero_degree_bound (h : LocalWeylRelG D4sector R w 0) :
    FiniteDimensional ℂ (cycDeg R w 0) ∧ Module.finrank ℂ (cycDeg R w 0) ≤ 1 := by
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ({w} : Set V)) := inferInstance
  have hle := localWeyl_zero_degree_le h
  haveI : FiniteDimensional ℂ (cycDeg R w 0) := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, (Submodule.finrank_mono hle).trans ?_⟩
  simpa using finrank_span_le_card ({w} : Set V)

theorem localWeyl_zero_total_dim (h : LocalWeylRelG D4sector R w 0) (B : ℕ) :
    ∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d) ≤ 1 := by
  classical
  by_cases hB : B = 0
  · subst B
    simp
  calc
    _ = Module.finrank ℂ (cycDeg R w 0) := by
      apply Finset.sum_eq_single 0
      · intro d _ hd
        rw [localWeyl_zero_cycDeg_eq_bot h d (by omega)]
        simp
      · intro hz
        exact False.elim (hz (Finset.mem_range.mpr (by omega)))
    _ ≤ 1 := (localWeyl_zero_degree_bound h).2

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_zero_degree_bound
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_zero_total_dim
