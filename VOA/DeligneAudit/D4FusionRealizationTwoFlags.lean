import VOA.DeligneAudit.D4FusionRealizationTwoSpanning

/-! The certified actual basis gives the genuine current-degree source flag. -/
namespace VOA.DeligneAudit.D4Two
open Certificate VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.D1TensorG.Gr
noncomputable section

def wordLevel (i : Fin 841) : ℕ := (wordNode i).level

theorem actualBasis_critical (c : Fin 28) (k : ℕ) (i : Fin 841)
    (ha : wordLevel i + k < 4) :
    sourceRep.op c k (actualBasis i) ∈ flag actualBasis wordLevel (wordLevel i + k) := by
  rw [actualBasis_apply]
  have hk : k < 4 := by omega
  apply source_action_mem (flag actualBasis wordLevel (wordLevel i+k)) c k hk i
  intro p hp
  have hcheck := action_check c k hk i
  have hb := fullAction_target_bound actionCase (actionIndex c k i) hcheck p hp
  have hcrit : (wordNode (actionSource (actionIndex c k i))).level +
      actionMode (actionIndex c k i) < 4 := by
    rw [actionIndex_source c k i i.isLt,actionIndex_mode c k i c.isLt i.isLt]
    exact ha
  have hl := fullAction_target_level actionCase (actionIndex c k i) hcheck hcrit p hp
  rw [actionIndex_source c k i i.isLt,actionIndex_mode c k i c.isLt i.isLt] at hl
  refine Submodule.subset_span ⟨(⟨p.1,hb⟩ : Fin 841),hl,?_⟩
  rw [actualBasis_apply]
  rfl

theorem source_generator_mem_flag : sourceGenerator ∈ flag actualBasis wordLevel 0 := by
  refine Submodule.subset_span ⟨(0 : Fin 841),?_,?_⟩
  · change 0 ≤ 0
    exact Nat.zero_le _
  · apply (flatCoordinates 28).injective
    rw [actualBasis_apply]
    simpa only [wordVector,LinearEquiv.apply_symm_apply] using flat_source_generator

theorem actualBasis_words (i : Fin 841) :
    ∃ l : List (Fin 28 × ℕ), degree l = wordLevel i ∧
      actualBasis i = wordOp sourceRep l sourceGenerator := by
  rw [actualBasis_apply]
  exact wordVector_word i

/-- Equality with the genuine filtration, with no rank or flag premise. -/
theorem source_Fbelow_eq_flag (d : ℕ) :
    Fbelow sourceRep sourceGenerator (d+1) = flag actualBasis wordLevel d :=
  Fbelow_eq_flag sourceRep sourceGenerator actualBasis wordLevel 4
    (fun i => wordNode_level i i.isLt) actualBasis_critical
    source_generator_mem_flag actualBasis_words d

theorem source_Fbelow_finrank (d : ℕ) :
    Module.finrank ℂ (Fbelow sourceRep sourceGenerator (d+1)) =
      Fintype.card {i : Fin 841 // wordLevel i ≤ d} := by
  rw [source_Fbelow_eq_flag]
  exact finrank_flag actualBasis wordLevel d

end
#print axioms source_Fbelow_eq_flag
#print axioms source_Fbelow_finrank
end VOA.DeligneAudit.D4Two
