import VOA.DeligneAudit.D4FusionRealizationTwoModel
import VOA.DeligneAudit.DeligneFusionD1TensorGGrCore

/-! Every checked word vector is an actual source word of its certified degree. -/
namespace VOA.DeligneAudit.D4Two
open Certificate VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.D1TensorG.Gr
noncomputable section

def wordParent (i : Fin 841) (hi : i.val ≠ 0) : Fin 841 :=
  ⟨(wordNode i).parent,(wordNode_parent i i.isLt hi).1.trans i.isLt⟩

theorem wordParent_lt (i : Fin 841) (hi : i.val ≠ 0) : (wordParent i hi).val < i.val :=
  (wordNode_parent i i.isLt hi).1

def wordColor (i : Fin 841) (hi : i.val ≠ 0) : Fin 28 :=
  ⟨(wordNode i).color,(wordNode_parent i i.isLt hi).2.1⟩

def wordWitness (i : Fin 841) : List (Fin 28 × ℕ) :=
  if hi : i.val = 0 then [] else
    (wordColor i hi,(wordNode i).mode) :: wordWitness (wordParent i hi)
termination_by i.val
decreasing_by exact wordParent_lt _ _

theorem wordWitness_degree (i : Fin 841) :
    degree (wordWitness i) = (wordNode i).level := by
  refine (measure (fun i : Fin 841 => i.val)).wf.induction
    (C := fun j => degree (wordWitness j) = (wordNode j).level) i ?_
  intro j ih
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    rw [wordWitness,dif_pos hj]
    rfl
  · rw [wordWitness,dif_neg hj,degree_cons,ih (wordParent j hj) (wordParent_lt j hj)]
    have h := (wordNode_parent j j.isLt hj).2.2.1
    change (wordNode j).mode + (wordNode (wordNode j).parent).level = (wordNode j).level
    omega

theorem flat_wordWitness (i : Fin 841) :
    flatCoordinates 28 (wordOp sourceRep (wordWitness i) sourceGenerator) =
      vec 841 (wordNode i).vector := by
  refine (measure (fun i : Fin 841 => i.val)).wf.induction
    (C := fun j => flatCoordinates 28 (wordOp sourceRep (wordWitness j) sourceGenerator) =
      vec 841 (wordNode j).vector) i ?_
  intro j ih
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    rw [wordWitness,dif_pos hj]
    exact flat_source_generator
  · rw [wordWitness,dif_neg hj]
    change flatCoordinates 28 (sourceRep.op (wordColor j hj) (wordNode j).mode
      (wordOp sourceRep (wordWitness (wordParent j hj)) sourceGenerator)) = _
    rw [source_flat_current,ih (wordParent j hj) (wordParent_lt j hj)]
    exact (wordNode_vec_step j j.isLt hj).symm

def wordVector (i : Fin 841) : Source :=
  (flatCoordinates 28).symm (vec 841 (wordNode i).vector)

theorem wordVector_eq_sourceword (i : Fin 841) :
    wordVector i = wordOp sourceRep (wordWitness i) sourceGenerator := by
  apply (flatCoordinates 28).injective
  simpa only [wordVector,LinearEquiv.apply_symm_apply] using (flat_wordWitness i).symm

theorem wordVector_word (i : Fin 841) :
    ∃ l : List (Fin 28 × ℕ), degree l = (wordNode i).level ∧
      wordVector i = wordOp sourceRep l sourceGenerator :=
  ⟨wordWitness i,wordWitness_degree i,wordVector_eq_sourceword i⟩

end
#print axioms wordWitness_degree
#print axioms flat_wordWitness
#print axioms wordVector_word
end VOA.DeligneAudit.D4Two
