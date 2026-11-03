import VOA.DeligneAudit.DeligneFusionD1TensorGGrPieces

/-!
# Coordinate separation in the actual current-degree quotient

Degree projections descend through the lower-filtration relations. They
separate the actual cyclic degree pieces, without any finite-dimensionality
assumption on the ambient quotient.
-/

namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {T : Type*} [AddCommGroup T] [Module ℂ T]
variable (R : CurrentModule f T) (w : T)

def keepDegree (d : ℕ) : (ℕ →₀ T) →ₗ[ℂ] (ℕ →₀ T) :=
  Finsupp.lsingle d ∘ₗ evalAt d

theorem keepDegree_single (d e : ℕ) (v : T) :
    keepDegree d (Finsupp.single e v) =
      if d = e then Finsupp.single e v else 0 := by
  by_cases h : d = e
  · subst e
    simp [keepDegree, evalAt]
  · simp [keepDegree, evalAt, h]

theorem Lsub_keepDegree (d : ℕ) :
    Lsub R w ≤ (Lsub R w).comap (keepDegree d) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, v, hv, rfl⟩
  change keepDegree d (Finsupp.single e v) ∈ Lsub R w
  rw [keepDegree_single]
  split_ifs
  · exact single_mem_Lsub R w hv
  · exact Submodule.zero_mem _

def degreeProj (d : ℕ) :
    ((ℕ →₀ T) ⧸ Lsub R w) →ₗ[ℂ] ((ℕ →₀ T) ⧸ Lsub R w) :=
  (Lsub R w).mapQ (Lsub R w) (keepDegree d) (Lsub_keepDegree R w d)

theorem degreeProj_tag (d e : ℕ) (v : T) :
    degreeProj R w d (tag R w e v) = if d = e then tag R w e v else 0 := by
  change (Lsub R w).mkQ (keepDegree d (Finsupp.single e v)) = _
  rw [keepDegree_single]
  split_ifs <;> simp [tag_apply]

theorem degreeProj_cycDeg (d e : ℕ) {x : (ℕ →₀ T) ⧸ Lsub R w}
    (hx : x ∈ cycDeg (grRep R w) (wg R w) e) :
    degreeProj R w d x = if d = e then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      change degree l = e at hl
      rw [grRep_word]
      change degreeProj R w d (tag R w (degree l) (wordOp R l w)) = _
      rw [degreeProj_tag]
      simp only [hl, tag_apply]
  | zero => simp
  | add u v hu hv ihu ihv =>
      rw [map_add, ihu, ihv]
      split_ifs <;> simp
  | smul a v hv ih =>
      rw [map_smul, ih]
      split_ifs <;> simp

abbrev GradePiece (d : ℕ) := cycDeg (grRep R w) (wg R w) d

def pieceSum (B : ℕ) :
    (Π i : Fin B, GradePiece R w i.val) →ₗ[ℂ] ((ℕ →₀ T) ⧸ Lsub R w) where
  toFun v := ∑ i, (v i : (ℕ →₀ T) ⧸ Lsub R w)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

theorem degreeProj_pieceSum (B : ℕ) (i : Fin B)
    (v : Π j : Fin B, GradePiece R w j.val) :
    degreeProj R w i.val (pieceSum R w B v) = (v i : (ℕ →₀ T) ⧸ Lsub R w) := by
  change degreeProj R w i.val (∑ j, (v j : (ℕ →₀ T) ⧸ Lsub R w)) = _
  rw [map_sum, Finset.sum_eq_single i]
  · rw [degreeProj_cycDeg R w i.val i.val (v i).property, if_pos rfl]
  · intro j _ hji
    rw [degreeProj_cycDeg R w i.val j.val (v j).property]
    have hne : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    simp [hne]
  · simp

theorem pieceSum_injective (B : ℕ) : Function.Injective (pieceSum R w B) := by
  intro u v huv
  funext i
  apply Subtype.ext
  have hi := congrArg (degreeProj R w i.val) huv
  rw [degreeProj_pieceSum, degreeProj_pieceSum] at hi
  exact hi

end

end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.degreeProj_cycDeg
#print axioms VOA.DeligneAudit.D1TensorG.Gr.pieceSum_injective
