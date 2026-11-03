import VOA.DeligneAudit.D4CharProjectedStep
import VOA.DeligneAudit.DeligneFusionD1TensorGGrRankProjection

/-! Degree projections for current-word closures, independently of the Lie type. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule f V)

structure CurrentGrading where
  piece : ℕ → Submodule ℂ V
  proj : ℕ → Module.End ℂ V
  proj_mem : ∀ d v, proj d v ∈ piece d
  proj_piece : ∀ d e v, v ∈ piece e → proj d v = if e = d then v else 0
  op_piece : ∀ a r d v, v ∈ piece d → ρ.op a r v ∈ piece (r + d)

variable {ρ}

theorem currentGrading_idem (g : CurrentGrading ρ) (d : ℕ) (v : V) :
    g.proj d (g.proj d v) = g.proj d v := by
  rw [g.proj_piece d d _ (g.proj_mem d v), if_pos rfl]

theorem currentGrading_word (g : CurrentGrading ρ) (l : List (Fin n × ℕ))
    (d : ℕ) {v : V} (hv : v ∈ g.piece d) :
    wordOp ρ l v ∈ g.piece (SectorGraded.wordDeg l + d) := by
  induction l with
  | nil => simpa [SectorGraded.wordDeg] using hv
  | cons x l ih =>
      simpa only [SectorGraded.wordDeg, List.map_cons, List.sum_cons, Nat.add_assoc]
        using g.op_piece x.1 x.2 (SectorGraded.wordDeg l + d) _ ih

def colourClosure (P : Fin n → Prop) (S : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (l : List (Fin n × ℕ)) (v : V),
    l.Forall (fun x => P x.1) ∧ v ∈ S ∧ z = wordOp ρ l v}

def colourDegreeOrbit (P : Fin n → Prop) (v : V) (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l : List (Fin n × ℕ),
    l.Forall (fun x => P x.1) ∧ SectorGraded.wordDeg l = d ∧ z = wordOp ρ l v}

theorem colourClosure_projection (g : CurrentGrading ρ) (P : Fin n → Prop)
    (S : Submodule ℂ V) (d N : ℕ) (hS : S ≤ g.piece d) :
    (colourClosure (ρ := ρ) P S).map (g.proj N) ≤ colourClosure (ρ := ρ) P S := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro z ⟨l, v, hl, hv, rfl⟩
  change g.proj N (wordOp ρ l v) ∈ colourClosure (ρ := ρ) P S
  rw [g.proj_piece N _ _ (currentGrading_word g l d (hS hv))]
  split_ifs
  · exact Submodule.subset_span ⟨l, v, hl, hv, rfl⟩
  · exact Submodule.zero_mem _

theorem colourClosure_singleton (P : Fin n → Prop) (v : V) :
    colourClosure (ρ := ρ) P (ℂ ∙ v) =
      Submodule.span ℂ {z | ∃ l : List (Fin n × ℕ),
        l.Forall (fun x => P x.1) ∧ z = wordOp ρ l v} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨l, u, hl, hu, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [wordOp_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨l, hl, rfl⟩)
  · apply Submodule.span_mono
    rintro z ⟨l, hl, rfl⟩
    exact ⟨l, v, hl, Submodule.mem_span_singleton_self v, rfl⟩

theorem colourOrbit_projection (g : CurrentGrading ρ) (P : Fin n → Prop)
    (d N : ℕ) {v : V} (hv : v ∈ g.piece d) (hd : d ≤ N) :
    (colourClosure (ρ := ρ) P (ℂ ∙ v)).map (g.proj N) =
      colourDegreeOrbit (ρ := ρ) P v (N - d) := by
  rw [colourClosure_singleton]
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro z ⟨l, hl, rfl⟩
    change g.proj N (wordOp ρ l v) ∈ colourDegreeOrbit (ρ := ρ) P v (N - d)
    rw [g.proj_piece N _ _ (currentGrading_word g l d hv)]
    split_ifs with he
    · exact Submodule.subset_span ⟨l, hl, by omega, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro z ⟨l, hl, he, rfl⟩
    refine ⟨wordOp ρ l v, Submodule.subset_span ⟨l, hl, rfl⟩, ?_⟩
    rw [g.proj_piece N _ _ (currentGrading_word g l d hv), if_pos (by omega)]

theorem colourOrbit_projection_zero (g : CurrentGrading ρ) (P : Fin n → Prop)
    (d N : ℕ) {v : V} (hv : v ∈ g.piece d) (hd : N < d) :
    (colourClosure (ρ := ρ) P (ℂ ∙ v)).map (g.proj N) = ⊥ := by
  apply eq_bot_iff.mpr
  rw [colourClosure_singleton]
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro z ⟨l, hl, rfl⟩
  change g.proj N (wordOp ρ l v) ∈ (⊥ : Submodule ℂ V)
  rw [g.proj_piece N _ _ (currentGrading_word g l d hv), if_neg (by omega)]
  exact Submodule.zero_mem _

theorem currentGrading_cyclic (g : CurrentGrading ρ) {w : V}
    (hw : w ∈ g.piece 0) (N : ℕ) :
    (UnivG.cycSubG ρ w).map (g.proj N) = cycDeg ρ w N := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro z ⟨l, rfl⟩
    change g.proj N (wordOp ρ l w) ∈ cycDeg ρ w N
    rw [g.proj_piece N _ _ (currentGrading_word g l 0 hw)]
    split_ifs with hd
    · exact Submodule.subset_span ⟨l, by simpa using hd, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro z ⟨l, hl, rfl⟩
    refine ⟨wordOp ρ l w, UnivG.wordOp_mem_cycSubG ρ w l, ?_⟩
    rw [g.proj_piece N _ _ (currentGrading_word g l 0 hw), if_pos (by simpa using hl)]

/-- The degree-tagged lift supplies genuine projections for every current module. -/
def taggedCurrentGrading : CurrentGrading (D1TensorG.Gr.gRep ρ) where
  piece d := LinearMap.range (Finsupp.lsingle d : V →ₗ[ℂ] ℕ →₀ V)
  proj d := D1TensorG.Gr.keepDegree d
  proj_mem d v := ⟨v d, rfl⟩
  proj_piece d e v hv := by
    obtain ⟨u, rfl⟩ := hv
    simpa only [Finsupp.lsingle_apply, eq_comm] using
      D1TensorG.Gr.keepDegree_single d e u
  op_piece a r d v hv := by
    obtain ⟨u, rfl⟩ := hv
    refine ⟨ρ.op a r u, ?_⟩
    change Finsupp.single (r + d) _ = D1TensorG.Gr.gop ρ a r (Finsupp.single d u)
    rw [D1TensorG.Gr.gop_single, Nat.add_comm]

theorem tagged_cycDeg (w : V) (N : ℕ) :
    cycDeg (D1TensorG.Gr.gRep ρ) (Finsupp.single 0 w) N =
      (cycDeg ρ w N).map (Finsupp.lsingle N) := by
  rw [cycDeg, cycDeg, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨wordOp ρ l w, ⟨l, hl, rfl⟩, ?_⟩
    rw [D1TensorG.Gr.gRep_word]
    simp only [Finsupp.lsingle_apply, zero_add, hl, D1TensorG.Gr.degree]
  · rintro ⟨v, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨l, hl, ?_⟩
    rw [D1TensorG.Gr.gRep_word]
    simp only [Finsupp.lsingle_apply, zero_add, hl, D1TensorG.Gr.degree]

theorem tagged_cycDeg_finrank (w : V) (N : ℕ) :
    Module.finrank ℂ (cycDeg (D1TensorG.Gr.gRep ρ) (Finsupp.single 0 w) N) =
      Module.finrank ℂ (cycDeg ρ w N) := by
  rw [tagged_cycDeg]
  exact (Submodule.equivMapOfInjective _ (Finsupp.single_injective N)
    (cycDeg ρ w N)).finrank_eq.symm

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.currentGrading_idem
#print axioms VOA.DeligneAudit.D4Char.currentGrading_word
#print axioms VOA.DeligneAudit.D4Char.colourClosure_projection
#print axioms VOA.DeligneAudit.D4Char.colourClosure_singleton
#print axioms VOA.DeligneAudit.D4Char.colourOrbit_projection
#print axioms VOA.DeligneAudit.D4Char.colourOrbit_projection_zero
#print axioms VOA.DeligneAudit.D4Char.currentGrading_cyclic
#print axioms VOA.DeligneAudit.D4Char.tagged_cycDeg
#print axioms VOA.DeligneAudit.D4Char.tagged_cycDeg_finrank
