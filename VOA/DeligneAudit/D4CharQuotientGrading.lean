import VOA.DeligneAudit.D4CharA3GradedBound
import VOA.DeligneAudit.D4CharGradedKeys

/-! Degree projections on presented current modules and homogeneous quotients. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {ρ : CurrentModule f V}

theorem currentGrading_cyclic_shift (g : CurrentGrading ρ) (d N : ℕ)
    {v : V} (hv : v ∈ g.piece d) (hd : d ≤ N) :
    (cycSubG ρ v).map (g.proj N) = cycDeg ρ v (N - d) := by
  have hc : colourClosure (ρ := ρ) (fun _ => True) (ℂ ∙ v) = cycSubG ρ v := by
    rw [colourClosure_singleton]
    simp only [cycSubG, List.forall_iff_forall_mem, implies_true, true_and]
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]
  rw [← hc]
  exact (colourOrbit_projection g (fun _ => True) d N hv hd).trans
    (colourDegreeOrbit_true _ _ _)

def quotientCurrentGrading (g : CurrentGrading ρ) (F : Submodule ℂ V)
    (hF : ∀ a r, F ≤ F.comap (ρ.op a r))
    (hproj : ∀ d, F.map (g.proj d) ≤ F) : CurrentGrading (quotRepG ρ F hF) where
  piece d := (g.piece d).map F.mkQ
  proj d := F.mapQ F (g.proj d) (Submodule.map_le_iff_le_comap.mp (hproj d))
  proj_mem d z := by
    obtain ⟨v, rfl⟩ := F.mkQ_surjective z
    exact ⟨g.proj d v, g.proj_mem d v, rfl⟩
  proj_piece d e z hz := by
    obtain ⟨v, hv, rfl⟩ := hz
    change F.mkQ (g.proj d v) = if e = d then F.mkQ v else 0
    rw [g.proj_piece d e v hv]
    split_ifs <;> simp
  op_piece a r d z hz := by
    obtain ⟨v, hv, rfl⟩ := hz
    exact ⟨ρ.op a r v, g.op_piece a r d v hv, rfl⟩

theorem quotient_projection_commute (g : CurrentGrading ρ) (F : Submodule ℂ V)
    (hF : ∀ a r, F ≤ F.comap (ρ.op a r))
    (hproj : ∀ d, F.map (g.proj d) ≤ F) (S : Submodule ℂ V) (N : ℕ) :
    (S.map (g.proj N)).map F.mkQ =
      (S.map F.mkQ).map ((quotientCurrentGrading g F hF hproj).proj N) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  rfl

theorem cycDeg_current_op (R : CurrentModule f V) (w : V) (a : Fin n) (r d : ℕ) :
    cycDeg R w d ≤ (cycDeg R w (r + d)).comap (R.op a r) := by
  apply Submodule.span_le.mpr
  rintro v ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨(a, r) :: l, by rw [degG_cons, hl], rfl⟩

theorem univ_projection_homogeneous (R : RelSpec n) (N d : ℕ)
    {v : UModG f R} (hv : v ∈ cycDeg (univRepG f R) (wUG f R) d) :
    projUG f R N v = if d = N then v else 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      rw [wordOp_univG, projUG_mk, hl]
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add, ihx, ihy]
      split_ifs <;> simp
  | smul a x hx ih =>
      rw [map_smul, ih]
      split_ifs <;> simp

theorem univ_projection_mem (R : RelSpec n) (N : ℕ) (v : UModG f R) :
    projUG f R N v ∈ cycDeg (univRepG f R) (wUG f R) N := by
  obtain ⟨u, rfl⟩ := (Jrel f R).mkQ_surjective v
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hu hv
  | single l a =>
      have he : Finsupp.single l a = a • UnivG.sw l := by simp [UnivG.sw]
      rw [he, map_smul, map_smul]
      apply Submodule.smul_mem
      change projUG f R N (Submodule.Quotient.mk (UnivG.sw l)) ∈ _
      rw [projUG_mk]
      split_ifs with hd
      · rw [← wordOp_univG]
        exact Submodule.subset_span ⟨l, hd, rfl⟩
      · exact Submodule.zero_mem _

def universalCurrentGrading (R : RelSpec n) : CurrentGrading (univRepG f R) where
  piece d := cycDeg (univRepG f R) (wUG f R) d
  proj d := projUG f R d
  proj_mem := univ_projection_mem R
  proj_piece d e v hv := univ_projection_homogeneous R d e hv
  op_piece a r d v hv := cycDeg_current_op _ _ a r d hv

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.currentGrading_cyclic_shift
#print axioms VOA.DeligneAudit.D4Char.quotient_projection_commute
#print axioms VOA.DeligneAudit.D4Char.cycDeg_current_op
#print axioms VOA.DeligneAudit.D4Char.univ_projection_homogeneous
#print axioms VOA.DeligneAudit.D4Char.univ_projection_mem
