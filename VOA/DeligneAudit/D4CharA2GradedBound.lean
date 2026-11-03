import VOA.DeligneAudit.D4CharA2GradedCount

/-! The sharp GL3 character upper bound for every all-weight sl3 local Weyl generator. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector SectorWeyl LeviKeyFiltration

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem terminal_finrank_le_steps (n : ℕ) (F : ℕ → Submodule ℂ V)
    (hzero : F 0 = ⊥) (hmono : ∀ i < n, F i ≤ F (i + 1))
    (hfinite : ∀ i < n, FiniteDimensional ℂ (StepQuot F i)) :
    Module.finrank ℂ (F n) ≤
      ∑ i ∈ Finset.range n, Module.finrank ℂ (StepQuot F i) := by
  have hh := a2_terminal_finrank_le_sum n F (fun i => F (i + 1)) (fun _ => 1)
    hzero hmono hfinite (fun i hi => by simp [KeyQuot, StepQuot])
  simpa only [one_mul] using hh

variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2_graded_bound_with_projection (g : CurrentGrading ρ)
    (hw : w ∈ g.piece 0) (p q : ℕ) (h : A2LocalWeylRel ρ w p q) (N : ℕ) :
    Module.finrank ℂ (cycDeg ρ w N) ≤ A2.gl3Hilb (p + q) q 0 N := by
  let F := fun i => (a2KeyPrefix ρ w (a2KeyEnum p q) i).map (g.proj N)
  have hz : F 0 = ⊥ := by simp [F, a2KeyPrefix_zero]
  have ht : F (a2KeyBox p q).card = cycDeg ρ w N := by
    dsimp only [F]
    rw [a2OrderedPrefix_top ρ w p q h, currentGrading_cyclic g hw N]
  have hm (i : ℕ) (hi : i < (a2KeyBox p q).card) : F i ≤ F (i + 1) :=
    Submodule.map_mono (a2KeyPrefix_mono ρ w hi (a2KeyEnum p q))
  have hf (i : ℕ) (hi : i < (a2KeyBox p q).card) :
      FiniteDimensional ℂ (StepQuot F i) :=
    (a2ProjectedStep_bound ρ w g hw p q h N ⟨i, hi⟩).1
  have hh := terminal_finrank_le_steps (a2KeyBox p q).card F hz hm hf
  rw [ht] at hh
  calc
    Module.finrank ℂ (cycDeg ρ w N) ≤
        ∑ i ∈ Finset.range (a2KeyBox p q).card,
          Module.finrank ℂ (StepQuot F i) := hh
    _ = ∑ i : Fin (a2KeyBox p q).card,
        Module.finrank ℂ (StepQuot F i.val) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range.mp hi, dif_pos]
    _ ≤ ∑ i : Fin (a2KeyBox p q).card,
        a2GradedKeyContribution p q N (a2KeyEnum p q i) :=
      Finset.sum_le_sum (fun i _ => (a2ProjectedStep_bound ρ w g hw p q h N i).2)
    _ ≤ A2.gl3Hilb (p + q) q 0 N := a2GradedKey_enum_sum_le p q N

theorem tagged_zero_iterate {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
    (R : CurrentModule f V) (a : Fin n) (k d : ℕ) (v : V) :
    ((D1TensorG.Gr.gRep R).op a 0)^[k] (Finsupp.single d v) =
      Finsupp.single d ((R.op a 0)^[k] v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact D1TensorG.Gr.gop_single R a 0 d _

theorem a2_localWeyl_tagged (p q : ℕ) (h : A2LocalWeylRel ρ w p q) :
    A2LocalWeylRel (D1TensorG.Gr.gRep ρ) (Finsupp.single 0 w) p q where
  raising e he r := by
    change D1TensorG.Gr.gop ρ e r (Finsupp.single 0 w) = 0
    rw [D1TensorG.Gr.gop_single, h.raising e he r, Finsupp.single_zero]
  cartan_pos e he r hr := by
    change D1TensorG.Gr.gop ρ e r (Finsupp.single 0 w) = 0
    rw [D1TensorG.Gr.gop_single, h.cartan_pos e he r hr, Finsupp.single_zero]
  cartan_first := by
    change D1TensorG.Gr.gop ρ 6 0 (Finsupp.single 0 w) = _
    rw [D1TensorG.Gr.gop_single, h.cartan_first]
    simp only [zero_add, Finsupp.smul_single]
  cartan_second := by
    change D1TensorG.Gr.gop ρ 7 0 (Finsupp.single 0 w) = _
    rw [D1TensorG.Gr.gop_single, h.cartan_second]
    simp only [zero_add, Finsupp.smul_single]
  lowering_first := by rw [tagged_zero_iterate, h.lowering_first, Finsupp.single_zero]
  lowering_second := by rw [tagged_zero_iterate, h.lowering_second, Finsupp.single_zero]

/-- No grading hypothesis is imposed on the module: the tagged lift supplies it. -/
theorem a2_all_weight_graded_bound (p q : ℕ) (h : A2LocalWeylRel ρ w p q) (N : ℕ) :
    FiniteDimensional ℂ (cycDeg ρ w N) ∧
      Module.finrank ℂ (cycDeg ρ w N) ≤ A2.gl3Hilb (p + q) q 0 N := by
  haveI := (a2_all_weight_rank ρ w p q h).1
  have hc : cycDeg ρ w N ≤ UnivG.cycSubG ρ w := by
    apply Submodule.span_le.mpr
    rintro v ⟨l, _, rfl⟩
    exact UnivG.wordOp_mem_cycSubG ρ w l
  refine ⟨Submodule.finiteDimensional_of_le hc, ?_⟩
  have hh := a2_graded_bound_with_projection (D1TensorG.Gr.gRep ρ)
    (Finsupp.single 0 w) (taggedCurrentGrading (ρ := ρ)) ⟨w, rfl⟩ p q
    (a2_localWeyl_tagged ρ w p q h) N
  rwa [tagged_cycDeg_finrank] at hh

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.terminal_finrank_le_steps
#print axioms VOA.DeligneAudit.D4Char.a2_graded_bound_with_projection
#print axioms VOA.DeligneAudit.D4Char.tagged_zero_iterate
#print axioms VOA.DeligneAudit.D4Char.a2_localWeyl_tagged
#print axioms VOA.DeligneAudit.D4Char.a2_all_weight_graded_bound
