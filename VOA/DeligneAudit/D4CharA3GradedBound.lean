import VOA.DeligneAudit.D4CharA3GradedCount

/-! The sharp GL4 character upper bound for every sl4 local Weyl generator. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector SectorWeyl LeviKeyFiltration

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_graded_bound_with_projection (g : CurrentGrading ρ)
    (hw : w ∈ g.piece 0) (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c)) (N : ℕ) :
    Module.finrank ℂ (cycDeg ρ w N) ≤ gl4Hilb (a + b + c) (b + c) c 0 N := by
  let F := fun i => (a3KeyPrefix ρ w (a3KeyEnum a b c) i).map (g.proj N)
  have hz : F 0 = ⊥ := by simp [F, a3KeyPrefix_zero]
  have ht : F (a3KeyBox a b c).card = cycDeg ρ w N := by
    dsimp only [F]
    rw [a3OrderedPrefix_top ρ w a b c h, currentGrading_cyclic g hw N]
  have hm (i : ℕ) (hi : i < (a3KeyBox a b c).card) : F i ≤ F (i + 1) :=
    Submodule.map_mono (a3KeyPrefix_mono ρ w hi (a3KeyEnum a b c))
  have hf (i : ℕ) (hi : i < (a3KeyBox a b c).card) :
      FiniteDimensional ℂ (StepQuot F i) :=
    (a3ProjectedStep_bound ρ w g hw a b c h N ⟨i, hi⟩).1
  have hh := terminal_finrank_le_steps (a3KeyBox a b c).card F hz hm hf
  rw [ht] at hh
  calc
    Module.finrank ℂ (cycDeg ρ w N) ≤
        ∑ i ∈ Finset.range (a3KeyBox a b c).card,
          Module.finrank ℂ (StepQuot F i) := hh
    _ = ∑ i : Fin (a3KeyBox a b c).card,
        Module.finrank ℂ (StepQuot F i.val) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range.mp hi, dif_pos]
    _ ≤ ∑ i : Fin (a3KeyBox a b c).card,
        a3GradedKeyContribution a b c N (a3KeyEnum a b c i) :=
      Finset.sum_le_sum (fun i _ => (a3ProjectedStep_bound ρ w g hw a b c h N i).2)
    _ ≤ gl4Hilb (a + b + c) (b + c) c 0 N := a3GradedKey_enum_sum_le a b c N

theorem a3_localWeyl_tagged (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    LocalWeylRel (D1TensorG.Gr.gRep ρ) (Finsupp.single 0 w) (weightABC a b c) where
  raising e he r := by
    change D1TensorG.Gr.gop ρ e r (Finsupp.single 0 w) = 0
    rw [D1TensorG.Gr.gop_single, h.raising e he r, Finsupp.single_zero]
  cartan_pos i r hr := by
    change D1TensorG.Gr.gop ρ (simpleH i) r (Finsupp.single 0 w) = 0
    rw [D1TensorG.Gr.gop_single, h.cartan_pos i r hr, Finsupp.single_zero]
  cartan_zero i := by
    change D1TensorG.Gr.gop ρ (simpleH i) 0 (Finsupp.single 0 w) = _
    rw [D1TensorG.Gr.gop_single, h.cartan_zero i]
    simp only [zero_add, Finsupp.smul_single]
  lowering i := by rw [tagged_zero_iterate, h.lowering i, Finsupp.single_zero]

/-- The graded type-A3 local Weyl bound, for all weights and all current degrees. -/
theorem a3_all_weight_graded_bound (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (N : ℕ) :
    FiniteDimensional ℂ (cycDeg ρ w N) ∧
      Module.finrank ℂ (cycDeg ρ w N) ≤ gl4Hilb (a + b + c) (b + c) c 0 N := by
  haveI := (a3_all_weight_rank ρ w a b c h).1
  have hc : cycDeg ρ w N ≤ UnivG.cycSubG ρ w := by
    apply Submodule.span_le.mpr
    rintro v ⟨l, _, rfl⟩
    exact UnivG.wordOp_mem_cycSubG ρ w l
  refine ⟨Submodule.finiteDimensional_of_le hc, ?_⟩
  have hh := a3_graded_bound_with_projection (D1TensorG.Gr.gRep ρ)
    (Finsupp.single 0 w) (taggedCurrentGrading (ρ := ρ)) ⟨w, rfl⟩ a b c
    (a3_localWeyl_tagged ρ w a b c h) N
  rwa [tagged_cycDeg_finrank] at hh

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.a3_graded_bound_with_projection
#print axioms VOA.DeligneAudit.D4Char.a3_localWeyl_tagged
#print axioms VOA.DeligneAudit.D4Char.a3_all_weight_graded_bound
