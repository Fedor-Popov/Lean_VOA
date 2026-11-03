import VOA.DeligneAudit.D4LeviKSMixedEvalTransfer

/-! A polynomial supported on one summand evaluates with zero-mode spectator slots. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xyzEvaluation_sum_zero_slots {σ τ : Type*}
    [Fintype σ] [Fintype τ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ ⊕ τ → Fin 6) (P : MvPolynomial σ ℂ) :
    xyzEvaluation ρ w shape (rename Sum.inl P) =
      (((Finset.univ.toList : List τ).map fun t =>
        ρ.op (radicalColour (shape (Sum.inr t))) 0).prod)
        (xyzEvaluation ρ w (shape ∘ Sum.inl) P) := by
  classical
  have hslots : (Finset.univ.toList : List (σ ⊕ τ)).Perm
      ((Finset.univ.toList : List σ).map Sum.inl ++
        (Finset.univ.toList : List τ).map Sum.inr) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.nodup_toList _
    · apply List.Nodup.append
      · exact (Finset.nodup_toList _).map Sum.inl_injective
      · exact (Finset.nodup_toList _).map Sum.inr_injective
      · intro x hx hy
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨v, _, h⟩ := List.mem_map.mp hy
        exact Sum.inl_ne_inr h.symm
    · ext t
      rcases t with t | t <;> simp
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial σ ℂ) =
          z • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      simp only [map_smul, map_smul]
      have hrename : rename Sum.inl (modeMonomial σ d) =
          modeMonomial (σ ⊕ τ) (d.mapDomain Sum.inl) := by
        simp [modeMonomial, rename_monomial]
      rw [hrename]
      simp only [xyzEvaluation, modeWordEvaluation_monomial]
      have hp := hslots.map (fun t : σ ⊕ τ =>
        (shape t, d.mapDomain Sum.inl t))
      have hword :
          (shapedModes shape Finset.univ.toList (d.mapDomain Sum.inl)).Perm
            (shapedModes (shape ∘ Sum.inl) Finset.univ.toList d ++
              (Finset.univ.toList : List τ).map fun t =>
                (shape (Sum.inr t), 0)) := by
        have hinl (i : σ) :
            (d.mapDomain (Sum.inl : σ → σ ⊕ τ)) (Sum.inl i) = d i := by
          rw [Finsupp.mapDomain_apply Sum.inl_injective]
        have hinr (i : τ) :
            (d.mapDomain (Sum.inl : σ → σ ⊕ τ)) (Sum.inr i) = 0 := by
          apply Finsupp.mapDomain_notin_range
          simp
        simpa only [shapedModes, List.map_append, List.map_map,
          Function.comp_def, hinl, hinr] using hp
      rw [radicalWord_perm ρ w hword]
      simp only [radicalWord_eq_prod, List.map_append, List.prod_append,
        List.map_map, Function.comp_def, Module.End.mul_apply]
      have hc :
          ((shapedModes (shape ∘ Sum.inl) Finset.univ.toList d).map
              fun p => ρ.op (radicalColour p.1) p.2).prod *
            ((Finset.univ.toList : List τ).map fun t =>
              ρ.op (radicalColour (shape (Sum.inr t))) 0).prod =
          ((Finset.univ.toList : List τ).map fun t =>
              ρ.op (radicalColour (shape (Sum.inr t))) 0).prod *
            ((shapedModes (shape ∘ Sum.inl) Finset.univ.toList d).map
              fun p => ρ.op (radicalColour p.1) p.2).prod := by
        ext v
        have h := radicalWord_perm ρ v
          (List.perm_append_comm (l₁ :=
            shapedModes (shape ∘ Sum.inl) Finset.univ.toList d)
            (l₂ := (Finset.univ.toList : List τ).map fun t =>
              (shape (Sum.inr t), 0)))
        rw [radicalWord_eq_prod, radicalWord_eq_prod] at h
        simpa only [List.map_append, List.prod_append, List.map_map,
          Function.comp_def, Module.End.mul_apply] using h
      simpa only [Function.comp_def, Module.End.mul_apply] using
        congrArg (z • ·) (congrArg (· w) hc)
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, LinearMap.add_apply]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_sum_zero_slots
