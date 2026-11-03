import VOA.DeligneAudit.D4LevelCorePresentationAudit

/-! The semisimple and reductive Levi orbits of the bottom vector agree. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

/-- Removing the sign in a Levi current does not change cyclic membership. -/
theorem semisimpleCyclic_unsigned (v : V) (e : Fin 15) (r : ℕ)
    {u : V} (hu : u ∈ cycSubG (leviCurrent ρ) v) :
    ρ.op (leviColour e) r u ∈ cycSubG (leviCurrent ρ) v := by
  have hs : (leviSign e : ℂ) * (leviSign e : ℂ) = 1 := by
    fin_cases e <;> norm_num [leviSign]
  have hh := (cycSubG (leviCurrent ρ) v).smul_mem (leviSign e : ℂ)
    (cycSubG_inv (leviCurrent ρ) v e r hu)
  simpa only [leviCurrent, LinearMap.smul_apply, smul_smul, hs, one_smul] using hh

/-- Stability of the extra Cartan on the generator extends to its semisimple cyclic module. -/
theorem semisimpleCyclic_extraCartan (v : V)
    (hv : ∀ r, ρ.op (0 : Fin 28) r v ∈ cycSubG (leviCurrent ρ) v) (r : ℕ) :
    cycSubG (leviCurrent ρ) v ≤ (cycSubG (leviCurrent ρ) v).comap (ρ.op (0 : Fin 28) r) := by
  classical
  let C := cycSubG (leviCurrent ρ) v
  rw [cycSubG, Submodule.span_le]
  rintro z ⟨l, rfl⟩
  change ρ.op (0 : Fin 28) r (wordOp (leviCurrent ρ) l v) ∈ C
  induction l with
  | nil => exact hv r
  | cons q l ih =>
      let u := wordOp (leviCurrent ρ) l v
      have hu : u ∈ C := wordOp_mem_cycSubG (leviCurrent ρ) v l
      have hsum : (∑ t : Fin 28, D4sector.f (0 : Fin 28) (leviColour q.1) t •
          ρ.op t (r + q.2) u) ∈ C := by
        apply C.sum_mem
        intro t _
        by_cases ht : t ∈ Set.range leviColour
        · obtain ⟨e, rfl⟩ := ht
          exact C.smul_mem _ (semisimpleCyclic_unsigned ρ v e _ hu)
        · rw [extra_levi_bracket_outside q.1 t ht, zero_smul]
          exact C.zero_mem
      change ρ.op (0 : Fin 28) r ((leviSign q.1 : ℂ) • ρ.op (leviColour q.1) q.2 u) ∈ C
      rw [map_smul, sub_eq_iff_eq_add.mp (ρ.comm (0 : Fin 28) (leviColour q.1) r q.2 u)]
      exact C.smul_mem _ (C.add_mem hsum (semisimpleCyclic_unsigned ρ v q.1 q.2 ih))

variable (w : V)

/-- The bottom semisimple cyclic module is stable under every reductive Levi current. -/
theorem bottomSemisimpleCyclic_levi (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (e : Fin 28) (r : ℕ)
    (he : IsLevi e) :
    cycSubG (leviCurrent ρ) (bottomVector ρ w a c) ≤
      (cycSubG (leviCurrent ρ) (bottomVector ρ w a c)).comap (ρ.op e r) := by
  rcases levi_colour_or_extra e he with rfl | ⟨i, rfl⟩
  · apply semisimpleCyclic_extraCartan
    intro s
    have hh := bottomVector_extraCartan ρ w m a c h s
    change ρ.op (0 : Fin 28) s (bottomVector ρ w a c) =
      -ρ.op (leviColour (A3Sector.simpleH 0)) s (bottomVector ρ w a c) at hh
    rw [hh]
    exact Submodule.neg_mem _ (semisimpleCyclic_unsigned ρ _ _ _
      (wordOp_mem_cycSubG (leviCurrent ρ) _ []))
  · intro u hu
    exact semisimpleCyclic_unsigned ρ _ i r hu

/-- The full reductive orbit of the bottom vector equals its semisimple cyclic module. -/
theorem bottomVector_reductiveOrbit_eq_cyclic (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    keyVectorOrbit ρ (bottomVector ρ w a c) =
      cycSubG (leviCurrent ρ) (bottomVector ρ w a c) := by
  apply le_antisymm
  · rw [keyVectorOrbit, Submodule.span_le]
    rintro v ⟨l, hl, rfl⟩
    induction l with
    | nil => exact wordOp_mem_cycSubG (leviCurrent ρ) _ []
    | cons q l ih =>
        simp only [List.forall_cons] at hl
        exact bottomSemisimpleCyclic_levi ρ w m a c h q.1 q.2 hl.1 (ih hl.2)
  · rw [cycSubG, Submodule.span_le]
    rintro v ⟨l, rfl⟩
    induction l with
    | nil => exact keyVectorOrbit_mem ρ _ [] (by simp)
    | cons q l ih =>
        exact Submodule.smul_mem _ _
          (keyVectorOrbit_inv ρ _ _ q.2 (leviColour_isLevi q.1) ih)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.semisimpleCyclic_unsigned
#print axioms VOA.DeligneAudit.D4LevelReduction.semisimpleCyclic_extraCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomSemisimpleCyclic_levi
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomVector_reductiveOrbit_eq_cyclic
