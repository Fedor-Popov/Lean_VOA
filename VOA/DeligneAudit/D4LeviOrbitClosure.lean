import VOA.DeligneAudit.D4LeviKeyNonDominant

/-! The extra gl₄ Cartan preserves the higher-key quotient. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem extra_levi_bracket_support (a : Fin 15) :
    (br 0 (leviColour a)).all
      (fun p => decide (∃ i : Fin 15, (leviColour i : ℕ) = p.1)) = true := by
  fin_cases a <;> decide

theorem extra_levi_bracket_outside (a : Fin 15) (c : Fin 28)
    (hc : c ∉ Set.range leviColour) :
    D4sector.f (0 : Fin 28) (leviColour a) c = 0 := by
  have hs := extra_levi_bracket_support a
  simp only [List.all_eq_true, decide_eq_true_eq] at hs
  have hz : sget (br 0 (leviColour a)) c = 0 := by
    by_contra hn
    obtain ⟨p, hp, hpc⟩ := exists_of_sget_ne_zero hn
    obtain ⟨i, hi⟩ := hs p hp
    exact hc ⟨i, Fin.ext (hi.trans hpc)⟩
  simp [D4sector, fD4, fC, fZ, hz]

theorem higherOrbit_extra_inv (k : RadicalKey) (r : ℕ) :
    higherOrbit ρ w m k ≤
      (higherOrbit ρ w m k).comap (ρ.op (0 : Fin 28) r) := by
  intro v hv
  have hm : (higherOrbit ρ w m k).map (ρ.op (0 : Fin 28) r) ≤
      higherOrbit ρ w m k := by
    rw [higherOrbit, Submodule.map_iSup]
    apply iSup_le
    intro j
    apply Submodule.map_le_iff_le_comap.mpr
    intro x hx
    exact Submodule.mem_iSup_of_mem j
      (levi_op_orbit ρ w j.val 0 r ⟨0, rfl⟩ hx)
  exact hm (Submodule.mem_map_of_mem hv)

theorem higherOrbit_full_levi_inv (k : RadicalKey)
    (a : Fin 28) (ha : IsLevi a) (r : ℕ) :
    higherOrbit ρ w m k ≤
      (higherOrbit ρ w m k).comap (ρ.op a r) := by
  intro v hv
  have hm : (higherOrbit ρ w m k).map (ρ.op a r) ≤
      higherOrbit ρ w m k := by
    rw [higherOrbit, Submodule.map_iSup]
    apply iSup_le
    intro j
    apply Submodule.map_le_iff_le_comap.mpr
    intro x hx
    exact Submodule.mem_iSup_of_mem j
      (levi_op_orbit ρ w j.val a r ha hx)
  exact hm (Submodule.mem_map_of_mem hv)

theorem levi_colour_or_extra (a : Fin 28) (ha : IsLevi a) :
    a = 0 ∨ ∃ i : Fin 15, leviColour i = a := by
  obtain ⟨j, rfl⟩ := ha
  fin_cases j <;> decide

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.higherOrbit_extra_inv
#print axioms VOA.DeligneAudit.D4Levi.higherOrbit_full_levi_inv
#print axioms VOA.DeligneAudit.D4Levi.levi_colour_or_extra
#print axioms VOA.DeligneAudit.D4Levi.extra_levi_bracket_support
#print axioms VOA.DeligneAudit.D4Levi.extra_levi_bracket_outside
