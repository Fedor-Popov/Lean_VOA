import VOA.DeligneAudit.D4LeviKeyOrbits

/-! Higher-key Levi closure and its quotient current module. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The sum of all Levi orbits above a key in the total order. -/
def higherOrbit (k : RadicalKey) : Submodule ℂ V :=
  ⨆ j : {j : RadicalKey // keyLess m k j}, keyOrbit ρ w j.val

theorem keyOrbit_le_higher (k j : RadicalKey) (hkj : keyLess m k j) :
    keyOrbit ρ w j ≤ higherOrbit ρ w m k := by
  exact le_iSup_of_le ⟨j, hkj⟩ le_rfl

theorem leviColour_isLevi (a : Fin 15) : IsLevi (leviColour a) := by
  change ∃ i : Fin 16, leviIndex i = leviColour a
  refine ⟨⟨a.val + 1, by omega⟩, ?_⟩
  fin_cases a <;> rfl

theorem higherOrbit_levi_inv (k : RadicalKey) (a : Fin 15) (r : ℕ) :
    higherOrbit ρ w m k ≤
      (higherOrbit ρ w m k).comap ((leviCurrent ρ).op a r) := by
  intro v hv
  have hmap : (higherOrbit ρ w m k).map ((leviCurrent ρ).op a r) ≤
      higherOrbit ρ w m k := by
    rw [higherOrbit, Submodule.map_iSup]
    apply iSup_le
    intro j
    apply Submodule.map_le_iff_le_comap.mpr
    intro x hx
    apply Submodule.mem_iSup_of_mem j
    change (leviSign a : ℂ) • ρ.op (leviColour a) r x ∈ keyOrbit ρ w j.val
    exact (keyOrbit ρ w j.val).smul_mem _
      (levi_op_orbit ρ w j.val (leviColour a) r (leviColour_isLevi a) hx)
  exact hmap (Submodule.mem_map_of_mem hv)

/-- The sl4 current action on the quotient by all higher key orbits. -/
def keyQuotCurrent (k : RadicalKey) :
    CurrentModule VOA.DeligneAudit.A3Sector.bracketTable
      (V ⧸ higherOrbit ρ w m k) :=
  VOA.DeligneAudit.UnivG.quotRepG (leviCurrent ρ)
    (higherOrbit ρ w m k) (higherOrbit_levi_inv ρ w m k)

theorem keyQuotCurrent_op (k : RadicalKey) (a : Fin 15) (r : ℕ) (v : V) :
    (keyQuotCurrent ρ w m k).op a r ((higherOrbit ρ w m k).mkQ v) =
      (higherOrbit ρ w m k).mkQ ((leviCurrent ρ).op a r v) := rfl

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyOrbit_le_higher
#print axioms VOA.DeligneAudit.D4Levi.leviColour_isLevi
#print axioms VOA.DeligneAudit.D4Levi.higherOrbit_levi_inv
#print axioms VOA.DeligneAudit.D4Levi.keyQuotCurrent
#print axioms VOA.DeligneAudit.D4Levi.keyQuotCurrent_op
