import VOA.DeligneAudit.D4LeviKeyCartanPos

/-! The simple-Cartan local Weyl relations in a higher-key quotient. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem key_cartan_pos_quot
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (hr : 0 < r) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    (keyQuotCurrent ρ w m k).op (VOA.DeligneAudit.A3Sector.simpleH i) r
      ((higherOrbit ρ w m k).mkQ v) = 0 := by
  have hm := cartan_pos_mem_higher ρ w m h i r hr k hv
  rw [keyQuotCurrent_op]
  fin_cases i <;>
    simpa [leviCurrent, leviSign, leviColour,
      VOA.DeligneAudit.A3Sector.simpleH] using
        (Submodule.Quotient.mk_eq_zero (higherOrbit ρ w m k)).mpr hm

theorem key_cartan_zero_quot
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    (keyQuotCurrent ρ w m k).op (VOA.DeligneAudit.A3Sector.simpleH i) 0
      ((higherOrbit ρ w m k).mkQ v) =
        (keyLabel m i k : ℂ) • (higherOrbit ρ w m k).mkQ v := by
  have hw := cartan_weight_key ρ w m h i k hv
  have hw' := congrArg (higherOrbit ρ w m k).mkQ hw
  rw [keyQuotCurrent_op]
  fin_cases i <;>
    simpa [leviCurrent, leviSign, leviColour,
      VOA.DeligneAudit.A3Sector.simpleH, map_smul] using
        hw'

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.key_cartan_pos_quot
#print axioms VOA.DeligneAudit.D4Levi.key_cartan_zero_quot
