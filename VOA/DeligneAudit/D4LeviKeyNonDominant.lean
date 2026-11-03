import VOA.DeligneAudit.D4LeviExtraCartanPositive

/-! A key with a negative simple sl4 label vanishes in its higher-key quotient. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem key_non_dominant_quot_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hneg : ∃ i : Fin 3, keyLabel m i k < 0)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    (higherOrbit ρ w m k).mkQ v = 0 := by
  obtain ⟨i, hi⟩ := hneg
  exact (key_simple_sharp_quot ρ w m h i k hv).1 hi

theorem keyLayer_le_higher_of_non_dominant
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hneg : ∃ i : Fin 3, keyLabel m i k < 0) :
    keyLayer ρ w k ≤ higherOrbit ρ w m k := by
  intro v hv
  exact (Submodule.Quotient.mk_eq_zero (higherOrbit ρ w m k)).mp
    (key_non_dominant_quot_zero ρ w m h k hneg hv)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.key_non_dominant_quot_zero
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_higher_of_non_dominant
