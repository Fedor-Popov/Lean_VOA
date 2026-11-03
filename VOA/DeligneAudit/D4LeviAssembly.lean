import VOA.DeligneAudit.D4LeviSource
import VOA.DeligneAudit.D4LeviGeneration
import VOA.DeligneAudit.D4LeviRootNil

/-! Joint first-layer certificate for every multiplicity in the D4 presentation. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Generation, source Levi rank, and all positive-root zero-mode powers. -/
theorem first_layer
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    cycSubG ρ w = leviSpan ρ w ∧
    FiniteDimensional ℂ (cycSubG (leviCurrent ρ) w) ∧
    Module.finrank ℂ (cycSubG (leviCurrent ρ) w) ≤ 6 ^ m ∧
    (∀ c : Fin 28, 16 ≤ c.val →
      ((ρ.op c 0) ^ rootExponent m c) w = 0) := by
  obtain ⟨hfd, hrank⟩ := source_levi_rank ρ w m h
  exact ⟨source_generation ρ w m h, hfd, hrank,
    fun c hc => source_root_nil ρ w m h c hc⟩

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.first_layer
