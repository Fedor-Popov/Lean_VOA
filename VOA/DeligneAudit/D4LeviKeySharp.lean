import VOA.DeligneAudit.D4LeviAllRaise
import VOA.DeligneAudit.D4LeviKeyCartanQuot
import VOA.DeligneAudit.DeligneFusionCLFilt

/-! Sharp simple lowering powers, including vanishing for a negative key label. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem key_simple_sharp_quot
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    let N := higherOrbit ρ w m k
    let Q := keyQuotCurrent ρ w m k
    let lam := keyLabel m i k
    (lam < 0 → N.mkQ v = 0) ∧
      (0 ≤ lam → (Q.op (VOA.DeligneAudit.A3Sector.simpleF i) 0)^[
        lam.toNat + 1] (N.mkQ v) = 0) := by
  dsimp
  let N := higherOrbit ρ w m k
  let Q := keyQuotCurrent ρ w m k
  let E := Q.op (VOA.DeligneAudit.A3Sector.simpleE i) 0
  let F := Q.op (VOA.DeligneAudit.A3Sector.simpleF i) 0
  let H := Q.op (VOA.DeligneAudit.A3Sector.simpleH i) 0
  have hEF : ∀ u, E (F u) - F (E u) = H u := by
    intro u
    dsimp [E, F, H]
    rw [Q.comm]
    simp [VOA.DeligneAudit.A3Sector.simple_ef_table]
  have hHF : ∀ u, H (F u) - F (H u) = (-2 : ℂ) • F u := by
    intro u
    dsimp [E, F, H]
    rw [Q.comm]
    simp [VOA.DeligneAudit.A3Sector.simple_hf_table]
  have he : E (N.mkQ v) = 0 := key_simple_raise_quot ρ w m h i 0 k hv
  have hh : H (N.mkQ v) = (keyLabel m i k : ℂ) • N.mkQ v :=
    key_cartan_zero_quot ρ w m h i k hv
  let K := lowerBaseExponent m i + 2 * keyDepth k
  have hn : F^[K] (N.mkQ v) = 0 :=
    key_simple_lower_nil_quot ρ w m h i k hv
  exact VOA.DeligneAudit.CLFilt.hw_pow E F H hEF hHF he hh K hn

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.key_simple_sharp_quot
