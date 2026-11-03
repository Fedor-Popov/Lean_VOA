import VOA.DeligneAudit.D4LeviRaiseWord

/-! Simple Levi raising modes vanish on key vectors modulo higher orbits. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem simple_raise_key_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r v ∈
      higherOrbit ρ w m k := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hkey, rfl⟩ := hz
      rw [← hkey]
      exact simple_raise_word_higher ρ w m h i r l
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (higherOrbit ρ w m k).add_mem hx hy
  | smul c x _ hx =>
      simpa using (higherOrbit ρ w m k).smul_mem c hx

theorem key_simple_raise_quot
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    (keyQuotCurrent ρ w m k).op
      (VOA.DeligneAudit.A3Sector.simpleE i) r
      ((higherOrbit ρ w m k).mkQ v) = 0 := by
  have hm := simple_raise_key_higher ρ w m h i r k hv
  rw [keyQuotCurrent_op]
  fin_cases i <;>
    simpa [leviCurrent, leviSign, leviColour,
      VOA.DeligneAudit.A3Sector.simpleE] using
        (Submodule.Quotient.mk_eq_zero (higherOrbit ρ w m k)).mpr hm

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.simple_raise_key_higher
#print axioms VOA.DeligneAudit.D4Levi.key_simple_raise_quot
