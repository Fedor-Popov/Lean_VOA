import VOA.DeligneAudit.D4LeviLowerNil

/-! Lowering nilpotence descends to the higher-key quotient. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem key_simple_lower_nil_levi
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ((leviCurrent ρ).op (VOA.DeligneAudit.A3Sector.simpleF i) 0 ^
      (lowerBaseExponent m i + 2 * keyDepth k)) v = 0 := by
  have hn := key_simple_lower_nil ρ w m h i k hv
  fin_cases i
  · simpa [leviCurrent, leviSign, leviColour,
      VOA.DeligneAudit.A3Sector.simpleF, simpleLowerIndex,
      lowerColour] using hn
  · simpa [leviCurrent, leviSign, leviColour,
      VOA.DeligneAudit.A3Sector.simpleF, simpleLowerIndex,
      lowerColour] using hn
  · simp only [leviCurrent, leviSign, leviColour,
      VOA.DeligneAudit.A3Sector.simpleF, Int.cast_neg,
      Int.cast_one, neg_one_smul]
    have hn' : (ρ.op (16 : Fin 28) 0 ^
        (lowerBaseExponent m 2 + 2 * keyDepth k)) v = 0 := by
      simpa [simpleLowerIndex, lowerColour] using hn
    rw [neg_pow]
    simp [hn']

theorem key_simple_lower_nil_quot
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ((keyQuotCurrent ρ w m k).op
      (VOA.DeligneAudit.A3Sector.simpleF i) 0)^[
        lowerBaseExponent m i + 2 * keyDepth k]
      ((higherOrbit ρ w m k).mkQ v) = 0 := by
  let N := higherOrbit ρ w m k
  let Q := keyQuotCurrent ρ w m k
  have hiter : ∀ n (u : V),
      (Q.op (VOA.DeligneAudit.A3Sector.simpleF i) 0)^[n] (N.mkQ u) =
        N.mkQ (((leviCurrent ρ).op
          (VOA.DeligneAudit.A3Sector.simpleF i) 0)^[n] u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
        intro u
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        rfl
  change (Q.op (VOA.DeligneAudit.A3Sector.simpleF i) 0)^[
    lowerBaseExponent m i + 2 * keyDepth k] (N.mkQ v) = 0
  rw [hiter, ← Module.End.pow_apply, key_simple_lower_nil_levi ρ w m h i k hv]
  exact map_zero _

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.key_simple_lower_nil_levi
#print axioms VOA.DeligneAudit.D4Levi.key_simple_lower_nil_quot
