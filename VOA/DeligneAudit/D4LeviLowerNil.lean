import VOA.DeligneAudit.D4LeviLowerAd

/-! Uniform simple-Levi lowering nilpotence on each exact key layer. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.FiniteG

def lowerBaseExponent (m : ℕ) (i : Fin 3) : ℕ :=
  if i = 1 then m + 1 else 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem source_simple_lower_nil
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (i : Fin 3) :
    (ρ.op (lowerColour (simpleLowerIndex i)) 0 ^
      lowerBaseExponent m i) w = 0 := by
  have hh := source_root_nil ρ w m h
    (lowerColour (simpleLowerIndex i))
    (by fin_cases i <;> decide)
  fin_cases i <;>
    simpa [lowerBaseExponent, rootExponent, simpleLowerIndex, lowerColour]
      using hh

theorem simple_lower_nil_word
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (l : List (Fin 6 × ℕ)) :
    (ρ.op (lowerColour (simpleLowerIndex i)) 0 ^
      (lowerBaseExponent m i + 2 * l.length)) (radicalWord ρ w l) = 0 := by
  induction l with
  | nil =>
      simpa [radicalWord] using source_simple_lower_nil ρ w m h i
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      have hp := pow_kill_of_ad
        (ρ.op (lowerColour (simpleLowerIndex i)) 0)
        (ρ.op (radicalColour j) s) 2
        (lowerBaseExponent m i + 2 * l.length)
        (radicalWord ρ w l)
        (simple_lower_ad_two ρ i j s) ih
      change (ρ.op (lowerColour (simpleLowerIndex i)) 0 ^
        (lowerBaseExponent m i + 2 * (l.length + 1)))
          (ρ.op (radicalColour j) s (radicalWord ρ w l)) = 0
      convert hp using 1 <;> ring

theorem key_simple_lower_nil
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    (ρ.op (lowerColour (simpleLowerIndex i)) 0 ^
      (lowerBaseExponent m i + 2 * keyDepth k)) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hkey, rfl⟩ := hz
      have hlen : l.length = keyDepth k := by
        simpa [← hkey] using (wordKey_depth l).symm
      simpa only [hlen] using simple_lower_nil_word ρ w m h i l
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.source_simple_lower_nil
#print axioms VOA.DeligneAudit.D4Levi.simple_lower_nil_word
#print axioms VOA.DeligneAudit.D4Levi.key_simple_lower_nil
