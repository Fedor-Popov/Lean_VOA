import VOA.DeligneAudit.LeviTypeA3KeyLowerAd

/-! A uniform local nilpotence bound for both simple Levi lowerings. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.FiniteG
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_lowering_nilpotent_word (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (l : List (Fin 3 × ℕ)) :
    (ρ.op (leviF i) 0 ^ ((if i = 0 then b else c) + 1 + 2 * l.length))
      (radicalWord (radicalOp ρ) l • w) = 0 := by
  induction l with
  | nil =>
      fin_cases i
      · simpa [radicalWord, leviF, simpleF, weightABC,
          Module.End.pow_apply] using h.lowering 1
      · simpa [radicalWord, leviF, simpleF, weightABC,
          Module.End.pow_apply] using h.lowering 2
  | cons x l ih =>
      rcases x with ⟨j, s⟩
      have hp := pow_kill_of_ad (ρ.op (leviF i) 0) (radicalOp ρ j s)
        2 ((if i = 0 then b else c) + 1 + 2 * l.length)
        (radicalWord (radicalOp ρ) l • w)
        (a3_lowering_ad_two ρ i j s) ih
      change (ρ.op (leviF i) 0 ^
        ((if i = 0 then b else c) + 1 + 2 * (l.length + 1)))
        (radicalOp ρ j s (radicalWord (radicalOp ρ) l • w)) = 0
      convert hp using 1 <;> ring

theorem a3_key_lowering_nilpotent (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) :
    (ρ.op (leviF i) 0 ^
      ((if i = 0 then b else c) + 1 + 2 * (k.d₁ + k.d₂ + k.d₃))) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, _, _, _, _, hlen, rfl⟩ := hz
      simpa only [hlen] using a3_lowering_nilpotent_word ρ w a b c h i l
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul d x _ hx => simp [map_smul, hx]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_lowering_nilpotent_word
#print axioms VOA.DeligneAudit.A3Sector.a3_key_lowering_nilpotent
