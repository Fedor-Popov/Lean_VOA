import VOA.DeligneAudit.LeviTypeA2CertHigher
import VOA.DeligneAudit.DeligneFusionFiniteGNil
import VOA.DeligneAudit.DeligneSectorA2

/-! Uniform zero-mode lowering nilpotence on each radical key layer. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.FiniteG
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem radicalWord_as_wordOp (l : List (Fin 2 × ℕ)) :
    wordOp ρ (l.map fun x =>
      ((if x.1 = 0 then 3 else 5 : Fin 8), x.2)) w =
      radicalWord (a2RadicalOp ρ) l • w := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨i, s⟩
      fin_cases i
      · simpa [wordOp, radicalWord, a2RadicalOp] using congrArg (ρ.op 3 s) ih
      · simpa [wordOp, radicalWord, a2RadicalOp] using congrArg (ρ.op 5 s) ih

/-- The node-two lowering operator kills every vector of a fixed radical key
after a common power. The bound comes from the generic current-word lemma. -/
theorem a2_key_lowering_nilpotent (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    (ρ.op 4 0 ^ (q + 1 + adK A2sector * (k.d₁ + k.d₂))) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, _, _, _, hlen, rfl⟩ := hz
      let l' : List (Fin 8 × ℕ) :=
        l.map fun x => ((if x.1 = 0 then 3 else 5 : Fin 8), x.2)
      have hw : (ρ.op 4 0 ^ (q + 1)) w = 0 := by
        simpa [Module.End.pow_apply] using h.lowering_second
      have hwt : A2sector.wt (4 : Fin 8) ≠ 0 := by
        decide
      have hpow := pow_kill_word (S := A2sector) ρ
        (⟨4, by decide⟩ : Fin A2sector.n) hwt hw l'
      have hword : wordOp ρ l' w = radicalWord (a2RadicalOp ρ) l • w :=
        radicalWord_as_wordOp ρ w l
      change (ρ.op 4 0 ^ (q + 1 + adK A2sector * l'.length))
        (wordOp ρ l' w) = 0 at hpow
      rw [hword] at hpow
      simpa only [l', List.length_map, hlen] using hpow
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_lowering_nilpotent
