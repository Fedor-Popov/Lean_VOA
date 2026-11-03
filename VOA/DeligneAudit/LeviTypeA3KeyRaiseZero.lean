import VOA.DeligneAudit.LeviTypeA3KeyRaising

/-! A raising mode kills radical words with no letter that it can replace. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

def a3RaiseSource : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 2

def a3RaiseDest : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1

theorem a3RaiseTarget_eq (i j : Fin 3) :
    a3RaiseTarget i j =
      if j = a3RaiseSource i then some (a3RaiseDest i) else none := by
  fin_cases i <;> fin_cases j <;> decide

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_raising_word_zero_no_source (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (r : ℕ) (l : List (Fin 3 × ℕ))
    (hl : l.countP (fun x => x.1 = a3RaiseSource i) = 0) :
    ρ.op (leviE i) r (radicalWord (radicalOp ρ) l • w) = 0 := by
  induction l with
  | nil =>
      simpa [radicalWord] using h.raising (leviE i)
        (by fin_cases i <;> decide) r
  | cons x l ih =>
      rcases x with ⟨j, s⟩
      have hj : j ≠ a3RaiseSource i := by
        intro heq
        subst j
        simp at hl
      have ht : l.countP (fun x => x.1 = a3RaiseSource i) = 0 := by
        simpa [hj] using hl
      have hc := a3_raising_comm ρ i j r s
        (radicalWord (radicalOp ρ) l • w)
      rw [a3RaiseTarget_eq, if_neg hj] at hc
      change ρ.op (leviE i) r
        (radicalOp ρ j s (radicalWord (radicalOp ρ) l • w)) = 0
      rw [sub_eq_zero.mp hc, ih ht]
      simp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3RaiseTarget_eq
#print axioms VOA.DeligneAudit.A3Sector.a3_raising_word_zero_no_source
