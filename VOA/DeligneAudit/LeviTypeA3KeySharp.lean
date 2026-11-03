import VOA.DeligneAudit.LeviTypeA3KeyLowerNil
import VOA.DeligneAudit.DeligneFusionCLFilt

/-! Sharp simple Levi lowering relations on a key quotient. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

def a3KeyLabelInt (b c : ℕ) (i : Fin 2) (k : A3RadicalKey) : ℤ :=
  if i = 0 then (b : ℤ) + k.d₁ - k.d₂ else (c : ℤ) + k.d₂ - k.d₃

theorem a3KeyLabel_eq_int (b c : ℕ) (i : Fin 2) (k : A3RadicalKey) :
    a3KeyLabel b c i k = (a3KeyLabelInt b c i k : ℂ) := by
  fin_cases i <;>
    simp [a3KeyLabel, a3KeyLabelInt, Int.cast_sub, Int.cast_add]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem a3_sl3_simple_hw_pow
    (Q : CurrentModule VOA.AffineSl3.bracketTable V)
    (i : Fin 2) (x : V) (m : ℤ) (K : ℕ)
    (he : Q.op (if i = 0 then 0 else 1) 0 x = 0)
    (hh : Q.op (if i = 0 then 6 else 7) 0 x = (m : ℂ) • x)
    (hn : (Q.op (if i = 0 then 3 else 4) 0)^[K] x = 0) :
    (m < 0 → x = 0) ∧
      (0 ≤ m → (Q.op (if i = 0 then 3 else 4) 0)^[m.toNat + 1] x = 0) := by
  let E := Q.op (if i = 0 then 0 else 1) 0
  let F := Q.op (if i = 0 then 3 else 4) 0
  let H := Q.op (if i = 0 then 6 else 7) 0
  have hEF : ∀ u, E (F u) - F (E u) = H u := by
    intro u
    fin_cases i <;> simp [E, F, H, Q.comm,
      Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hHF : ∀ u, H (F u) - F (H u) = (-2 : ℂ) • F u := by
    intro u
    fin_cases i <;> simp [E, F, H, Q.comm,
      Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  exact VOA.DeligneAudit.CLFilt.hw_pow E F H hEF hHF he hh K hn

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyLabel_eq_int
#print axioms VOA.DeligneAudit.A3Sector.a3_sl3_simple_hw_pow
