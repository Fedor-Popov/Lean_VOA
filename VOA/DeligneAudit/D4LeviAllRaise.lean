import VOA.DeligneAudit.D4LeviKeyRaise

/-! All six positive sl4 currents vanish on an exact key in the quotient. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

private theorem positive_pair_table (c : Fin 3) (z : Fin 15) :
    VOA.DeligneAudit.A3Sector.bracketTable
      (if c = 2 then 0 else if c = 1 then 0 else 3)
      (if c = 2 then 4 else if c = 1 then 3 else 5) z =
        if z = (if c = 2 then 2 else if c = 1 then 1 else 4) then 1 else 0 := by
  have ht : VOA.DeligneAudit.A3Sector.bracketInt
      (if c = 2 then 0 else if c = 1 then 0 else 3)
      (if c = 2 then 4 else if c = 1 then 3 else 5) z =
        if z = (if c = 2 then 2 else if c = 1 then 1 else 4)
          then 1 else 0 := by
    fin_cases c <;> fin_cases z <;> decide
  simpa [VOA.DeligneAudit.A3Sector.bracketTable, ht]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.DeligneAudit.A3Sector.bracketTable V)

private theorem positive_pair_op (c : Fin 3) (r s : ℕ) (v : V) :
    Q.op (if c = 2 then 2 else if c = 1 then 1 else 4) (r + s) v =
      Q.op (if c = 2 then 0 else if c = 1 then 0 else 3) r
        (Q.op (if c = 2 then 4 else if c = 1 then 3 else 5) s v) -
      Q.op (if c = 2 then 4 else if c = 1 then 3 else 5) s
        (Q.op (if c = 2 then 0 else if c = 1 then 0 else 3) r v) := by
  rw [Q.comm]
  simp only [positive_pair_table, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, one_smul]

theorem positive_zero_of_simple (v : V)
    (h : ∀ i : Fin 3, ∀ r,
      Q.op (VOA.DeligneAudit.A3Sector.simpleE i) r v = 0)
    (e : Fin 15) (he : e.val < 6) (r : ℕ) : Q.op e r v = 0 := by
  have h0 : ∀ s, Q.op 0 s v = 0 := by
    intro s
    exact h 0 s
  have h3 : ∀ s, Q.op 3 s v = 0 := by
    intro s
    exact h 1 s
  have h5 : ∀ s, Q.op 5 s v = 0 := by
    intro s
    exact h 2 s
  have h4 : ∀ s, Q.op 4 s v = 0 := by
    intro s
    have hc := positive_pair_op Q 0 0 s v
    simpa [h3, h5] using hc
  have h1 : ∀ s, Q.op 1 s v = 0 := by
    intro s
    have hc := positive_pair_op Q 1 0 s v
    simpa [h0, h3] using hc
  have h2 : ∀ s, Q.op 2 s v = 0 := by
    intro s
    have hc := positive_pair_op Q 2 0 s v
    simpa [h0, h4] using hc
  fin_cases e
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r
  all_goals simp at he

variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem key_all_raise_quot
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k)
    (e : Fin 15) (he : e.val < 6) (r : ℕ) :
    (keyQuotCurrent ρ w m k).op e r
      ((higherOrbit ρ w m k).mkQ v) = 0 := by
  apply positive_zero_of_simple (keyQuotCurrent ρ w m k) _
    (fun i s => key_simple_raise_quot ρ w m h i s k hv) e he r

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.positive_zero_of_simple
#print axioms VOA.DeligneAudit.D4Levi.key_all_raise_quot
