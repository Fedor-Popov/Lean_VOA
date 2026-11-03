import VOA.DeligneAudit.A3SectorGoal
import VOA.DeligneAudit.DeligneFusionGarlandSl3
import VOA.DeligneAudit.LeviTypeAFinite

/-! High-mode cutoffs for both node-one radical colours of `sl₃`. -/

namespace VOA.DeligneAudit.LeviTypeA

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

private def a2E : Fin 2 → Fin 8 | 0 => 0 | 1 => 1
private def a2F : Fin 2 → Fin 8 | 0 => 3 | 1 => 4
private def a2H : Fin 2 → Fin 8 | 0 => 6 | 1 => 7
private def a2Weight (p q : ℕ) : Fin 2 → ℕ | 0 => p | 1 => q

/-- Garland's single-letter consequence at each simple root. -/
theorem a2_simple_mode_zero (w : V) (p q : ℕ)
    (h : A3Sector.A2LocalWeylRel ρ w p q) (i : Fin 2) (s : ℕ)
    (hs : a2Weight p q i ≤ s) : ρ.op (a2F i) s w = 0 := by
  let Fm : ℕ → Module.End ℂ V := fun r => ρ.op (a2F i) r
  let Hm : ℕ → Module.End ℂ V := fun r => ρ.op (a2H i) r
  let E1 : Module.End ℂ V := ρ.op (a2E i) 1
  have hEF : ∀ k, E1 * Fm k - Fm k * E1 = Hm (k + 1) := by
    intro k
    fin_cases i <;> rw [SectorWeyl.op_comm_end] <;>
      simp [Hm, a2E, a2F, a2H, Fin.sum_univ_eight,
        bracketTable, Nat.add_comm]
  have hHF : ∀ m k, Hm (m + 1) * Fm k - Fm k * Hm (m + 1) =
      (-2 : ℂ) • Fm (m + 1 + k) := by
    intro m k
    fin_cases i <;> rw [SectorWeyl.op_comm_end] <;>
      simp [Fm, a2F, a2H, Fin.sum_univ_eight, bracketTable]
  have hFF : ∀ r t, Fm r * Fm t = Fm t * Fm r := by
    intro r t
    apply sub_eq_zero.mp
    fin_cases i <;> rw [SectorWeyl.op_comm_end] <;>
      simp [a2F, Fin.sum_univ_eight, bracketTable]
  have hE : E1 w = 0 :=
    h.raising (a2E i) (by fin_cases i <;> decide) 1
  have hH : ∀ m, Hm (m + 1) w = 0 := by
    intro m
    exact h.cartan_pos (a2H i) (by fin_cases i <;> decide) _ (by omega)
  have hN : (Fm 0 ^ (a2Weight p q i + 1)) w = 0 := by
    fin_cases i
    · simpa [Fm, a2F, a2Weight, Module.End.pow_apply] using h.lowering_first
    · simpa [Fm, a2F, a2Weight, Module.End.pow_apply] using h.lowering_second
  have hg := Garland.garland hEF hHF hFF hE hH 1 (by omega) hN s (by omega)
  simpa [Garland.Fs, Fm] using hg

/-- The compound lowering current has cutoff `p + q`. -/
theorem a2_compound_mode_zero (w : V) (p q : ℕ)
    (h : A3Sector.A2LocalWeylRel ρ w p q) (s : ℕ) (hs : p + q ≤ s) :
    ρ.op 5 s w = 0 := by
  have hbr : ρ.op 4 q * ρ.op 3 (s - q) -
      ρ.op 3 (s - q) * ρ.op 4 q = ρ.op 5 s := by
    rw [SectorWeyl.op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable, Nat.add_sub_of_le (by omega : q ≤ s)]
  exact next_root_mode_zero (fun r => ρ.op 4 r) (fun r => ρ.op 3 r)
    (fun r => ρ.op 5 r) q s w hbr
    (a2_simple_mode_zero ρ w p q h 1 q (by simp [a2Weight]))
    (a2_simple_mode_zero ρ w p q h 0 (s - q) (by simpa [a2Weight] using
      (show p ≤ s - q by omega)))

/-- The two commuting node-one radical currents. -/
def a2RadicalOp (i : Fin 2) (s : ℕ) : Module.End ℂ V :=
  ρ.op (if i = 0 then 3 else 5) s

theorem a2RadicalOp_comm (i j : Fin 2) (r s : ℕ) :
    a2RadicalOp ρ i r * a2RadicalOp ρ j s =
      a2RadicalOp ρ j s * a2RadicalOp ρ i r := by
  apply sub_eq_zero.mp
  fin_cases i <;> fin_cases j <;>
    simp [a2RadicalOp, SectorWeyl.op_comm_end, Fin.sum_univ_eight, bracketTable]

/-- Each fixed radical depth is finite-dimensional at every weight. -/
theorem a2_radicalLayer_finite (w : V) (p q j : ℕ)
    (h : A3Sector.A2LocalWeylRel ρ w p q) :
    FiniteDimensional ℂ (radicalLayer (a2RadicalOp ρ) w j) := by
  apply radicalLayer_finite (B := p + q) (a2RadicalOp ρ) w
  · exact fun i s j t => a2RadicalOp_comm ρ i j s t
  · intro i s hs
    fin_cases i
    · simpa [a2RadicalOp, a2F] using
        a2_simple_mode_zero ρ w p q h 0 s (by simp [a2Weight]; omega)
    · simpa [a2RadicalOp] using a2_compound_mode_zero ρ w p q h s hs

end VOA.DeligneAudit.LeviTypeA

#print axioms VOA.DeligneAudit.LeviTypeA.a2_simple_mode_zero
#print axioms VOA.DeligneAudit.LeviTypeA.a2_compound_mode_zero
#print axioms VOA.DeligneAudit.LeviTypeA.a2RadicalOp_comm
#print axioms VOA.DeligneAudit.LeviTypeA.a2_radicalLayer_finite
