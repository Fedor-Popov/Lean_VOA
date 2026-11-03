import VOA.DeligneAudit.D4LevelReductionCorePresentation

/-! Positive Cartan currents on bottom words as the two alphabet power-sum shifts. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The Cartan derivative of a bottom word is the sum of its two weighted mode shifts. -/
theorem bottomWord_rawCartan_shifts (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (i : Fin 3) (r : ℕ) (hr : 0 < r)
    (l : List (Fin 6 × ℕ)) (hl : ∀ q ∈ l, q.1 = 1 ∨ q.1 = 5) :
    ρ.op (leviColour (A3Sector.simpleH i)) r (radicalWord ρ w l) =
      (letterWeight i 1 : ℂ) • colourPowerShift ρ w 1 r l +
        (letterWeight i 5 : ℂ) • colourPowerShift ρ w 5 r l := by
  induction l with
  | nil =>
      simpa [radicalWord, wordOp, colourPowerShift] using source_cartan_pos ρ w m h i r hr
  | cons q l ih =>
      rcases q with ⟨j, s⟩
      have hj := hl (j, s) (by simp)
      have ht : ∀ q ∈ l, q.1 = 1 ∨ q.1 = 5 := fun q hq =>
        hl q (List.mem_cons_of_mem (j, s) hq)
      change ρ.op (leviColour (A3Sector.simpleH i)) r
        (ρ.op (radicalColour j) s (radicalWord ρ w l)) = _
      rw [sub_eq_iff_eq_add.mp (cartan_radical_comm ρ i j r s _), ih ht]
      rcases hj with rfl | rfl
      all_goals
        simp only [colourPowerShift, show (1 : Fin 6) ≠ 5 by decide,
          show (5 : Fin 6) ≠ 1 by decide, if_true, if_false, zero_add,
          smul_add, map_add, map_smul, radicalWord, List.map_cons, wordOp]
        abel

/-- The bottom Cartan symbols are the adjoint power sum and minus the two-letter sum. -/
theorem bottomWord_cartanPowerSums (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (i : Fin 3) (r : ℕ) (hr : 0 < r)
    (l : List (Fin 6 × ℕ)) (hl : ∀ q ∈ l, q.1 = 1 ∨ q.1 = 5) :
    (leviCurrent ρ).op (A3Sector.simpleH i) r (radicalWord ρ w l) =
      if i = 1 then -colourPowerShift ρ w 1 r l - colourPowerShift ρ w 5 r l
        else colourPowerShift ρ w 1 r l := by
  have hh := bottomWord_rawCartan_shifts ρ w m h i r hr l hl
  fin_cases i <;>
    simpa [leviCurrent, leviSign, A3Sector.simpleH, letterWeight,
      keyLabel, wordKey, sub_eq_add_neg] using hh

/-- The extra reductive Cartan acts by the negative adjoint-letter power sum. -/
theorem bottomWord_extraCartanPowerSum (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (r : ℕ) (hr : 0 < r)
    (l : List (Fin 6 × ℕ)) (hl : ∀ q ∈ l, q.1 = 1 ∨ q.1 = 5) :
    ρ.op (0 : Fin 28) r (radicalWord ρ w l) = -colourPowerShift ρ w 1 r l := by
  induction l with
  | nil =>
      simpa [radicalWord, wordOp, colourPowerShift] using source_extra_pos ρ w m h r hr
  | cons q l ih =>
      rcases q with ⟨j, s⟩
      have hj := hl (j, s) (by simp)
      have ht : ∀ q ∈ l, q.1 = 1 ∨ q.1 = 5 := fun q hq =>
        hl q (List.mem_cons_of_mem (j, s) hq)
      change ρ.op (0 : Fin 28) r (ρ.op (radicalColour j) s (radicalWord ρ w l)) = _
      rw [sub_eq_iff_eq_add.mp (extra_comm ρ j r s _), ih ht]
      rcases hj with rfl | rfl
      all_goals
        simp [extraWeight, colourPowerShift, radicalWord, wordOp, add_comm]

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.bottomWord_rawCartan_shifts
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomWord_cartanPowerSums
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomWord_extraCartanPowerSum
