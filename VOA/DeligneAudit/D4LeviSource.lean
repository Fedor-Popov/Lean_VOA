import VOA.DeligneAudit.D4LeviPBWTable
import VOA.DeligneAudit.LeviTypeA3GradedInductionFinal
import VOA.DeligneAudit.D4FusionKernelGeneric

/-! The ravFam generator restricts to the sl4 local Weyl weight (0,m,0). -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem source_localWeyl
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    VOA.DeligneAudit.A3Sector.LocalWeylRel
      (leviCurrent ρ) w (VOA.DeligneAudit.A3Sector.weightABC 0 m 0) := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he r
    have hraise : D4sector.raising (leviColour e) := by
      fin_cases e <;> simp_all [leviColour, D4sector]
    change (leviSign e : ℂ) • ρ.op (leviColour e) r w = 0
    rw [rs_raising hs hraise r]
    simp
  · intro i r hr
    have hcart : D4sector.cartan
        (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) := by
      change (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)).val < 4
      fin_cases i <;> decide
    change (leviSign (VOA.DeligneAudit.A3Sector.simpleH i) : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r w = 0
    rw [rs_cartan_pos hs hcart r hr]
    simp
  · intro i
    fin_cases i
    · simpa [leviCurrent, leviSign, leviColour,
        VOA.DeligneAudit.A3Sector.simpleH,
        VOA.DeligneAudit.A3Sector.weightABC, D4sector, thetaD4] using
          (rs_cartan_zero hs (by change 2 < 4; decide : D4sector.cartan (2 : Fin 28)))
    · simpa [leviCurrent, leviSign, leviColour,
        VOA.DeligneAudit.A3Sector.simpleH,
        VOA.DeligneAudit.A3Sector.weightABC, D4sector, thetaD4] using
          (rs_cartan_zero hs (by change 1 < 4; decide : D4sector.cartan (1 : Fin 28)))
    · simpa [leviCurrent, leviSign, leviColour,
        VOA.DeligneAudit.A3Sector.simpleH,
        VOA.DeligneAudit.A3Sector.weightABC, D4sector, thetaD4] using
          (rs_cartan_zero hs (by change 3 < 4; decide : D4sector.cartan (3 : Fin 28)))
  · intro i
    fin_cases i
    · simpa [leviCurrent, leviSign, leviColour,
        VOA.DeligneAudit.A3Sector.simpleF,
        VOA.DeligneAudit.A3Sector.weightABC, D4sector, lowExpD4] using
          (rs_lowering hs (by change 16 ≤ 17 ∧ 17 < 20; decide :
            D4sector.lowering (17 : Fin 28)))
    · simpa [leviCurrent, leviSign, leviColour,
        VOA.DeligneAudit.A3Sector.simpleF,
        VOA.DeligneAudit.A3Sector.weightABC, D4sector, lowExpD4] using
          (rs_lowering hs (by change 16 ≤ 18 ∧ 18 < 20; decide :
            D4sector.lowering (18 : Fin 28)))
    · have hnil := rs_lowering hs
        (by change 16 ≤ 16 ∧ 16 < 20; decide : D4sector.lowering (16 : Fin 28))
      have hzero : ρ.op (16 : Fin 28) 0 w = 0 := by
        simpa [D4sector, lowExpD4, Function.iterate_one] using hnil
      simpa [leviCurrent, leviSign, leviColour,
        VOA.DeligneAudit.A3Sector.simpleF,
        VOA.DeligneAudit.A3Sector.weightABC, Function.iterate_one,
        LinearMap.smul_apply] using congrArg Neg.neg hzero

/-- At the source, the restricted cyclic sl4 module has rank at most 6^m. -/
theorem source_levi_rank
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    FiniteDimensional ℂ
      (cycSubG (leviCurrent ρ) w) ∧
      Module.finrank ℂ (cycSubG (leviCurrent ρ) w) ≤ 6 ^ m := by
  simpa using VOA.DeligneAudit.A3Sector.a3_all_weight_rank
    (leviCurrent ρ) w 0 m 0 (source_localWeyl ρ w m h)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.source_localWeyl
#print axioms VOA.DeligneAudit.D4Levi.source_levi_rank
