import VOA.DeligneAudit.LeviTypeA3KeyRaiseQuot
import VOA.DeligneAudit.DeligneFusionFiniteGAlg

/-! The two simple Levi lowerings have adjoint length at most two on radical letters. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.FiniteG

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

private theorem op_comm_end (x y : Fin 15) (r s : ℕ) :
    ρ.op x r * ρ.op y s - ρ.op y s * ρ.op x r =
      ∑ e, bracketTable x y e • ρ.op e (r + s) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  exact ρ.comm x y r s v

theorem a3_lowering_ad_radical (i : Fin 2) (j : Fin 3) (s : ℕ) :
    adR (ρ.op (leviF i) 0) (radicalOp ρ j s) =
      if i = 0 ∧ j = 0 then radicalOp ρ 1 s else
      if i = 1 ∧ j = 1 then radicalOp ρ 2 s else 0 := by
  rw [adR_apply]
  change ρ.op (leviF i) 0 * ρ.op (F j) s -
    ρ.op (F j) s * ρ.op (leviF i) 0 = _
  rw [op_comm_end]
  fin_cases i <;> fin_cases j
  · simp [radicalOp, levi_step_one]
  · simp [radicalOp, levi_other_zero 0 1 (by decide)]
  · simp [radicalOp, levi_other_zero 0 2 (by decide)]
  · simp [radicalOp, levi_other_zero 1 0 (by decide)]
  · simp [radicalOp, levi_step_two]
  · simp [radicalOp, levi_other_zero 1 2 (by decide)]

theorem a3_lowering_ad_two (i : Fin 2) (j : Fin 3) (s : ℕ) :
    (adR (ρ.op (leviF i) 0))^[2] (radicalOp ρ j s) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 by decide, Function.iterate_add_apply]
  simp only [Function.iterate_one]
  rw [a3_lowering_ad_radical]
  fin_cases i <;> fin_cases j <;>
    simp [a3_lowering_ad_radical, adR_apply]
  all_goals
    rw [← adR_apply, a3_lowering_ad_radical]
    simp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_lowering_ad_radical
#print axioms VOA.DeligneAudit.A3Sector.a3_lowering_ad_two
