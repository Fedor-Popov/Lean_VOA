import VOA.DeligneAudit.LeviTypeA2CertSl2Bound
import VOA.DeligneAudit.LeviTypeA2CertKeyClosure

/-! The node-two current triple is an `sl₂[t]` action. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2
open VOA.AffineSl3

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

/-- The node-two `e₂, h₂, f₂` modes satisfy the current `sl₂` table. -/
theorem a2_node2_sl2 :
    SL2 (fun r => ρ.op 1 r) (fun r => ρ.op 7 r) (fun r => ρ.op 4 r) := by
  refine ⟨fun s k => ?_, fun s k => ?_, fun s k => ?_,
    fun s k => ?_, fun s k => ?_⟩
  · rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · apply sub_eq_zero.mp
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · apply sub_eq_zero.mp
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_node2_sl2
