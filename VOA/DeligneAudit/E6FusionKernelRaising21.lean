import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem raising_21 : ∀ c : Fin 78, fZ brK 21 77 c ≠ 0 →
    c.val < 6 ∨ (c.val ∈ fusL ∧ c ≠ 77) := by decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
