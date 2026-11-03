import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem small_simpleZ : (∀ c : Fin 78, fZ brK 10 46 c = if c = 1 then 1 else 0) ∧
    (∀ c : Fin 78, fZ brK 1 46 c = if c = 46 then -2 else 0) := by decide +kernel

theorem small_eθZ : (∀ c : Fin 78, fZ brK 41 77 c ≠ 0 → c.val < 6) ∧ fZ brK 41 77 1 = -2 := by
  decide +kernel
end
end VOA.DeligneAudit.UnivG.E6K
