import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_42 :
    (hselK (42 : Fin 78)).val < 6 ∧ fZ brK (hselK (42 : Fin 78)) 42 42 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 42 → fZ brK (hselK (42 : Fin 78)) 42 c = 0 := by
  decide +kernel

theorem low_42 : ∀ c : Fin 78, fZ brK 42 77 c = 0 := by decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
