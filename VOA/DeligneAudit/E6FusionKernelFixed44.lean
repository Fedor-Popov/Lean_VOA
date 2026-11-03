import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_44 :
    (hselK (44 : Fin 78)).val < 6 ∧ fZ brK (hselK (44 : Fin 78)) 44 44 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 44 → fZ brK (hselK (44 : Fin 78)) 44 c = 0 := by
  decide +kernel

theorem low_44 : ∀ c : Fin 78, fZ brK 44 77 c = 0 := by decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
