import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_47 :
    (hselK (47 : Fin 78)).val < 6 ∧ fZ brK (hselK (47 : Fin 78)) 47 47 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 47 → fZ brK (hselK (47 : Fin 78)) 47 c = 0 := by
  decide +kernel

theorem low_47 : ∀ c : Fin 78, fZ brK 47 77 c = 0 := by decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
