import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_45 :
    (hselK (45 : Fin 78)).val < 6 ∧ fZ brK (hselK (45 : Fin 78)) 45 45 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 45 → fZ brK (hselK (45 : Fin 78)) 45 c = 0 := by
  decide +kernel

theorem low_45 : ∀ c : Fin 78, fZ brK 45 77 c = 0 := by decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
