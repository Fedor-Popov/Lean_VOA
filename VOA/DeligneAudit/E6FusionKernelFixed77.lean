import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_77 :
    (hselK (77 : Fin 78)).val < 6 ∧ fZ brK (hselK (77 : Fin 78)) 77 77 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 77 → fZ brK (hselK (77 : Fin 78)) 77 c = 0 := by
  decide +kernel

theorem low_77 : ∀ c : Fin 78, fZ brK 77 77 c = 0 := by decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
