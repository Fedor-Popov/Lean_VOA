import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_71 :
    (hselK (71 : Fin 78)).val < 6 ∧ fZ brK (hselK (71 : Fin 78)) 71 71 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 71 → fZ brK (hselK (71 : Fin 78)) 71 c = 0 := by
  decide +kernel

theorem low_71 : ∀ c : Fin 78, fZ brK 71 77 c = 0 := by decide +kernel

theorem root_71 :
    6 ≤ (bselK (71 : Fin 78)).val ∧ (bselK (71 : Fin 78)).val < 42 ∧
      kselK (71 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (71 : Fin 78)) 77 c =
        if c = 71 then kselK (71 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
