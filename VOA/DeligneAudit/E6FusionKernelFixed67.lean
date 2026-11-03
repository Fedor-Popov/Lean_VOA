import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_67 :
    (hselK (67 : Fin 78)).val < 6 ∧ fZ brK (hselK (67 : Fin 78)) 67 67 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 67 → fZ brK (hselK (67 : Fin 78)) 67 c = 0 := by
  decide +kernel

theorem low_67 : ∀ c : Fin 78, fZ brK 67 77 c = 0 := by decide +kernel

theorem root_67 :
    6 ≤ (bselK (67 : Fin 78)).val ∧ (bselK (67 : Fin 78)).val < 42 ∧
      kselK (67 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (67 : Fin 78)) 77 c =
        if c = 67 then kselK (67 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
