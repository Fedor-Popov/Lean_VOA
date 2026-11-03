import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_46 :
    (hselK (46 : Fin 78)).val < 6 ∧ fZ brK (hselK (46 : Fin 78)) 46 46 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 46 → fZ brK (hselK (46 : Fin 78)) 46 c = 0 := by
  decide +kernel

theorem low_46 : ∀ c : Fin 78, fZ brK 46 77 c = 0 := by decide +kernel

theorem root_46 :
    6 ≤ (bselK (46 : Fin 78)).val ∧ (bselK (46 : Fin 78)).val < 42 ∧
      kselK (46 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (46 : Fin 78)) 77 c =
        if c = 46 then kselK (46 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
