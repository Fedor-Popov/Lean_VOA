import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_60 :
    (hselK (60 : Fin 78)).val < 6 ∧ fZ brK (hselK (60 : Fin 78)) 60 60 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 60 → fZ brK (hselK (60 : Fin 78)) 60 c = 0 := by
  decide +kernel

theorem low_60 : ∀ c : Fin 78, fZ brK 60 77 c = 0 := by decide +kernel

theorem root_60 :
    6 ≤ (bselK (60 : Fin 78)).val ∧ (bselK (60 : Fin 78)).val < 42 ∧
      kselK (60 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (60 : Fin 78)) 77 c =
        if c = 60 then kselK (60 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
