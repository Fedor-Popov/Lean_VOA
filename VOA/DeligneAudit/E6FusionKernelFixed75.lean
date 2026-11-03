import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_75 :
    (hselK (75 : Fin 78)).val < 6 ∧ fZ brK (hselK (75 : Fin 78)) 75 75 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 75 → fZ brK (hselK (75 : Fin 78)) 75 c = 0 := by
  decide +kernel

theorem low_75 : ∀ c : Fin 78, fZ brK 75 77 c = 0 := by decide +kernel

theorem root_75 :
    6 ≤ (bselK (75 : Fin 78)).val ∧ (bselK (75 : Fin 78)).val < 42 ∧
      kselK (75 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (75 : Fin 78)) 77 c =
        if c = 75 then kselK (75 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
