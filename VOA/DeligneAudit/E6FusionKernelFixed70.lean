import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_70 :
    (hselK (70 : Fin 78)).val < 6 ∧ fZ brK (hselK (70 : Fin 78)) 70 70 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 70 → fZ brK (hselK (70 : Fin 78)) 70 c = 0 := by
  decide +kernel

theorem low_70 : ∀ c : Fin 78, fZ brK 70 77 c = 0 := by decide +kernel

theorem root_70 :
    6 ≤ (bselK (70 : Fin 78)).val ∧ (bselK (70 : Fin 78)).val < 42 ∧
      kselK (70 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (70 : Fin 78)) 77 c =
        if c = 70 then kselK (70 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
