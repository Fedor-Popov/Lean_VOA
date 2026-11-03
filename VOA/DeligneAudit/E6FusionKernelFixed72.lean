import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_72 :
    (hselK (72 : Fin 78)).val < 6 ∧ fZ brK (hselK (72 : Fin 78)) 72 72 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 72 → fZ brK (hselK (72 : Fin 78)) 72 c = 0 := by
  decide +kernel

theorem low_72 : ∀ c : Fin 78, fZ brK 72 77 c = 0 := by decide +kernel

theorem root_72 :
    6 ≤ (bselK (72 : Fin 78)).val ∧ (bselK (72 : Fin 78)).val < 42 ∧
      kselK (72 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (72 : Fin 78)) 77 c =
        if c = 72 then kselK (72 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
