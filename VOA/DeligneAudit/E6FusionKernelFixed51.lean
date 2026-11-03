import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_51 :
    (hselK (51 : Fin 78)).val < 6 ∧ fZ brK (hselK (51 : Fin 78)) 51 51 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 51 → fZ brK (hselK (51 : Fin 78)) 51 c = 0 := by
  decide +kernel

theorem low_51 : ∀ c : Fin 78, fZ brK 51 77 c = 0 := by decide +kernel

theorem root_51 :
    6 ≤ (bselK (51 : Fin 78)).val ∧ (bselK (51 : Fin 78)).val < 42 ∧
      kselK (51 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (51 : Fin 78)) 77 c =
        if c = 51 then kselK (51 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
