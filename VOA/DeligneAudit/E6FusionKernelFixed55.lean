import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_55 :
    (hselK (55 : Fin 78)).val < 6 ∧ fZ brK (hselK (55 : Fin 78)) 55 55 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 55 → fZ brK (hselK (55 : Fin 78)) 55 c = 0 := by
  decide +kernel

theorem low_55 : ∀ c : Fin 78, fZ brK 55 77 c = 0 := by decide +kernel

theorem root_55 :
    6 ≤ (bselK (55 : Fin 78)).val ∧ (bselK (55 : Fin 78)).val < 42 ∧
      kselK (55 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (55 : Fin 78)) 77 c =
        if c = 55 then kselK (55 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
