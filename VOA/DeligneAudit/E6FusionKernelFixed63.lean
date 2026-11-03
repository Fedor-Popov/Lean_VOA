import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_63 :
    (hselK (63 : Fin 78)).val < 6 ∧ fZ brK (hselK (63 : Fin 78)) 63 63 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 63 → fZ brK (hselK (63 : Fin 78)) 63 c = 0 := by
  decide +kernel

theorem low_63 : ∀ c : Fin 78, fZ brK 63 77 c = 0 := by decide +kernel

theorem root_63 :
    6 ≤ (bselK (63 : Fin 78)).val ∧ (bselK (63 : Fin 78)).val < 42 ∧
      kselK (63 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (63 : Fin 78)) 77 c =
        if c = 63 then kselK (63 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
