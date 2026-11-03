import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_76 :
    (hselK (76 : Fin 78)).val < 6 ∧ fZ brK (hselK (76 : Fin 78)) 76 76 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 76 → fZ brK (hselK (76 : Fin 78)) 76 c = 0 := by
  decide +kernel

theorem low_76 : ∀ c : Fin 78, fZ brK 76 77 c = 0 := by decide +kernel

theorem root_76 :
    6 ≤ (bselK (76 : Fin 78)).val ∧ (bselK (76 : Fin 78)).val < 42 ∧
      kselK (76 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (76 : Fin 78)) 77 c =
        if c = 76 then kselK (76 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
