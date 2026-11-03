import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_62 :
    (hselK (62 : Fin 78)).val < 6 ∧ fZ brK (hselK (62 : Fin 78)) 62 62 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 62 → fZ brK (hselK (62 : Fin 78)) 62 c = 0 := by
  decide +kernel

theorem low_62 : ∀ c : Fin 78, fZ brK 62 77 c = 0 := by decide +kernel

theorem root_62 :
    6 ≤ (bselK (62 : Fin 78)).val ∧ (bselK (62 : Fin 78)).val < 42 ∧
      kselK (62 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (62 : Fin 78)) 77 c =
        if c = 62 then kselK (62 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
