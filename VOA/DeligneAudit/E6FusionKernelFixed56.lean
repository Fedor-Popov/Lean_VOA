import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_56 :
    (hselK (56 : Fin 78)).val < 6 ∧ fZ brK (hselK (56 : Fin 78)) 56 56 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 56 → fZ brK (hselK (56 : Fin 78)) 56 c = 0 := by
  decide +kernel

theorem low_56 : ∀ c : Fin 78, fZ brK 56 77 c = 0 := by decide +kernel

theorem root_56 :
    6 ≤ (bselK (56 : Fin 78)).val ∧ (bselK (56 : Fin 78)).val < 42 ∧
      kselK (56 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (56 : Fin 78)) 77 c =
        if c = 56 then kselK (56 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
