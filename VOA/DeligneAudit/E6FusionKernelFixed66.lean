import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_66 :
    (hselK (66 : Fin 78)).val < 6 ∧ fZ brK (hselK (66 : Fin 78)) 66 66 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 66 → fZ brK (hselK (66 : Fin 78)) 66 c = 0 := by
  decide +kernel

theorem low_66 : ∀ c : Fin 78, fZ brK 66 77 c = 0 := by decide +kernel

theorem root_66 :
    6 ≤ (bselK (66 : Fin 78)).val ∧ (bselK (66 : Fin 78)).val < 42 ∧
      kselK (66 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (66 : Fin 78)) 77 c =
        if c = 66 then kselK (66 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
