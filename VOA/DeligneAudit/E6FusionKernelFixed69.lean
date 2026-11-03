import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_69 :
    (hselK (69 : Fin 78)).val < 6 ∧ fZ brK (hselK (69 : Fin 78)) 69 69 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 69 → fZ brK (hselK (69 : Fin 78)) 69 c = 0 := by
  decide +kernel

theorem low_69 : ∀ c : Fin 78, fZ brK 69 77 c = 0 := by decide +kernel

theorem root_69 :
    6 ≤ (bselK (69 : Fin 78)).val ∧ (bselK (69 : Fin 78)).val < 42 ∧
      kselK (69 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (69 : Fin 78)) 77 c =
        if c = 69 then kselK (69 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
