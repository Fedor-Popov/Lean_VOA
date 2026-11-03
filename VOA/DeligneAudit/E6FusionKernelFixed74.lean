import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_74 :
    (hselK (74 : Fin 78)).val < 6 ∧ fZ brK (hselK (74 : Fin 78)) 74 74 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 74 → fZ brK (hselK (74 : Fin 78)) 74 c = 0 := by
  decide +kernel

theorem low_74 : ∀ c : Fin 78, fZ brK 74 77 c = 0 := by decide +kernel

theorem root_74 :
    6 ≤ (bselK (74 : Fin 78)).val ∧ (bselK (74 : Fin 78)).val < 42 ∧
      kselK (74 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (74 : Fin 78)) 77 c =
        if c = 74 then kselK (74 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
