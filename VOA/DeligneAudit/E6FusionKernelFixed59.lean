import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_59 :
    (hselK (59 : Fin 78)).val < 6 ∧ fZ brK (hselK (59 : Fin 78)) 59 59 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 59 → fZ brK (hselK (59 : Fin 78)) 59 c = 0 := by
  decide +kernel

theorem low_59 : ∀ c : Fin 78, fZ brK 59 77 c = 0 := by decide +kernel

theorem root_59 :
    6 ≤ (bselK (59 : Fin 78)).val ∧ (bselK (59 : Fin 78)).val < 42 ∧
      kselK (59 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (59 : Fin 78)) 77 c =
        if c = 59 then kselK (59 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
