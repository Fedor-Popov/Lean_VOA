import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_68 :
    (hselK (68 : Fin 78)).val < 6 ∧ fZ brK (hselK (68 : Fin 78)) 68 68 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 68 → fZ brK (hselK (68 : Fin 78)) 68 c = 0 := by
  decide +kernel

theorem low_68 : ∀ c : Fin 78, fZ brK 68 77 c = 0 := by decide +kernel

theorem root_68 :
    6 ≤ (bselK (68 : Fin 78)).val ∧ (bselK (68 : Fin 78)).val < 42 ∧
      kselK (68 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (68 : Fin 78)) 77 c =
        if c = 68 then kselK (68 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
