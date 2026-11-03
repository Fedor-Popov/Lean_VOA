import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_64 :
    (hselK (64 : Fin 78)).val < 6 ∧ fZ brK (hselK (64 : Fin 78)) 64 64 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 64 → fZ brK (hselK (64 : Fin 78)) 64 c = 0 := by
  decide +kernel

theorem low_64 : ∀ c : Fin 78, fZ brK 64 77 c = 0 := by decide +kernel

theorem root_64 :
    6 ≤ (bselK (64 : Fin 78)).val ∧ (bselK (64 : Fin 78)).val < 42 ∧
      kselK (64 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (64 : Fin 78)) 77 c =
        if c = 64 then kselK (64 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
