import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem trunc_73 :
    (hselK (73 : Fin 78)).val < 6 ∧ fZ brK (hselK (73 : Fin 78)) 73 73 ≠ 0 ∧
      ∀ c : Fin 78, c ≠ 73 → fZ brK (hselK (73 : Fin 78)) 73 c = 0 := by
  decide +kernel

theorem low_73 : ∀ c : Fin 78, fZ brK 73 77 c = 0 := by decide +kernel

theorem root_73 :
    6 ≤ (bselK (73 : Fin 78)).val ∧ (bselK (73 : Fin 78)).val < 42 ∧
      kselK (73 : Fin 78) ≠ 0 ∧ ∀ c : Fin 78,
      fZ brK (bselK (73 : Fin 78)) 77 c =
        if c = 73 then kselK (73 : Fin 78) else 0 := by
  decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
