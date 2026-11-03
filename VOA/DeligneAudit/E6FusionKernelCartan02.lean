import VOA.DeligneAudit.E6FusionKernelData

/-! Small fixed-index E6 kernel checks, preserving the original integer facts. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000

theorem cartan_2 : ∀ c : Fin 78, fZ brK 2 77 c =
    if c = 77 then -(thetaH (2 : Fin 78) : ℤ) else 0 := by decide +kernel

end
end VOA.DeligneAudit.UnivG.E6K
