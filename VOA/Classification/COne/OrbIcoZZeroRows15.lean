import VOA.Classification.COne.OrbIcoZZeroRows14

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def high82 : ModeRel := [(82, [mkRat (1) 1])]

theorem high82_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high82 = 0 := by
  simp [high82, evalConst, selfMode_high 82 (by omega)]

end VOA.Classification.COne.OrbIcoZ
