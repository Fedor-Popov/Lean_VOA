import VOA.Classification.COne.OrbIcoZZeroRows13

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def high76 : ModeRel := [(76, [mkRat (1) 1])]

theorem high76_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high76 = 0 := by
  simp [high76, evalConst, selfMode_high 76 (by omega)]

def high77 : ModeRel := [(77, [mkRat (1) 1])]

theorem high77_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high77 = 0 := by
  simp [high77, evalConst, selfMode_high 77 (by omega)]

def high78 : ModeRel := [(78, [mkRat (1) 1])]

theorem high78_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high78 = 0 := by
  simp [high78, evalConst, selfMode_high 78 (by omega)]

def high79 : ModeRel := [(79, [mkRat (1) 1])]

theorem high79_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high79 = 0 := by
  simp [high79, evalConst, selfMode_high 79 (by omega)]

def high80 : ModeRel := [(80, [mkRat (1) 1])]

theorem high80_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high80 = 0 := by
  simp [high80, evalConst, selfMode_high 80 (by omega)]

def high81 : ModeRel := [(81, [mkRat (1) 1])]

theorem high81_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high81 = 0 := by
  simp [high81, evalConst, selfMode_high 81 (by omega)]

end VOA.Classification.COne.OrbIcoZ
