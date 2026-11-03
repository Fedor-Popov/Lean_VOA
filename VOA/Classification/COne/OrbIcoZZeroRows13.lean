import VOA.Classification.COne.OrbIcoZZeroRows12

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def circle5 : ModeRel := [(-7, [mkRat (1) 1]), (-6, [mkRat (36) 1]), (-5, [mkRat (630) 1]), (-4, [mkRat (7140) 1]), (-3, [mkRat (58905) 1]), (-2, [mkRat (376992) 1]), (-1, [mkRat (1947792) 1]), (0, [mkRat (8347680) 1]), (1, [mkRat (30260340) 1]), (2, [mkRat (94143280) 1]), (3, [mkRat (254186856) 1]), (4, [mkRat (600805296) 1]), (5, [mkRat (1251677700) 1]), (6, [mkRat (2310789600) 1]), (7, [mkRat (3796297200) 1]), (8, [mkRat (5567902560) 1]), (9, [mkRat (7307872110) 1]), (10, [mkRat (8597496600) 1]), (11, [mkRat (9075135300) 1]), (12, [mkRat (8597496600) 1]), (13, [mkRat (7307872110) 1]), (14, [mkRat (5567902560) 1]), (15, [mkRat (3796297200) 1]), (16, [mkRat (2310789600) 1]), (17, [mkRat (1251677700) 1]), (18, [mkRat (600805296) 1]), (19, [mkRat (254186856) 1]), (20, [mkRat (94143280) 1]), (21, [mkRat (30260340) 1]), (22, [mkRat (8347680) 1]), (23, [mkRat (1947792) 1]), (24, [mkRat (376992) 1]), (25, [mkRat (58905) 1]), (26, [mkRat (7140) 1]), (27, [mkRat (630) 1]), (28, [mkRat (36) 1]), (29, [mkRat (1) 1])]

set_option maxHeartbeats 2000000 in
theorem circle5_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode circle5 = 0 := by
  have h := congrArg f (selfMode_circle 5)
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert h using 1
  norm_num [circle5, evalConst, mkRat]
  module

def circle7 : ModeRel := [(-9, [mkRat (1) 1]), (-8, [mkRat (36) 1]), (-7, [mkRat (630) 1]), (-6, [mkRat (7140) 1]), (-5, [mkRat (58905) 1]), (-4, [mkRat (376992) 1]), (-3, [mkRat (1947792) 1]), (-2, [mkRat (8347680) 1]), (-1, [mkRat (30260340) 1]), (0, [mkRat (94143280) 1]), (1, [mkRat (254186856) 1]), (2, [mkRat (600805296) 1]), (3, [mkRat (1251677700) 1]), (4, [mkRat (2310789600) 1]), (5, [mkRat (3796297200) 1]), (6, [mkRat (5567902560) 1]), (7, [mkRat (7307872110) 1]), (8, [mkRat (8597496600) 1]), (9, [mkRat (9075135300) 1]), (10, [mkRat (8597496600) 1]), (11, [mkRat (7307872110) 1]), (12, [mkRat (5567902560) 1]), (13, [mkRat (3796297200) 1]), (14, [mkRat (2310789600) 1]), (15, [mkRat (1251677700) 1]), (16, [mkRat (600805296) 1]), (17, [mkRat (254186856) 1]), (18, [mkRat (94143280) 1]), (19, [mkRat (30260340) 1]), (20, [mkRat (8347680) 1]), (21, [mkRat (1947792) 1]), (22, [mkRat (376992) 1]), (23, [mkRat (58905) 1]), (24, [mkRat (7140) 1]), (25, [mkRat (630) 1]), (26, [mkRat (36) 1]), (27, [mkRat (1) 1])]

set_option maxHeartbeats 2000000 in
theorem circle7_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode circle7 = 0 := by
  have h := congrArg f (selfMode_circle 7)
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert h using 1
  norm_num [circle7, evalConst, mkRat]
  module

def high72 : ModeRel := [(72, [mkRat (1) 1])]

theorem high72_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high72 = 0 := by
  simp [high72, evalConst, selfMode_high 72 (by omega)]

def high73 : ModeRel := [(73, [mkRat (1) 1])]

theorem high73_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high73 = 0 := by
  simp [high73, evalConst, selfMode_high 73 (by omega)]

def high74 : ModeRel := [(74, [mkRat (1) 1])]

theorem high74_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high74 = 0 := by
  simp [high74, evalConst, selfMode_high 74 (by omega)]

def high75 : ModeRel := [(75, [mkRat (1) 1])]

theorem high75_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode high75 = 0 := by
  simp [high75, evalConst, selfMode_high 75 (by omega)]

end VOA.Classification.COne.OrbIcoZ
