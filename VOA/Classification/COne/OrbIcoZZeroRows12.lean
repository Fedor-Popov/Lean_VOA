import VOA.Classification.COne.OrbIcoZZeroRows11

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def skew22 : ModeRel := [(22, [mkRat (2) 1]), (23, [mkRat (48) 1]), (24, [mkRat (1128) 1]), (25, [mkRat (17296) 1]), (26, [mkRat (194580) 1]), (27, [mkRat (1712304) 1]), (28, [mkRat (12271512) 1]), (29, [mkRat (73629072) 1]), (30, [mkRat (377348994) 1]), (31, [mkRat (1677106640) 1]), (32, [mkRat (6540715896) 1]), (33, [mkRat (22595200368) 1]), (34, [mkRat (69668534468) 1]), (35, [mkRat (192928249296) 1]), (36, [mkRat (482320623240) 1]), (37, [mkRat (1093260079344) 1]), (38, [mkRat (2254848913647) 1]), (39, [mkRat (4244421484512) 1]), (40, [mkRat (7309837001104) 1]), (41, [mkRat (11541847896480) 1]), (42, [mkRat (16735679449896) 1]), (43, [mkRat (22314239266528) 1]), (44, [mkRat (27385657281648) 1]), (45, [mkRat (30957699535776) 1]), (46, [mkRat (32247603683100) 1]), (47, [mkRat (30957699535776) 1]), (48, [mkRat (27385657281648) 1]), (49, [mkRat (22314239266528) 1]), (50, [mkRat (16735679449896) 1]), (51, [mkRat (11541847896480) 1]), (52, [mkRat (7309837001104) 1]), (53, [mkRat (4244421484512) 1]), (54, [mkRat (2254848913647) 1]), (55, [mkRat (1093260079344) 1]), (56, [mkRat (482320623240) 1]), (57, [mkRat (192928249296) 1]), (58, [mkRat (69668534468) 1]), (59, [mkRat (22595200368) 1]), (60, [mkRat (6540715896) 1]), (61, [mkRat (1677106640) 1]), (62, [mkRat (377348994) 1]), (63, [mkRat (73629072) 1]), (64, [mkRat (12271512) 1]), (65, [mkRat (1712304) 1]), (66, [mkRat (194580) 1]), (67, [mkRat (17296) 1]), (68, [mkRat (1128) 1]), (69, [mkRat (48) 1]), (70, [mkRat (1) 1])]

set_option maxHeartbeats 2000000 in
theorem skew22_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode skew22 = 0 := by
  have hs := selfMode_skew 22 (by omega)
  change selfMode 22 = sgn 23 •
    ∑ j ∈ Finset.range 49, cbz 48 (j : ℤ) • selfMode (22 + j) at hs
  have h := congrArg f hs
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [skew22, evalConst, mkRat]
  module

def skew46 : ModeRel := [(46, [mkRat (2) 1]), (47, [mkRat (24) 1]), (48, [mkRat (276) 1]), (49, [mkRat (2024) 1]), (50, [mkRat (10626) 1]), (51, [mkRat (42504) 1]), (52, [mkRat (134596) 1]), (53, [mkRat (346104) 1]), (54, [mkRat (735471) 1]), (55, [mkRat (1307504) 1]), (56, [mkRat (1961256) 1]), (57, [mkRat (2496144) 1]), (58, [mkRat (2704156) 1]), (59, [mkRat (2496144) 1]), (60, [mkRat (1961256) 1]), (61, [mkRat (1307504) 1]), (62, [mkRat (735471) 1]), (63, [mkRat (346104) 1]), (64, [mkRat (134596) 1]), (65, [mkRat (42504) 1]), (66, [mkRat (10626) 1]), (67, [mkRat (2024) 1]), (68, [mkRat (276) 1]), (69, [mkRat (24) 1]), (70, [mkRat (1) 1])]

set_option maxHeartbeats 2000000 in
theorem skew46_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode skew46 = 0 := by
  have hs := selfMode_skew 46 (by omega)
  change selfMode 46 = sgn 47 •
    ∑ j ∈ Finset.range 25, cbz 24 (j : ℤ) • selfMode (46 + j) at hs
  have h := congrArg f hs
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [skew46, evalConst, mkRat]
  module

def skew62 : ModeRel := [(62, [mkRat (2) 1]), (63, [mkRat (8) 1]), (64, [mkRat (28) 1]), (65, [mkRat (56) 1]), (66, [mkRat (70) 1]), (67, [mkRat (56) 1]), (68, [mkRat (28) 1]), (69, [mkRat (8) 1]), (70, [mkRat (1) 1])]

set_option maxHeartbeats 2000000 in
theorem skew62_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode skew62 = 0 := by
  have hs := selfMode_skew 62 (by omega)
  change selfMode 62 = sgn 63 •
    ∑ j ∈ Finset.range 9, cbz 8 (j : ℤ) • selfMode (62 + j) at hs
  have h := congrArg f hs
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [skew62, evalConst, mkRat]
  module

def skew70 : ModeRel := [(70, [mkRat (2) 1])]

set_option maxHeartbeats 2000000 in
theorem skew70_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode skew70 = 0 := by
  have hs := selfMode_skew 70 (by omega)
  change selfMode 70 = sgn 71 •
    ∑ j ∈ Finset.range 1, cbz 0 (j : ℤ) • selfMode (70 + j) at hs
  have h := congrArg f hs
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [skew70, evalConst, mkRat]
  module

def circle1 : ModeRel := [(-3, [mkRat (1) 1]), (-2, [mkRat (36) 1]), (-1, [mkRat (630) 1]), (0, [mkRat (7140) 1]), (1, [mkRat (58905) 1]), (2, [mkRat (376992) 1]), (3, [mkRat (1947792) 1]), (4, [mkRat (8347680) 1]), (5, [mkRat (30260340) 1]), (6, [mkRat (94143280) 1]), (7, [mkRat (254186856) 1]), (8, [mkRat (600805296) 1]), (9, [mkRat (1251677700) 1]), (10, [mkRat (2310789600) 1]), (11, [mkRat (3796297200) 1]), (12, [mkRat (5567902560) 1]), (13, [mkRat (7307872110) 1]), (14, [mkRat (8597496600) 1]), (15, [mkRat (9075135300) 1]), (16, [mkRat (8597496600) 1]), (17, [mkRat (7307872110) 1]), (18, [mkRat (5567902560) 1]), (19, [mkRat (3796297200) 1]), (20, [mkRat (2310789600) 1]), (21, [mkRat (1251677700) 1]), (22, [mkRat (600805296) 1]), (23, [mkRat (254186856) 1]), (24, [mkRat (94143280) 1]), (25, [mkRat (30260340) 1]), (26, [mkRat (8347680) 1]), (27, [mkRat (1947792) 1]), (28, [mkRat (376992) 1]), (29, [mkRat (58905) 1]), (30, [mkRat (7140) 1]), (31, [mkRat (630) 1]), (32, [mkRat (36) 1]), (33, [mkRat (1) 1])]

set_option maxHeartbeats 2000000 in
theorem circle1_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode circle1 = 0 := by
  have h := congrArg f (selfMode_circle 1)
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert h using 1
  norm_num [circle1, evalConst, mkRat]
  module

def circle3 : ModeRel := [(-5, [mkRat (1) 1]), (-4, [mkRat (36) 1]), (-3, [mkRat (630) 1]), (-2, [mkRat (7140) 1]), (-1, [mkRat (58905) 1]), (0, [mkRat (376992) 1]), (1, [mkRat (1947792) 1]), (2, [mkRat (8347680) 1]), (3, [mkRat (30260340) 1]), (4, [mkRat (94143280) 1]), (5, [mkRat (254186856) 1]), (6, [mkRat (600805296) 1]), (7, [mkRat (1251677700) 1]), (8, [mkRat (2310789600) 1]), (9, [mkRat (3796297200) 1]), (10, [mkRat (5567902560) 1]), (11, [mkRat (7307872110) 1]), (12, [mkRat (8597496600) 1]), (13, [mkRat (9075135300) 1]), (14, [mkRat (8597496600) 1]), (15, [mkRat (7307872110) 1]), (16, [mkRat (5567902560) 1]), (17, [mkRat (3796297200) 1]), (18, [mkRat (2310789600) 1]), (19, [mkRat (1251677700) 1]), (20, [mkRat (600805296) 1]), (21, [mkRat (254186856) 1]), (22, [mkRat (94143280) 1]), (23, [mkRat (30260340) 1]), (24, [mkRat (8347680) 1]), (25, [mkRat (1947792) 1]), (26, [mkRat (376992) 1]), (27, [mkRat (58905) 1]), (28, [mkRat (7140) 1]), (29, [mkRat (630) 1]), (30, [mkRat (36) 1]), (31, [mkRat (1) 1])]

set_option maxHeartbeats 2000000 in
theorem circle3_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode circle3 = 0 := by
  have h := congrArg f (selfMode_circle 3)
  simp only [map_sum, map_smul, map_zero] at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert h using 1
  norm_num [circle3, evalConst, mkRat]
  module

end VOA.Classification.COne.OrbIcoZ
