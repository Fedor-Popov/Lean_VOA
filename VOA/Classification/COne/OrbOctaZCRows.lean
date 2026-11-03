import VOA.Classification.COne.OrbOctaZCCache07
import VOA.Classification.COne.OrbOctaZCElimination

/-! The remaining rows of the finite P25 mode certificate. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu Polynomial

def circle1 : ModeRel := [
  (-3, [mkRat (1) 1]),
  (-2, [mkRat (16) 1]),
  (-1, [mkRat (120) 1]),
  (0, [mkRat (560) 1]),
  (1, [mkRat (1820) 1]),
  (2, [mkRat (4368) 1]),
  (3, [mkRat (8008) 1]),
  (4, [mkRat (11440) 1]),
  (5, [mkRat (12870) 1]),
  (6, [mkRat (11440) 1]),
  (7, [mkRat (8008) 1]),
  (8, [mkRat (4368) 1]),
  (9, [mkRat (1820) 1]),
  (10, [mkRat (560) 1]),
  (11, [mkRat (120) 1]),
  (12, [mkRat (16) 1]),
  (13, [mkRat (1) 1])]

theorem circle1_holds : evalRel OrbOctaR.W selfMode circle1 = 0 := by
  have h := selfMode_circle 1
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1 ; norm_num [circle1, evalRel, zp, mkRat] ; module

def skew6 : ModeRel := [
  (6, [mkRat (2) 1]),
  (7, [mkRat (24) 1]),
  (8, [mkRat (276) 1]),
  (9, [mkRat (2024) 1]),
  (10, [mkRat (10626) 1]),
  (11, [mkRat (42504) 1]),
  (12, [mkRat (134596) 1]),
  (13, [mkRat (346104) 1]),
  (14, [mkRat (735471) 1]),
  (15, [mkRat (1307504) 1]),
  (16, [mkRat (1961256) 1]),
  (17, [mkRat (2496144) 1]),
  (18, [mkRat (2704156) 1]),
  (19, [mkRat (2496144) 1]),
  (20, [mkRat (1961256) 1]),
  (21, [mkRat (1307504) 1]),
  (22, [mkRat (735471) 1]),
  (23, [mkRat (346104) 1]),
  (24, [mkRat (134596) 1]),
  (25, [mkRat (42504) 1]),
  (26, [mkRat (10626) 1]),
  (27, [mkRat (2024) 1]),
  (28, [mkRat (276) 1]),
  (29, [mkRat (24) 1]),
  (30, [mkRat (1) 1])]

theorem skew6_holds : evalRel OrbOctaR.W selfMode skew6 = 0 := by
  have h := selfMode_skew 6 (by decide)
  change selfMode 6 = sgn 7 •
    ∑ j ∈ Finset.range 25, cbz 24 (j : ℤ) • selfMode (6 + j) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1 ;
    norm_num [skew6, evalRel, zp, mkRat] ; module

def skew30 : ModeRel := [
  (30, [mkRat (2) 1])]

theorem skew30_holds : evalRel OrbOctaR.W selfMode skew30 = 0 := by
  have h := selfMode_skew 30 (by decide)
  change selfMode 30 = sgn 31 •
    ∑ j ∈ Finset.range 1, cbz 0 (j : ℤ) • selfMode (30 + j) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1 ;
    norm_num [skew30, evalRel, zp, mkRat] ; module

def high38 : ModeRel := [
  (38, [mkRat (1) 1])]

theorem high38_holds : evalRel OrbOctaR.W selfMode high38 = 0 := by
  norm_num [high38, evalRel, zp, mkRat, selfMode_high 38 (by decide)]

def high37 : ModeRel := [
  (37, [mkRat (1) 1])]

theorem high37_holds : evalRel OrbOctaR.W selfMode high37 = 0 := by
  norm_num [high37, evalRel, zp, mkRat, selfMode_high 37 (by decide)]

def high36 : ModeRel := [
  (36, [mkRat (1) 1])]

theorem high36_holds : evalRel OrbOctaR.W selfMode high36 = 0 := by
  norm_num [high36, evalRel, zp, mkRat, selfMode_high 36 (by decide)]

def high35 : ModeRel := [
  (35, [mkRat (1) 1])]

theorem high35_holds : evalRel OrbOctaR.W selfMode high35 = 0 := by
  norm_num [high35, evalRel, zp, mkRat, selfMode_high 35 (by decide)]

def high34 : ModeRel := [
  (34, [mkRat (1) 1])]

theorem high34_holds : evalRel OrbOctaR.W selfMode high34 = 0 := by
  norm_num [high34, evalRel, zp, mkRat, selfMode_high 34 (by decide)]

def high33 : ModeRel := [
  (33, [mkRat (1) 1])]

theorem high33_holds : evalRel OrbOctaR.W selfMode high33 = 0 := by
  norm_num [high33, evalRel, zp, mkRat, selfMode_high 33 (by decide)]

def high32 : ModeRel := [
  (32, [mkRat (1) 1])]

theorem high32_holds : evalRel OrbOctaR.W selfMode high32 = 0 := by
  norm_num [high32, evalRel, zp, mkRat, selfMode_high 32 (by decide)]

def low4 : ModeRel := [
  (27, [mkRat (1) 1]),
  (31, [mkRat (0) 1, mkRat (-48) 1, mkRat (-96) 1])]

theorem low4_holds : evalRel OrbOctaR.W selfMode low4 = 0 := by
  have h := low_mode27
  convert sub_eq_zero.mpr h using 1 ;
    norm_num [low4, evalRel, zp, mkRat, map_add, map_mul, aeval_C, aeval_X,
      LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply] ; module

def skew22 : ModeRel := [
  (22, [mkRat (2) 1]),
  (23, [mkRat (8) 1]),
  (24, [mkRat (28) 1]),
  (25, [mkRat (56) 1]),
  (26, [mkRat (70) 1]),
  (27, [mkRat (56) 1]),
  (28, [mkRat (28) 1]),
  (29, [mkRat (8) 1]),
  (30, [mkRat (1) 1])]

theorem skew22_holds : evalRel OrbOctaR.W selfMode skew22 = 0 := by
  have h := selfMode_skew 22 (by decide)
  change selfMode 22 = sgn 23 •
    ∑ j ∈ Finset.range 9, cbz 8 (j : ℤ) • selfMode (22 + j) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1 ;
    norm_num [skew22, evalRel, zp, mkRat] ; module

def circle5 : ModeRel := [
  (-7, [mkRat (1) 1]),
  (-6, [mkRat (16) 1]),
  (-5, [mkRat (120) 1]),
  (-4, [mkRat (560) 1]),
  (-3, [mkRat (1820) 1]),
  (-2, [mkRat (4368) 1]),
  (-1, [mkRat (8008) 1]),
  (0, [mkRat (11440) 1]),
  (1, [mkRat (12870) 1]),
  (2, [mkRat (11440) 1]),
  (3, [mkRat (8008) 1]),
  (4, [mkRat (4368) 1]),
  (5, [mkRat (1820) 1]),
  (6, [mkRat (560) 1]),
  (7, [mkRat (120) 1]),
  (8, [mkRat (16) 1]),
  (9, [mkRat (1) 1])]

theorem circle5_holds : evalRel OrbOctaR.W selfMode circle5 = 0 := by
  have h := selfMode_circle 5
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1 ; norm_num [circle5, evalRel, zp, mkRat] ; module

def circle3 : ModeRel := [
  (-5, [mkRat (1) 1]),
  (-4, [mkRat (16) 1]),
  (-3, [mkRat (120) 1]),
  (-2, [mkRat (560) 1]),
  (-1, [mkRat (1820) 1]),
  (0, [mkRat (4368) 1]),
  (1, [mkRat (8008) 1]),
  (2, [mkRat (11440) 1]),
  (3, [mkRat (12870) 1]),
  (4, [mkRat (11440) 1]),
  (5, [mkRat (8008) 1]),
  (6, [mkRat (4368) 1]),
  (7, [mkRat (1820) 1]),
  (8, [mkRat (560) 1]),
  (9, [mkRat (120) 1]),
  (10, [mkRat (16) 1]),
  (11, [mkRat (1) 1])]

theorem circle3_holds : evalRel OrbOctaR.W selfMode circle3 = 0 := by
  have h := selfMode_circle 3
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1 ; norm_num [circle3, evalRel, zp, mkRat] ; module

end VOA.Classification.COne.OrbOctaZC
