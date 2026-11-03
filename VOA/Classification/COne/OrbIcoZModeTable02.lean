import VOA.Classification.COne.OrbIcoZModeTable01

/-! Exact constant-pivot elimination in the genuine icosahedral Zhu algebra. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def modeExpression10 : ModeRel := [(67, [mkRat (16206667) 101640, mkRat (-473274181) 4573800, mkRat (387125909) 1143450, mkRat (211508032) 571725, mkRat (1483792) 63525]),
 (71, [mkRat (0) 1, mkRat (-6921797) 660, mkRat (-96339669661) 762300, mkRat (28626853097) 190575, mkRat (745759856) 190575, mkRat (-1531882848) 21175, mkRat (-33182208) 21175])]

set_option maxHeartbeats 8000000 in
theorem modeExpression10_check :
    equalRelCheck (substRel modeInterp9 (specialize (72) rawSymbolRows))
      ([(59, [mkRat (664564316024733696) 1])] ++ scaleRel [mkRat (-664564316024733696) 1] modeExpression10) = true := by
  decide +kernel

def modeInterp10 (k : ℤ) : ModeRel :=
  if k = (59) then modeExpression10 else modeInterp9 k

theorem modeInterp10_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp10 k) := by
  exact modeInterp_update modeInterp9 modeInterp9_correct (specialize (72) rawSymbolRows) modeExpression10
    (59) (mkRat (664564316024733696) 1) (by decide +kernel) (specializedNull_holds (72)) modeExpression10_check k

def modeExpression11 : ModeRel := [(67, [mkRat (-2194359) 8470, mkRat (91634623) 381150, mkRat (-79258954) 190575, mkRat (-167677024) 190575, mkRat (-2967584) 21175]),
 (71, [mkRat (0) 1, mkRat (938549) 55, mkRat (12912346933) 63525, mkRat (-17728902524) 63525, mkRat (-3867940352) 63525, mkRat (4550472768) 21175, mkRat (199093248) 21175])]

set_option maxHeartbeats 8000000 in
theorem modeExpression11_check :
    equalRelCheck (substRel modeInterp10 (specialize (71) rawSymbolRows))
      ([(58, [mkRat (714584068118728704) 1])] ++ scaleRel [mkRat (-714584068118728704) 1] modeExpression11) = true := by
  decide +kernel

def modeInterp11 (k : ℤ) : ModeRel :=
  if k = (58) then modeExpression11 else modeInterp10 k

theorem modeInterp11_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp11 k) := by
  exact modeInterp_update modeInterp10 modeInterp10_correct (specialize (71) rawSymbolRows) modeExpression11
    (58) (mkRat (714584068118728704) 1) (by decide +kernel) (specializedNull_holds (71)) modeExpression11_check k

def modeExpression12 : ModeRel := [(67, [mkRat (8253093843) 20040020, mkRat (-420927195859) 901800900, mkRat (76245376037) 225450225, mkRat (81854659036) 45090045, mkRat (36008589616) 75150075, mkRat (493324224) 25050025]),
 (71, [mkRat (0) 1, mkRat (-3532783673) 130130, mkRat (-48123632275009) 150300150, mkRat (37216529584198) 75150075, mkRat (19089398143672) 75150075, mkRat (-13849356623008) 25050025, mkRat (-168861439872) 5010005, mkRat (-57307834368) 25050025])]

set_option maxHeartbeats 8000000 in
theorem modeExpression12_check :
    equalRelCheck (substRel modeInterp11 (specialize (70) rawSymbolRows))
      ([(57, [mkRat (617767684534000000) 1])] ++ scaleRel [mkRat (-617767684534000000) 1] modeExpression12) = true := by
  decide +kernel

def modeInterp12 (k : ℤ) : ModeRel :=
  if k = (57) then modeExpression12 else modeInterp11 k

theorem modeInterp12_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp12 k) := by
  exact modeInterp_update modeInterp11 modeInterp11_correct (specialize (70) rawSymbolRows) modeExpression12
    (57) (mkRat (617767684534000000) 1) (by decide +kernel) (specializedNull_holds (70)) modeExpression12_check k

def modeExpression13 : ModeRel := [(67, [mkRat (-13777195283) 21471450, mkRat (156641196707) 193243050, mkRat (11831037208) 96621525, mkRat (-331153319108) 96621525, mkRat (-4396450816) 3578575, mkRat (-493324224) 3578575]),
 (71, [mkRat (0) 1, mkRat (5900160113) 139425, mkRat (15973365265001) 32207175, mkRat (-26983801031248) 32207175, mkRat (-24519020850568) 32207175, mkRat (4564777747072) 3578575, mkRat (333998022528) 3578575, mkRat (57307834368) 3578575])]

set_option maxHeartbeats 8000000 in
theorem modeExpression13_check :
    equalRelCheck (substRel modeInterp12 (specialize (69) rawSymbolRows))
      ([(56, [mkRat (371976889843944000) 1])] ++ scaleRel [mkRat (-371976889843944000) 1] modeExpression13) = true := by
  decide +kernel

def modeInterp13 (k : ℤ) : ModeRel :=
  if k = (56) then modeExpression13 else modeInterp12 k

theorem modeInterp13_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp13 k) := by
  exact modeInterp_update modeInterp12 modeInterp12_correct (specialize (69) rawSymbolRows) modeExpression13
    (56) (mkRat (371976889843944000) 1) (by decide +kernel) (specializedNull_holds (69)) modeExpression13_check k

def modeExpression14 : ModeRel := [(55, [mkRat (-8) 1]),
 (67, [mkRat (1825273113) 286286, mkRat (-181059129029) 21471450, mkRat (-74010337958) 10735725, mkRat (412175106832) 10735725, mkRat (172510100288) 10735725, mkRat (1973296896) 715715]),
 (71, [mkRat (0) 1, mkRat (-781869003) 1859, mkRat (-17595983587229) 3578575, mkRat (31259334252452) 3578575, mkRat (39427407052256) 3578575, mkRat (-58235595850112) 3578575, mkRat (-4638723743232) 3578575, mkRat (-229231337472) 715715])]

set_option maxHeartbeats 8000000 in
theorem modeExpression14_check :
    equalRelCheck (substRel modeInterp13 (specialize (67) rawSymbolRows))
      ([(54, [mkRat (-453720909685981184) 1])] ++ scaleRel [mkRat (453720909685981184) 1] modeExpression14) = true := by
  decide +kernel

def modeInterp14 (k : ℤ) : ModeRel :=
  if k = (54) then modeExpression14 else modeInterp13 k

theorem modeInterp14_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp14 k) := by
  exact modeInterp_update modeInterp13 modeInterp13_correct (specialize (67) rawSymbolRows) modeExpression14
    (54) (mkRat (-453720909685981184) 1) (by decide +kernel) (specializedNull_holds (67)) modeExpression14_check k

end VOA.Classification.COne.OrbIcoZ
