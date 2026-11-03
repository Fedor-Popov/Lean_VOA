import VOA.Classification.COne.OrbIcoZPolyRows
import VOA.Classification.COne.OrbIcoZSymbolCertificate

/-! Exact constant-pivot elimination in the genuine icosahedral Zhu algebra. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def modeExpression0 : ModeRel := []

set_option maxHeartbeats 8000000 in
theorem modeExpression0_check :
    equalRelCheck (substRel modeInterpInitial polySkew70)
      ([(70, [mkRat (2) 1])] ++ scaleRel [mkRat (-2) 1] modeExpression0) = true := by
  decide +kernel

def modeInterp0 (k : ℤ) : ModeRel :=
  if k = (70) then modeExpression0 else modeInterpInitial k

theorem modeInterp0_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp0 k) := by
  exact modeInterp_update modeInterpInitial modeInterpInitial_correct polySkew70 modeExpression0
    (70) (mkRat (2) 1) (by decide +kernel) polySkew70_holds modeExpression0_check k

def modeExpression1 : ModeRel := [(71, [mkRat (0) 1, mkRat (72) 1])]

set_option maxHeartbeats 8000000 in
theorem modeExpression1_check :
    equalRelCheck (substRel modeInterp0 (specialize (82) rawSymbolRows))
      ([(69, [mkRat (116861334187056256) 1])] ++ scaleRel [mkRat (-116861334187056256) 1] modeExpression1) = true := by
  decide +kernel

def modeInterp1 (k : ℤ) : ModeRel :=
  if k = (69) then modeExpression1 else modeInterp0 k

theorem modeInterp1_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp1 k) := by
  exact modeInterp_update modeInterp0 modeInterp0_correct (specialize (82) rawSymbolRows) modeExpression1
    (69) (mkRat (116861334187056256) 1) (by decide +kernel) (specializedNull_holds (82)) modeExpression1_check k

def modeExpression2 : ModeRel := [(71, [mkRat (0) 1, mkRat (-72) 1])]

set_option maxHeartbeats 8000000 in
theorem modeExpression2_check :
    equalRelCheck (substRel modeInterp1 (specialize (81) rawSymbolRows))
      ([(68, [mkRat (120015571460076864) 1])] ++ scaleRel [mkRat (-120015571460076864) 1] modeExpression2) = true := by
  decide +kernel

def modeInterp2 (k : ℤ) : ModeRel :=
  if k = (68) then modeExpression2 else modeInterp1 k

theorem modeInterp2_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp2 k) := by
  exact modeInterp_update modeInterp1 modeInterp1_correct (specialize (81) rawSymbolRows) modeExpression2
    (68) (mkRat (120015571460076864) 1) (by decide +kernel) (specializedNull_holds (81)) modeExpression2_check k

def modeExpression3 : ModeRel := [(67, [mkRat (-2) 1]),
 (71, [mkRat (0) 1, mkRat (72) 1])]

set_option maxHeartbeats 8000000 in
theorem modeExpression3_check :
    equalRelCheck (substRel modeInterp2 (specialize (79) rawSymbolRows))
      ([(66, [mkRat (-164887994889728000) 1])] ++ scaleRel [mkRat (164887994889728000) 1] modeExpression3) = true := by
  decide +kernel

def modeInterp3 (k : ℤ) : ModeRel :=
  if k = (66) then modeExpression3 else modeInterp2 k

theorem modeInterp3_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp3 k) := by
  exact modeInterp_update modeInterp2 modeInterp2_correct (specialize (79) rawSymbolRows) modeExpression3
    (66) (mkRat (-164887994889728000) 1) (by decide +kernel) (specializedNull_holds (79)) modeExpression3_check k

def modeExpression4 : ModeRel := [(67, [mkRat (71) 15, mkRat (44) 15]),
 (71, [mkRat (0) 1, mkRat (-1288) 5, mkRat (-9176) 5, mkRat (8064) 5])]

set_option maxHeartbeats 8000000 in
theorem modeExpression4_check :
    equalRelCheck (substRel modeInterp3 (specialize (78) rawSymbolRows))
      ([(65, [mkRat (-286292422674000000) 1])] ++ scaleRel [mkRat (286292422674000000) 1] modeExpression4) = true := by
  decide +kernel

def modeInterp4 (k : ℤ) : ModeRel :=
  if k = (65) then modeExpression4 else modeInterp3 k

theorem modeInterp4_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp4 k) := by
  exact modeInterp_update modeInterp3 modeInterp3_correct (specialize (78) rawSymbolRows) modeExpression4
    (65) (mkRat (-286292422674000000) 1) (by decide +kernel) (specializedNull_holds (78)) modeExpression4_check k

end VOA.Classification.COne.OrbIcoZ
