import VOA.Classification.COne.OrbIcoZModeTable00

/-! Exact constant-pivot elimination in the genuine icosahedral Zhu algebra. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def modeExpression5 : ModeRel := [(67, [mkRat (-46) 5, mkRat (-44) 5]),
 (71, [mkRat (0) 1, mkRat (2784) 5, mkRat (27528) 5, mkRat (-24192) 5])]

set_option maxHeartbeats 8000000 in
theorem modeExpression5_check :
    equalRelCheck (substRel modeInterp4 (specialize (77) rawSymbolRows))
      ([(64, [mkRat (-304633588283365824) 1])] ++ scaleRel [mkRat (304633588283365824) 1] modeExpression5) = true := by
  decide +kernel

def modeInterp5 (k : ℤ) : ModeRel :=
  if k = (64) then modeExpression5 else modeInterp4 k

theorem modeInterp5_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp5 k) := by
  exact modeInterp_update modeInterp4 modeInterp4_correct (specialize (77) rawSymbolRows) modeExpression5
    (64) (mkRat (-304633588283365824) 1) (by decide +kernel) (specializedNull_holds (77)) modeExpression5_check k

def modeExpression6 : ModeRel := [(67, [mkRat (4909) 280, mkRat (3949) 280, mkRat (883) 70]),
 (71, [mkRat (0) 1, mkRat (-22209) 20, mkRat (-1763637) 140, mkRat (378993) 35, mkRat (-8208) 35])]

set_option maxHeartbeats 8000000 in
theorem modeExpression6_check :
    equalRelCheck (substRel modeInterp5 (specialize (76) rawSymbolRows))
      ([(63, [mkRat (-202136564921532416) 1])] ++ scaleRel [mkRat (202136564921532416) 1] modeExpression6) = true := by
  decide +kernel

def modeInterp6 (k : ℤ) : ModeRel :=
  if k = (63) then modeExpression6 else modeInterp5 k

theorem modeInterp6_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp6 k) := by
  exact modeInterp_update modeInterp5 modeInterp5_correct (specialize (76) rawSymbolRows) modeExpression6
    (63) (mkRat (-202136564921532416) 1) (by decide +kernel) (specializedNull_holds (76)) modeExpression6_check k

def modeExpression7 : ModeRel := [(67, [mkRat (-6691) 210, mkRat (-3223) 210, mkRat (-1766) 35]),
 (71, [mkRat (0) 1, mkRat (10297) 5, mkRat (864389) 35, mkRat (-145140) 7, mkRat (32832) 35])]

set_option maxHeartbeats 8000000 in
theorem modeExpression7_check :
    equalRelCheck (substRel modeInterp6 polySkew62)
      ([(62, [mkRat (2) 1])] ++ scaleRel [mkRat (-2) 1] modeExpression7) = true := by
  decide +kernel

def modeInterp7 (k : ℤ) : ModeRel :=
  if k = (62) then modeExpression7 else modeInterp6 k

theorem modeInterp7_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp7 k) := by
  exact modeInterp_update modeInterp6 modeInterp6_correct polySkew62 modeExpression7
    (62) (mkRat (2) 1) (by decide +kernel) polySkew62_holds modeExpression7_check k

def modeExpression8 : ModeRel := [(67, [mkRat (39253) 700, mkRat (30673) 6300, mkRat (189307) 1575, mkRat (38368) 1575]),
 (71, [mkRat (0) 1, mkRat (-183013) 50, mkRat (-46867211) 1050, mkRat (20960726) 525, mkRat (-1243552) 525, mkRat (-697344) 175])]

set_option maxHeartbeats 8000000 in
theorem modeExpression8_check :
    equalRelCheck (substRel modeInterp7 (specialize (74) rawSymbolRows))
      ([(61, [mkRat (252927830812176000) 1])] ++ scaleRel [mkRat (-252927830812176000) 1] modeExpression8) = true := by
  decide +kernel

def modeInterp8 (k : ℤ) : ModeRel :=
  if k = (61) then modeExpression8 else modeInterp7 k

theorem modeInterp8_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp8 k) := by
  exact modeInterp_update modeInterp7 modeInterp7_correct (specialize (74) rawSymbolRows) modeExpression8
    (61) (mkRat (252927830812176000) 1) (by decide +kernel) (specializedNull_holds (74)) modeExpression8_check k

def modeExpression9 : ModeRel := [(67, [mkRat (-6707) 70, mkRat (18373) 630, mkRat (-70102) 315, mkRat (-38368) 315]),
 (71, [mkRat (0) 1, mkRat (31427) 5, mkRat (8031469) 105, mkRat (-1637740) 21, mkRat (504832) 105, mkRat (697344) 35])]

set_option maxHeartbeats 8000000 in
theorem modeExpression9_check :
    equalRelCheck (substRel modeInterp8 (specialize (73) rawSymbolRows))
      ([(60, [mkRat (494709908077000000) 1])] ++ scaleRel [mkRat (-494709908077000000) 1] modeExpression9) = true := by
  decide +kernel

def modeInterp9 (k : ℤ) : ModeRel :=
  if k = (60) then modeExpression9 else modeInterp8 k

theorem modeInterp9_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterp9 k) := by
  exact modeInterp_update modeInterp8 modeInterp8_correct (specialize (73) rawSymbolRows) modeExpression9
    (60) (mkRat (494709908077000000) 1) (by decide +kernel) (specializedNull_holds (73)) modeExpression9_check k

end VOA.Classification.COne.OrbIcoZ
