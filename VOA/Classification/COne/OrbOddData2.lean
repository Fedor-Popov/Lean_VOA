import VOA.Classification.COne.OrbOddData1

/-! # OrbOdd data, level 2: `x_{13}`, its `L(1)`/`L(2)` caches and witnesses (machine-generated;
every value is kernel-checked). -/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbOdd

/-- `x_{13}` (level 2). -/
def xv2 : VVec := ofRaw
    [(16, 49, [2]),
    (-5, 294, [1, 1])]

def wa2 : VVec := ofRaw []
def wb2 : VVec := ofRaw []

def ca1_2_0 : Cache := ofRawC [
  (2, [2], [(3, 1, [1])]),
  (65, [1, 1], [(38, 1, [1])])]

set_option maxRecDepth 100000 in
theorem ca1_2_0_ok : cacheOK 9 1 64 1 ca1_2_0 = true := by decide +kernel

def ca1_2 : Cache := ca1_2_0

theorem ca1_2_ok : cacheOK 9 1 64 1 ca1_2 = true := ca1_2_0_ok

def ca2_2_0 : Cache := ofRawC [
  (2, [2], [(73, 2, [])]),
  (65, [1, 1], [(54, 1, [])])]

set_option maxRecDepth 100000 in
theorem ca2_2_0_ok : cacheOK 9 1 64 2 ca2_2_0 = true := by decide +kernel

def ca2_2 : Cache := ca2_2_0

theorem ca2_2_ok : cacheOK 9 1 64 2 ca2_2 = true := ca2_2_0_ok

set_option maxRecDepth 100000 in
/-- `L(1) x_{13} = 3 x_{14}` modulo `U(Vir⁻) s₇`. -/
theorem chkA2_ok : chkGen ca1_2 xv2 xv1 wa2 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `L(2) x_{13} = 11 x_{15}` modulo `U(Vir⁻) s₇`. -/
theorem chkB2_ok : chkGen ca2_2 xv2 xvTop wb2 11 = true := by decide +kernel

end VOA.Classification.COne.OrbOdd
