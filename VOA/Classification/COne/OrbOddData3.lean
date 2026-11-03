import VOA.Classification.COne.OrbOddData2

/-! # OrbOdd data, level 3: `x_{12}`, its `L(1)`/`L(2)` caches and witnesses (machine-generated;
every value is kernel-checked). -/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbOdd

/-- `x_{12}` (level 3). -/
def xv3 : VVec := ofRaw
    [(37, 98, [3]),
    (-5, 441, [2, 1]),
    (-1, 1764, [1, 1, 1])]

def wa3 : VVec := ofRaw []
def wb3 : VVec := ofRaw []

def ca1_3_0 : Cache := ofRawC [
  (3, [3], [(4, 1, [2])]),
  (66, [2, 1], [(18, 1, [2]),
    (3, 1, [1, 1])]),
  (4161, [1, 1, 1], [(60, 1, [1, 1])])]

set_option maxRecDepth 100000 in
theorem ca1_3_0_ok : cacheOK 9 1 64 1 ca1_3_0 = true := by decide +kernel

def ca1_3 : Cache := ca1_3_0

theorem ca1_3_ok : cacheOK 9 1 64 1 ca1_3 = true := ca1_3_0_ok

def ca2_3_0 : Cache := ofRawC [
  (3, [3], [(5, 1, [1])]),
  (66, [2, 1], [(81, 2, [1])]),
  (4161, [1, 1, 1], [(168, 1, [1])])]

set_option maxRecDepth 100000 in
theorem ca2_3_0_ok : cacheOK 9 1 64 2 ca2_3_0 = true := by decide +kernel

def ca2_3 : Cache := ca2_3_0

theorem ca2_3_ok : cacheOK 9 1 64 2 ca2_3 = true := ca2_3_0_ok

set_option maxRecDepth 100000 in
/-- `L(1) x_{12} = 4 x_{13}` modulo `U(Vir⁻) s₇`. -/
theorem chkA3_ok : chkGen ca1_3 xv3 xv2 wa3 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `L(2) x_{12} = 12 x_{14}` modulo `U(Vir⁻) s₇`. -/
theorem chkB3_ok : chkGen ca2_3 xv3 xv1 wb3 12 = true := by decide +kernel

end VOA.Classification.COne.OrbOdd
