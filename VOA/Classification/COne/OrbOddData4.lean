import VOA.Classification.COne.OrbOddData3

/-! # OrbOdd data, level 4: `x_{11}`, its `L(1)`/`L(2)` caches and witnesses (machine-generated;
every value is kernel-checked). -/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbOdd

/-- `x_{11}` (level 4). -/
def xv4 : VVec := ofRaw
    [(8219, 31752, [4]),
    (15005, 571536, [3, 1]),
    (160, 3969, [2, 2]),
    (-3035, 285768, [2, 1, 1]),
    (395, 1143072, [1, 1, 1, 1])]

def wa4 : VVec := ofRaw []
def wb4 : VVec := ofRaw []

def ca1_4_0 : Cache := ofRawC [
  (4, [4], [(5, 1, [3])]),
  (67, [3, 1], [(18, 1, [3]),
    (4, 1, [2, 1])]),
  (130, [2, 2], [(3, 1, [3]),
    (6, 1, [2, 1])]),
  (4162, [2, 1, 1], [(38, 1, [2, 1]),
    (3, 1, [1, 1, 1])]),
  (266305, [1, 1, 1, 1], [(84, 1, [1, 1, 1])])]

set_option maxRecDepth 100000 in
theorem ca1_4_0_ok : cacheOK 9 1 64 1 ca1_4_0 = true := by decide +kernel

def ca1_4 : Cache := ca1_4_0

theorem ca1_4_ok : cacheOK 9 1 64 1 ca1_4 = true := ca1_4_0_ok

def ca2_4_0 : Cache := ofRawC [
  (4, [4], [(6, 1, [2])]),
  (67, [3, 1], [(5, 1, [1, 1])]),
  (130, [2, 2], [(81, 1, [2])]),
  (4162, [2, 1, 1], [(54, 1, [2]),
    (89, 2, [1, 1])]),
  (266305, [1, 1, 1, 1], [(348, 1, [1, 1])])]

set_option maxRecDepth 100000 in
theorem ca2_4_0_ok : cacheOK 9 1 64 2 ca2_4_0 = true := by decide +kernel

def ca2_4 : Cache := ca2_4_0

theorem ca2_4_ok : cacheOK 9 1 64 2 ca2_4 = true := ca2_4_0_ok

set_option maxRecDepth 100000 in
/-- `L(1) x_{11} = 5 x_{12}` modulo `U(Vir⁻) s₇`. -/
theorem chkA4_ok : chkGen ca1_4 xv4 xv3 wa4 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `L(2) x_{11} = 13 x_{13}` modulo `U(Vir⁻) s₇`. -/
theorem chkB4_ok : chkGen ca2_4 xv4 xv2 wb4 13 = true := by decide +kernel

end VOA.Classification.COne.OrbOdd
