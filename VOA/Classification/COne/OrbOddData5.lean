import VOA.Classification.COne.OrbOddData4

/-! # OrbOdd data, level 5: `x_{10}`, its `L(1)`/`L(2)` caches and witnesses (machine-generated;
every value is kernel-checked). -/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbOdd

/-- `x_{10}` (level 5). -/
def xv5 : VVec := ofRaw
    [(-32143, 264600, [5]),
    (37738, 297675, [4, 1]),
    (5951, 33075, [3, 2]),
    (-117377, 4762800, [3, 1, 1]),
    (-878, 33075, [2, 2, 1]),
    (1541, 476280, [2, 1, 1, 1]),
    (-661, 9525600, [1, 1, 1, 1, 1])]

def wa5 : VVec := ofRaw []
def wb5 : VVec := ofRaw []

def ca1_5_0 : Cache := ofRawC [
  (5, [5], [(6, 1, [4])]),
  (68, [4, 1], [(18, 1, [4]),
    (5, 1, [3, 1])]),
  (131, [3, 2], [(3, 1, [3, 1]),
    (4, 1, [2, 2])]),
  (4163, [3, 1, 1], [(38, 1, [3, 1]),
    (4, 1, [2, 1, 1])]),
  (4226, [2, 2, 1], [(3, 1, [3, 1]),
    (18, 1, [2, 2]),
    (6, 1, [2, 1, 1])]),
  (266306, [2, 1, 1, 1], [(60, 1, [2, 1, 1]),
    (3, 1, [1, 1, 1, 1])]),
  (17043521, [1, 1, 1, 1, 1], [(110, 1, [1, 1, 1, 1])])]

set_option maxRecDepth 100000 in
theorem ca1_5_0_ok : cacheOK 9 1 64 1 ca1_5_0 = true := by decide +kernel

def ca1_5 : Cache := ca1_5_0

theorem ca1_5_ok : cacheOK 9 1 64 1 ca1_5 = true := ca1_5_0_ok

def ca2_5_0 : Cache := ofRawC [
  (5, [5], [(7, 1, [3])]),
  (68, [4, 1], [(6, 1, [2, 1])]),
  (131, [3, 2], [(83, 2, [3]),
    (5, 1, [2, 1])]),
  (4163, [3, 1, 1], [(54, 1, [3]),
    (5, 1, [1, 1, 1])]),
  (4226, [2, 2, 1], [(89, 1, [2, 1])]),
  (266306, [2, 1, 1, 1], [(168, 1, [2, 1]),
    (97, 2, [1, 1, 1])]),
  (17043521, [1, 1, 1, 1, 1], [(600, 1, [1, 1, 1])])]

set_option maxRecDepth 100000 in
theorem ca2_5_0_ok : cacheOK 9 1 64 2 ca2_5_0 = true := by decide +kernel

def ca2_5 : Cache := ca2_5_0

theorem ca2_5_ok : cacheOK 9 1 64 2 ca2_5 = true := ca2_5_0_ok

set_option maxRecDepth 100000 in
/-- `L(1) x_{10} = 6 x_{11}` modulo `U(Vir⁻) s₇`. -/
theorem chkA5_ok : chkGen ca1_5 xv5 xv4 wa5 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `L(2) x_{10} = 14 x_{12}` modulo `U(Vir⁻) s₇`. -/
theorem chkB5_ok : chkGen ca2_5 xv5 xv3 wb5 14 = true := by decide +kernel

end VOA.Classification.COne.OrbOdd
