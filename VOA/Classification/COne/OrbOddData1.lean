import VOA.Classification.COne.OrbOddCert

/-! # OrbOdd data, level 1: `x_{14}`, its `L(1)`/`L(2)` caches and witnesses (machine-generated;
every value is kernel-checked). -/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbOdd

/-- `x_{14}` (level 1). -/
def xv1 : VVec := ofRaw
    [(1, 9, [1])]

def wa1 : VVec := ofRaw []
def wb1 : VVec := ofRaw []

def ca1_1_0 : Cache := ofRawC [
  (1, [1], [(18, 1, [])])]

set_option maxRecDepth 100000 in
theorem ca1_1_0_ok : cacheOK 9 1 64 1 ca1_1_0 = true := by decide +kernel

def ca1_1 : Cache := ca1_1_0

theorem ca1_1_ok : cacheOK 9 1 64 1 ca1_1 = true := ca1_1_0_ok

def ca2_1_0 : Cache := ofRawC [
  (1, [1], [])]

set_option maxRecDepth 100000 in
theorem ca2_1_0_ok : cacheOK 9 1 64 2 ca2_1_0 = true := by decide +kernel

def ca2_1 : Cache := ca2_1_0

theorem ca2_1_ok : cacheOK 9 1 64 2 ca2_1 = true := ca2_1_0_ok

set_option maxRecDepth 100000 in
/-- `L(1) x_{14} = 2 x_{15}` modulo `U(Vir⁻) s₇`. -/
theorem chkA1_ok : chkGen ca1_1 xv1 xvTop wa1 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `L(2) x_{14} = 10 x_{16}` modulo `U(Vir⁻) s₇`. -/
theorem chkB1_ok : chkGen ca2_1 xv1 [] wb1 10 = true := by decide +kernel

end VOA.Classification.COne.OrbOdd
