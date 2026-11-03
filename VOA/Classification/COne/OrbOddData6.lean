import VOA.Classification.COne.OrbOddData5

/-! # OrbOdd data, level 6: `x_{9}`, its `L(1)`/`L(2)` caches and witnesses (machine-generated;
every value is kernel-checked). -/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbOdd

/-- `x_{9}` (level 6). -/
def xv6 : VVec := ofRaw
    [(-24119213, 19448100, [6]),
    (3047110849, 7701447600, [5, 1]),
    (15306019, 35654850, [4, 2]),
    (6350261, 30561300, [3, 3]),
    (-62475037, 855716400, [4, 1, 1]),
    (-10124255, 77014476, [3, 2, 1]),
    (-217472, 10696455, [2, 2, 2]),
    (4244521, 466754400, [3, 1, 1, 1]),
    (13249463, 962680950, [2, 2, 1, 1]),
    (-1765921, 1540289520, [2, 1, 1, 1, 1]),
    (659359, 30805790400, [1, 1, 1, 1, 1, 1])]

def wa6 : VVec := ofRaw []
def wb6 : VVec := ofRaw []

def ca1_6_0 : Cache := ofRawC [
  (6, [6], [(7, 1, [5])]),
  (69, [5, 1], [(18, 1, [5]),
    (6, 1, [4, 1])]),
  (132, [4, 2], [(3, 1, [4, 1]),
    (5, 1, [3, 2])]),
  (195, [3, 3], [(4, 1, [5]),
    (8, 1, [3, 2])]),
  (4164, [4, 1, 1], [(38, 1, [4, 1]),
    (5, 1, [3, 1, 1])]),
  (4227, [3, 2, 1], [(18, 1, [3, 2]),
    (3, 1, [3, 1, 1]),
    (4, 1, [2, 2, 1])]),
  (8322, [2, 2, 2], [(6, 1, [5]),
    (9, 1, [3, 2]),
    (9, 1, [2, 2, 1])]),
  (266307, [3, 1, 1, 1], [(60, 1, [3, 1, 1]),
    (4, 1, [2, 1, 1, 1])]),
  (266370, [2, 2, 1, 1], [(3, 1, [3, 1, 1]),
    (38, 1, [2, 2, 1]),
    (6, 1, [2, 1, 1, 1])]),
  (17043522, [2, 1, 1, 1, 1], [(84, 1, [2, 1, 1, 1]),
    (3, 1, [1, 1, 1, 1, 1])]),
  (1090785345, [1, 1, 1, 1, 1, 1], [(138, 1, [1, 1, 1, 1, 1])])]

set_option maxRecDepth 100000 in
theorem ca1_6_0_ok : cacheOK 9 1 64 1 ca1_6_0 = true := by decide +kernel

def ca1_6 : Cache := ca1_6_0

theorem ca1_6_ok : cacheOK 9 1 64 1 ca1_6 = true := ca1_6_0_ok

def ca2_6_0 : Cache := ofRawC [
  (6, [6], [(8, 1, [4])]),
  (69, [5, 1], [(7, 1, [3, 1])]),
  (132, [4, 2], [(73, 2, [4]),
    (6, 1, [2, 2])]),
  (195, [3, 3], [(10, 1, [4]),
    (10, 1, [3, 1])]),
  (4164, [4, 1, 1], [(54, 1, [4]),
    (6, 1, [2, 1, 1])]),
  (4227, [3, 2, 1], [(91, 2, [3, 1]),
    (5, 1, [2, 1, 1])]),
  (8322, [2, 2, 2], [(267, 2, [2, 2])]),
  (266307, [3, 1, 1, 1], [(168, 1, [3, 1]),
    (5, 1, [1, 1, 1, 1])]),
  (266370, [2, 2, 1, 1], [(54, 1, [2, 2]),
    (97, 1, [2, 1, 1])]),
  (17043522, [2, 1, 1, 1, 1], [(348, 1, [2, 1, 1]),
    (105, 2, [1, 1, 1, 1])]),
  (1090785345, [1, 1, 1, 1, 1, 1], [(930, 1, [1, 1, 1, 1])])]

set_option maxRecDepth 100000 in
theorem ca2_6_0_ok : cacheOK 9 1 64 2 ca2_6_0 = true := by decide +kernel

def ca2_6 : Cache := ca2_6_0

theorem ca2_6_ok : cacheOK 9 1 64 2 ca2_6 = true := ca2_6_0_ok

set_option maxRecDepth 100000 in
/-- `L(1) x_{9} = 7 x_{10}` modulo `U(Vir⁻) s₇`. -/
theorem chkA6_ok : chkGen ca1_6 xv6 xv5 wa6 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `L(2) x_{9} = 15 x_{11}` modulo `U(Vir⁻) s₇`. -/
theorem chkB6_ok : chkGen ca2_6 xv6 xv4 wb6 15 = true := by decide +kernel

end VOA.Classification.COne.OrbOdd
