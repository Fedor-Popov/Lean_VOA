import VOA.Classification.COne.OrbIcoWSelf19

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self20Rows00 := jetRows 1 true 20 0
theorem self20Rows00_correct : jetRows 1 true 20 0 = self20Rows00 := rfl
def self20Row01 : List Jet := [[(-1/3),(-23/6)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self20Rows01 : List (List Jet) := self20Rows00 ++ [self20Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows01_correct : jetRows 1 true 20 1 = self20Rows01 := by
  rw [jetRows, self20Rows00_correct]
  change self20Rows00 ++ [jetStep 1 true 20 1 self20Rows00] = self20Rows00 ++ [self20Row01]
  congr 1
  decide +kernel
def self20Row02 : List Jet := [[(-31/22),(157/44)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self20Rows02 : List (List Jet) := self20Rows01 ++ [self20Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows02_correct : jetRows 1 true 20 2 = self20Rows02 := by
  rw [jetRows, self20Rows01_correct]
  change self20Rows01 ++ [jetStep 1 true 20 2 self20Rows01] = self20Rows01 ++ [self20Row02]
  congr 1
  decide +kernel
def self20Row03 : List Jet := [[(30/11),(39/11)],[(17/990),(85/396)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self20Rows03 : List (List Jet) := self20Rows02 ++ [self20Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows03_correct : jetRows 1 true 20 3 = self20Rows03 := by
  rw [jetRows, self20Rows02_correct]
  change self20Rows02 ++ [jetStep 1 true 20 3 self20Rows02] = self20Rows02 ++ [self20Row03]
  congr 1
  decide +kernel
def self20Row04 : List Jet := [[(-25/11),(-5435/396)],[(116/1485),(-37/297)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def self20Rows04 : List (List Jet) := self20Rows03 ++ [self20Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows04_correct : jetRows 1 true 20 4 = self20Rows04 := by
  rw [jetRows, self20Rows03_correct]
  change self20Rows03 ++ [jetStep 1 true 20 4 self20Rows03] = self20Rows03 ++ [self20Row04]
  congr 1
  decide +kernel
def self20Row05 : List Jet := [[(-21/44),(8197/440)],[(-19427/118800),(-3547/8800)],[(-1/1800),(-3/400)],[0,0],[0,0],[0,0],[0,0]]
def self20Rows05 : List (List Jet) := self20Rows04 ++ [self20Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows05_correct : jetRows 1 true 20 5 = self20Rows05 := by
  rw [jetRows, self20Rows04_correct]
  change self20Rows04 ++ [jetStep 1 true 20 5 self20Rows04] = self20Rows04 ++ [self20Row05]
  congr 1
  decide +kernel
def self20Row06 : List Jet := [[(2953/616),(-56051/6160)],[(676267/4989600),(11220331/9979200)],[(-631/226800),(3121/1663200)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def self20Rows06 : List (List Jet) := self20Rows05 ++ [self20Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows06_correct : jetRows 1 true 20 6 = self20Rows06 := by
  rw [jetRows, self20Rows05_correct]
  change self20Rows05 ++ [jetStep 1 true 20 6 self20Rows05] = self20Rows05 ++ [self20Row06]
  congr 1
  decide +kernel
def self20Row07 : List Jet := [[(-13756/1617),(-636121/32340)],[(11887/142560),(-878851/665280)],[(681787/104781600),(5004119/209563200)],[(281/17463600),(8149/34927200)],[0,0],[0,0],[0,0]]
def self20Rows07 : List (List Jet) := self20Rows06 ++ [self20Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows07_correct : jetRows 1 true 20 7 = self20Rows07 := by
  rw [jetRows, self20Rows06_correct]
  change self20Rows06 ++ [jetStep 1 true 20 7 self20Rows06] = self20Rows06 ++ [self20Row07]
  congr 1
  decide +kernel
def self20Row08 : List Jet := [[(6365/784),(1057983/17248)],[(-95097061/199584000),(-23507537/399168000)],[(-11373737/2095632000),(-255052859/4191264000)],[(2017/21829500),(439/21829500)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def self20Rows08 : List (List Jet) := self20Rows07 ++ [self20Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows08_correct : jetRows 1 true 20 8 = self20Rows08 := by
  rw [jetRows, self20Rows07_correct]
  change self20Rows07 ++ [jetStep 1 true 20 8 self20Rows07] = self20Rows07 ++ [self20Row08]
  congr 1
  decide +kernel
def self20Row09 : List Jet := [[(5035/8624),(-61876/693)],[(21055116553/25147584000),(65704304927/16765056000)],[(-405311/53887680),(337317731/5388768000)],[(-693563/2694384000),(-4358833/3429216000)],[(-667/1257379200),(-20677/2514758400)],[0,0],[0,0]]
def self20Rows09 : List (List Jet) := self20Rows08 ++ [self20Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows09_correct : jetRows 1 true 20 9 = self20Rows09 := by
  rw [jetRows, self20Rows08_correct]
  change self20Rows08 ++ [jetStep 1 true 20 9 self20Rows08] = self20Rows08 ++ [self20Row09]
  congr 1
  decide +kernel
def self20Row10 : List Jet := [[(-1075685/51744),(99690037/2328480)],[(-154322811131/251475840000),(-4883885852729/502951680000)],[(1690935781/45265651200),(61234887067/754427520000)],[(63937651/282910320000),(2721571/776160000)],[(-240697/62868960000),(-507517/125737920000)],[(-1/39916800),(-1/7983360)],[0,0]]
def self20Rows10 : List (List Jet) := self20Rows09 ++ [self20Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows10_correct : jetRows 1 true 20 10 = self20Rows10 := by
  rw [jetRows, self20Rows09_correct]
  change self20Rows09 ++ [jetStep 1 true 20 10 self20Rows09] = self20Rows09 ++ [self20Row10]
  congr 1
  decide +kernel
def self20Row11 : List Jet := [[(2335955/47432),(213473539/1067220)],[(-3988357639117/2766234240000),(1380431552299/122943744000)],[(-362195352119/4979221632000),(-29040281231933/49792216320000)],[(9214987/11855289600),(-86299627/26943840000)],[(4495303/296382240000),(26532487/276623424000)],[(793/27662342400),(793/1676505600)],[0,0]]
def self20Rows11 : List (List Jet) := self20Rows10 ++ [self20Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows11_correct : jetRows 1 true 20 11 = self20Rows11 := by
  rw [jetRows, self20Rows10_correct]
  change self20Rows10 ++ [jetStep 1 true 20 11 self20Rows10] = self20Rows10 ++ [self20Row11]
  congr 1
  decide +kernel
def self20Row12 : List Jet := [[(-324615/6776),(-22730123/24640)],[(58522432123381/6638962176000),(357461044867063/13277924352000)],[(45085652341/74688324480000),(269266621201691/149376648960000)],[(-811925261549/149376648960000),(-7371657876421/298753297920000)],[(-1405143433/74688324480000),(-66427866803/149376648960000)],[(49103/129667230000),(1541/2352240000)],[(1/479001600),(1/79833600)]]
def self20Rows12 : List (List Jet) := self20Rows11 ++ [self20Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Rows12_correct : jetRows 1 true 20 12 = self20Rows12 := by
  rw [jetRows, self20Rows11_correct]
  change self20Rows11 ++ [jetStep 1 true 20 12 self20Rows11] = self20Rows11 ++ [self20Row12]
  congr 1
  decide +kernel
def self20Coeffs : List Jet := [[(82776825/47432),(-115690100/17787)],[(500741936104313/5532468480000),(16226013610695901/11064936960000)],[(-19760416470769/3394923840000),(2449744163369/1867208112000)],[(-377292455989/4668020280000),(-44762509796969/37344162240000)],[(109231/77182875),(-69958841/22228668000)],[(172033/9261945000),(23233/176418000)],[(4/108056025),(2/3274425)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self20Coeffs_correct : widthCoefficients 1 true 20 = self20Coeffs := by
  rw [widthCoefficients,self20Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
