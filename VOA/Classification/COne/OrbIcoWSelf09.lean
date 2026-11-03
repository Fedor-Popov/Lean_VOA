import VOA.Classification.COne.OrbIcoWSelf08

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self09Rows00 := jetRows 2 true 9 0
theorem self09Rows00_correct : jetRows 2 true 9 0 = self09Rows00 := rfl
def self09Row01 : List Jet := [[(3/2),-2,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self09Rows01 : List (List Jet) := self09Rows00 ++ [self09Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows01_correct : jetRows 2 true 9 1 = self09Rows01 := by
  rw [jetRows, self09Rows00_correct]
  change self09Rows00 ++ [jetStep 2 true 9 1 self09Rows00] = self09Rows00 ++ [self09Row01]
  congr 1
  decide +kernel
def self09Row02 : List Jet := [[(-51/44),(-85/44),(23/11)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self09Rows02 : List (List Jet) := self09Rows01 ++ [self09Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows02_correct : jetRows 2 true 9 2 = self09Rows02 := by
  rw [jetRows, self09Rows01_correct]
  change self09Rows01 ++ [jetStep 2 true 9 2 self09Rows01] = self09Rows01 ++ [self09Row02]
  congr 1
  decide +kernel
def self09Row03 : List Jet := [[(-23/44),(574/165),(193/220)],[(-17/220),(17/660),(17/165)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self09Rows03 : List (List Jet) := self09Rows02 ++ [self09Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows03_correct : jetRows 2 true 9 3 = self09Rows03 := by
  rw [jetRows, self09Rows02_correct]
  change self09Rows02 ++ [jetStep 2 true 9 3 self09Rows02] = self09Rows02 ++ [self09Row03]
  congr 1
  decide +kernel
def self09Row04 : List Jet := [[(315/176),(-2401/2640),(-34279/7920)],[(59/990),(266/1485),(-13/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self09Rows04 : List (List Jet) := self09Rows03 ++ [self09Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows04_correct : jetRows 2 true 9 4 = self09Rows04 := by
  rw [jetRows, self09Rows03_correct]
  change self09Rows03 ++ [jetStep 2 true 9 4 self09Rows03] = self09Rows03 ++ [self09Row04]
  congr 1
  decide +kernel
def self09Row05 : List Jet := [[(-1161/704),(-36703/10560),(113207/31680)],[(371/7920),(-40373/237600),(-11551/39600)],[(1/400),(1/600),(-1/240)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self09Rows05 : List (List Jet) := self09Rows04 ++ [self09Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows05_correct : jetRows 2 true 9 5 = self09Rows05 := by
  rw [jetRows, self09Rows04_correct]
  change self09Rows04 ++ [jetStep 2 true 9 5 self09Rows04] = self09Rows04 ++ [self09Row05]
  congr 1
  decide +kernel
def self09Row06 : List Jet := [[(1059/9856),(659639/110880),(72461/33264)],[(-1541/11880),(-167269/1425600),(54709/158400)],[(-289/151200),(-43129/4989600),(-11273/1663200)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self09Rows06 : List (List Jet) := self09Rows05 ++ [self09Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows06_correct : jetRows 2 true 9 6 = self09Rows06 := by
  rw [jetRows, self09Rows05_correct]
  change self09Rows05 ++ [jetStep 2 true 9 6 self09Rows05] = self09Rows05 ++ [self09Row06]
  congr 1
  decide +kernel
def self09Row07 : List Jet := [[(132987/68992),(-3775649/1034880),(-14118547/1552320)],[(385691/3991680),(13486159/29937600),(3953209/29937600)],[(-9059/3492720),(772903/209563200),(4073731/209563200)],[(-281/3880800),(-281/2328480),(281/3880800)],[0,0,0],[0,0,0],[0,0,0]]
def self09Rows07 : List (List Jet) := self09Rows06 ++ [self09Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows07_correct : jetRows 2 true 9 7 = self09Rows07 := by
  rw [jetRows, self09Rows06_correct]
  change self09Rows06 ++ [jetStep 2 true 9 7 self09Rows06] = self09Rows06 ++ [self09Row07]
  congr 1
  decide +kernel
def self09Row08 : List Jet := [[(-149937/50176),(-14494079/4139520),(1271704501/124185600)],[(221219/3193344),(-105473237/239500800),(-111961643/119750400)],[(5791/924000),(1012079/66528000),(-156097/24948000)],[(1571/29106000),(15167/43659000),(11863/21829500)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self09Rows08 : List (List Jet) := self09Rows07 ++ [self09Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows08_correct : jetRows 2 true 9 8 = self09Rows08 := by
  rw [jetRows, self09Rows07_correct]
  change self09Rows07 ++ [jetStep 2 true 9 8 self09Rows07] = self09Rows07 ++ [self09Row08]
  congr 1
  decide +kernel
def self09Row09 : List Jet := [[(5446015/3311616),(846631637/74511360),(1565805413/2235340800)],[(-6766813/25147584),(-6609633713/30177100800),(3319219651/2743372800)],[(-69647693/25147584000),(-580982947/18860688000),(-1762141783/37721376000)],[(172889/1257379200),(206603/3429216000),(-16897883/18860688000)],[(667/279417600),(667/104781600),(667/419126400)],[0,0,0],[0,0,0]]
def self09Rows09 : List (List Jet) := self09Rows08 ++ [self09Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows09_correct : jetRows 2 true 9 9 = self09Rows09 := by
  rw [jetRows, self09Rows08_correct]
  change self09Rows08 ++ [jetStep 2 true 9 9 self09Rows08] = self09Rows08 ++ [self09Row09]
  congr 1
  decide +kernel
def self09Row10 : List Jet := [[(5549365/2207744),(-1096231919/99348480),(-11242307441/496742400)],[(3247168307/12070840320),(123159690571/90531302400),(114482249179/301771008000)],[(-301353739/26943840000),(13333628017/2263282560000),(74975803733/754427520000)],[(-551071/1796256000),(-35378977/26943840000),(-14079287/13471920000)],[(-68743/41912640000),(-1991351/125737920000),(-2431619/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self09Rows10 : List (List Jet) := self09Rows09 ++ [self09Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows10_correct : jetRows 2 true 9 10 = self09Rows10 := by
  rw [jetRows, self09Rows09_correct]
  change self09Rows09 ++ [jetStep 2 true 9 10 self09Rows09] = self09Rows09 ++ [self09Row10]
  congr 1
  decide +kernel
def self09Row11 : List Jet := [[(-3479185/495616),(-738750029/78059520),(13215504289/390297600)],[(71278136827/265558487040),(-6447777984017/3983377305600),(-92268250265533/19916886528000)],[(23984971729/922078080000),(557740589089/5532468480000),(93918937/11290752000)],[(-2352601/20490624000),(461981213/251475840000),(1983641201/296382240000)],[(-420239/39517632000),(-97280963/4149351360000),(25312543/691558560000)],[(-793/6147187200),(-793/1676505600),(-793/1844156160)],[0,0,0]]
def self09Rows11 : List (List Jet) := self09Rows10 ++ [self09Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows11_correct : jetRows 2 true 9 11 = self09Rows11 := by
  rw [jetRows, self09Rows10_correct]
  change self09Rows10 ++ [jetStep 2 true 9 11 self09Rows10] = self09Rows10 ++ [self09Row11]
  congr 1
  decide +kernel
def self09Row12 : List Jet := [[(237566405/291422208),(62828890987/1192181760),(1539316590199/32784998400)],[(-172022361463/113810780160),(-44433496160659/11950131916800),(383688868816339/59750659584000)],[(582262917893/39833773056000),(-1958211374083/8535808512000),(-52672316185187/74688324480000)],[(218804420897/99584432640000),(1907854736059/298753297920000),(-1749669492077/298753297920000)],[(8407331/338722560000),(99088829/508083840000),(571630837/1422634752000)],[(31231/691558560000),(1541/1058508000),(183851/32931360000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self09Rows12 : List (List Jet) := self09Rows11 ++ [self09Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Rows12_correct : jetRows 2 true 9 12 = self09Rows12 := by
  rw [jetRows, self09Rows11_correct]
  change self09Rows11 ++ [jetStep 2 true 9 12 self09Rows11] = self09Rows11 ++ [self09Row12]
  congr 1
  decide +kernel
def self09Coeffs : List Jet := [[(-10125410175/48570368),(-10237342567/24285184),(1844636343757/1092833280)],[(159543919375/11381078016),(-6049314052835/68286468096),(-304230255638957/1707161702400)],[(3092775535189/2263282560000),(325611094145569/74688324480000),(-131025550916549/18672081120000)],[(-466089563/148191120000),(334610342789/1778293440000),(3544155986677/8298702720000)],[(-121202029/129667230000),(-163531609/311201352000),(14331063749/1556006760000)],[(-70789/4322241000),(-7485293/129667230000),(-27679/43222410000)],[(-2/12006225),(-2/3274425),(-4/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self09Coeffs_correct : widthCoefficients 2 true 9 = self09Coeffs := by
  rw [widthCoefficients,self09Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
