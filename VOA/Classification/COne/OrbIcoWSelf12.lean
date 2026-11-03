import VOA.Classification.COne.OrbIcoWSelf11

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self12Rows00 := jetRows 2 true 12 0
theorem self12Rows00_correct : jetRows 2 true 12 0 = self12Rows00 := rfl
def self12Row01 : List Jet := [[1,(-5/2),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self12Rows01 : List (List Jet) := self12Rows00 ++ [self12Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows01_correct : jetRows 2 true 12 1 = self12Rows01 := by
  rw [jetRows, self12Rows00_correct]
  change self12Rows00 ++ [jetStep 2 true 12 1 self12Rows00] = self12Rows00 ++ [self12Row01]
  congr 1
  decide +kernel
def self12Row02 : List Jet := [[(-35/22),(-51/44),(145/44)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self12Rows02 : List (List Jet) := self12Rows01 ++ [self12Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows02_correct : jetRows 2 true 12 2 = self12Rows02 := by
  rw [jetRows, self12Rows01_correct]
  change self12Rows01 ++ [jetStep 2 true 12 2 self12Rows01] = self12Rows01 ++ [self12Row02]
  congr 1
  decide +kernel
def self12Row03 : List Jet := [[(14/33),(791/165),(-49/165)],[(-17/330),(17/220),(17/132)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self12Rows03 : List (List Jet) := self12Rows02 ++ [self12Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows03_correct : jetRows 2 true 12 3 = self12Rows03 := by
  rw [jetRows, self12Rows02_correct]
  change self12Rows02 ++ [jetStep 2 true 12 3 self12Rows02] = self12Rows02 ++ [self12Row03]
  congr 1
  decide +kernel
def self12Row04 : List Jet := [[(140/99),(-1553/396),(-25913/3960)],[(128/1485),(239/1485),(-179/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self12Rows04 : List (List Jet) := self12Rows03 ++ [self12Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows04_correct : jetRows 2 true 12 4 = self12Rows04 := by
  rw [jetRows, self12Rows03_correct]
  change self12Rows03 ++ [jetStep 2 true 12 4 self12Rows03] = self12Rows03 ++ [self12Row04]
  congr 1
  decide +kernel
def self12Row05 : List Jet := [[(-4991/1980),(-11641/6600),(75811/7920)],[(-1519/118800),(-76489/237600),(-511/1650)],[(1/600),(-1/1200),(-1/150)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self12Rows05 : List (List Jet) := self12Rows04 ++ [self12Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows05_correct : jetRows 2 true 12 5 = self12Rows05 := by
  rw [jetRows, self12Rows04_correct]
  change self12Rows04 ++ [jetStep 2 true 12 5 self12Rows04] = self12Rows04 ++ [self12Row05]
  congr 1
  decide +kernel
def self12Row06 : List Jet := [[(22519/11880),(1033757/118800),(-903407/332640)],[(-114997/997920),(1154851/9979200),(278149/369600)],[(-7433/2494800),(-45389/4989600),(-115/66528)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self12Rows06 : List (List Jet) := self12Rows05 ++ [self12Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows06_correct : jetRows 2 true 12 6 = self12Rows06 := by
  rw [jetRows, self12Rows05_correct]
  change self12Rows05 ++ [jetStep 2 true 12 6 self12Rows05] = self12Rows05 ++ [self12Row06]
  congr 1
  decide +kernel
def self12Row07 : List Jet := [[(167/297),(-51463/4620),(-12955267/970200)],[(19669589/104781600),(31790573/69854400),(-49661573/104781600)],[(-323/2993760),(130451/9979200),(826583/29937600)],[(-281/5821200),(-281/11642400),(281/1293600)],[0,0,0],[0,0,0],[0,0,0]]
def self12Rows07 : List (List Jet) := self12Rows06 ++ [self12Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows07_correct : jetRows 2 true 12 7 = self12Rows07 := by
  rw [jetRows, self12Rows06_correct]
  change self12Rows06 ++ [jetStep 2 true 12 7 self12Rows06] = self12Rows06 ++ [self12Row07]
  congr 1
  decide +kernel
def self12Row08 : List Jet := [[(-89267/23760),(6440521/1663200),(1096792591/38808000)],[(-387778133/4191264000),(-8293555189/8382528000),(-8326634993/8382528000)],[(126107/19958400),(283499/66528000),(-3973603/99792000)],[(2071/21829500),(199/485100),(16843/43659000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self12Rows08 : List (List Jet) := self12Rows07 ++ [self12Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows08_correct : jetRows 2 true 12 8 = self12Rows08 := by
  rw [jetRows, self12Rows07_correct]
  change self12Rows07 ++ [jetStep 2 true 12 8 self12Rows07] = self12Rows07 ++ [self12Row08]
  congr 1
  decide +kernel
def self12Row09 : List Jet := [[(228389/42768),(328657/23760),(-47740321/2138400)],[(-15816357257/75442752000),(15508739993/21555072000),(462332600911/150885504000)],[(-17920099/1886068800),(-1642327787/37721376000),(-1388272139/75442752000)],[(8683/244944000),(-2499437/5388768000),(-72557/42099750)],[(667/419126400),(667/279417600),(-667/104781600)],[0,0,0],[0,0,0]]
def self12Rows09 : List (List Jet) := self12Rows08 ++ [self12Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows09_correct : jetRows 2 true 12 9 = self12Rows09 := by
  rw [jetRows, self12Rows08_correct]
  change self12Rows08 ++ [jetStep 2 true 12 9 self12Rows08] = self12Rows08 ++ [self12Row09]
  congr 1
  decide +kernel
def self12Row10 : List Jet := [[(-4416209/2138400),(-86813213/2673000),(-19871654171/748440000)],[(1298701882273/2263282560000),(5458993561039/4526565120000),(-1165092620053/377213760000)],[(-913639183/1131641280000),(30869290261/452656512000),(15526093459/83825280000)],[(-1386379/3772137600),(-3026033/3429216000),(269295119/188606880000)],[(-231061/62868960000),(-242887/11430720000),(-402443/11430720000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self12Rows10 : List (List Jet) := self12Rows09 ++ [self12Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows10_correct : jetRows 2 true 12 10 = self12Rows10 := by
  rw [jetRows, self12Rows09_correct]
  change self12Rows09 ++ [jetStep 2 true 12 10 self12Rows09] = self12Rows09 ++ [self12Row10]
  congr 1
  decide +kernel
def self12Row11 : List Jet := [[(-428281/48600),(6613753/297000),(2002222261/17010000)],[(-2315259858829/4979221632000),(-8739540993643/1844156160000),(-35209667311757/7113173760000)],[(287983367387/8298702720000),(186453244091/5532468480000),(-2782305118391/8298702720000)],[(209787353/414935136000),(1753887757/414935136000),(20177057441/2766234240000)],[(-1370773/296382240000),(10602191/592764480000),(325691/2439360000)],[(-793/9220780800),(-793/3688312320),(793/3688312320)],[0,0,0]]
def self12Rows11 : List (List Jet) := self12Rows10 ++ [self12Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows11_correct : jetRows 2 true 12 11 = self12Rows11 := by
  rw [jetRows, self12Rows10_correct]
  change self12Rows10 ++ [jetStep 2 true 12 11 self12Rows10] = self12Rows10 ++ [self12Row11]
  congr 1
  decide +kernel
def self12Row12 : List Jet := [[(1341011/58320),(112531613/1166400),(-5950370527/56133000)],[(-73119602213029/42679042560000),(39666801222541/9484231680000),(1351615474720927/42679042560000)],[(-1108873619107/14937664896000),(-5491376178203/9958443264000),(-38671736775031/74688324480000)],[(32395311569/21339521280000),(-391557222103/99584432640000),(-11211509337901/298753297920000)],[(218671637/4979221632000),(1986358139/9958443264000),(56278267/691558560000)],[(81253/259334460000),(367187/148191120000),(60101/9879408000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self12Rows12 : List (List Jet) := self12Rows11 ++ [self12Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Rows12_correct : jetRows 2 true 12 12 = self12Rows12 := by
  rw [jetRows, self12Rows11_correct]
  change self12Rows11 ++ [jetStep 2 true 12 12 self12Rows11] = self12Rows11 ++ [self12Row12]
  congr 1
  decide +kernel
def self12Coeffs : List Jet := [[(-2997967/9720),(92697157/66825),(1541827187/324000)],[(-4217421831252193/149376648960000),(-21554392560536131/99584432640000),(36634335481619429/298753297920000)],[(2284638444677/1493766489600),(-1192568831413/259334460000),(-949357062243613/29875329792000)],[(2309112397/43222410000),(3640667736877/12448054080000),(-2223487695311/24896108160000)],[(-4042141/97250422500),(74338763/14145516000),(1268739341/74095560000)],[(-103003/9261945000),(691/1683990000),(347927/2058210000)],[(-4/36018675),(-2/7203735),(2/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self12Coeffs_correct : widthCoefficients 2 true 12 = self12Coeffs := by
  rw [widthCoefficients,self12Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
