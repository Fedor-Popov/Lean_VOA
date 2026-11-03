import VOA.Classification.COne.OrbIcoWSelf01

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self02Rows00 := jetRows 2 true 2 0
theorem self02Rows00_correct : jetRows 2 true 2 0 = self02Rows00 := rfl
def self02Row01 : List Jet := [[(8/3),(-5/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self02Rows01 : List (List Jet) := self02Rows00 ++ [self02Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows01_correct : jetRows 2 true 2 1 = self02Rows01 := by
  rw [jetRows, self02Rows00_correct]
  change self02Rows00 ++ [jetStep 2 true 2 1 self02Rows00] = self02Rows00 ++ [self02Row01]
  congr 1
  decide +kernel
def self02Row02 : List Jet := [[(10/11),(-71/44),(15/44)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self02Rows02 : List (List Jet) := self02Rows01 ++ [self02Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows02_correct : jetRows 2 true 2 2 = self02Rows02 := by
  rw [jetRows, self02Rows01_correct]
  change self02Rows01 ++ [jetStep 2 true 2 2 self02Rows01] = self02Rows01 ++ [self02Row02]
  congr 1
  decide +kernel
def self02Row03 : List Jet := [[(-18/11),(49/110),(2/5)],[(-68/495),(-17/180),(17/396)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self02Rows03 : List (List Jet) := self02Rows02 ++ [self02Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows03_correct : jetRows 2 true 2 3 = self02Rows03 := by
  rw [jetRows, self02Rows02_correct]
  change self02Rows02 ++ [jetStep 2 true 2 3 self02Rows02] = self02Rows02 ++ [self02Row03]
  congr 1
  decide +kernel
def self02Row04 : List Jet := [[(35/66),(91/88),(-497/990)],[(-97/1485),(49/1485),(116/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self02Rows04 : List (List Jet) := self02Rows03 ++ [self02Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows04_correct : jetRows 2 true 2 4 = self02Rows04 := by
  rw [jetRows, self02Rows03_correct]
  change self02Rows03 ++ [jetStep 2 true 2 4 self02Rows03] = self02Rows03 ++ [self02Row04]
  congr 1
  decide +kernel
def self02Row05 : List Jet := [[(87/110),(-723/550),(-43/1760)],[(1547/14850),(7057/79200),(-907/19800)],[(1/225),(3/400),(1/600)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self02Rows05 : List (List Jet) := self02Rows04 ++ [self02Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows05_correct : jetRows 2 true 2 5 = self02Rows05 := by
  rw [jetRows, self02Rows04_correct]
  change self02Rows04 ++ [jetStep 2 true 2 5 self02Rows04] = self02Rows04 ++ [self02Row05]
  congr 1
  decide +kernel
def self02Row06 : List Jet := [[(-177/140),(2813/7700),(3015/4928)],[(-79/8910),(-147317/1425600),(-28817/475200)],[(1873/623700),(3497/1663200),(-1339/332640)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self02Rows06 : List (List Jet) := self02Rows05 ++ [self02Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows06_correct : jetRows 2 true 2 6 = self02Rows06 := by
  rw [jetRows, self02Rows05_correct]
  change self02Rows05 ++ [jetStep 2 true 2 6 self02Rows05] = self02Rows05 ++ [self02Row06]
  congr 1
  decide +kernel
def self02Row07 : List Jet := [[(701/1078),(31039/32340),(-922961/1293600)],[(-2741/28350),(-199/52800),(1128419/9979200)],[(-503/119070),(-1805239/209563200),(-68591/23284800)],[(-281/2182950),(-12083/34927200),(-281/1058400)],[0,0,0],[0,0,0],[0,0,0]]
def self02Rows07 : List (List Jet) := self02Rows06 ++ [self02Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows07_correct : jetRows 2 true 2 7 = self02Rows07 := by
  rw [jetRows, self02Rows06_correct]
  change self02Rows06 ++ [jetStep 2 true 2 7 self02Rows06] = self02Rows06 ++ [self02Row07]
  congr 1
  decide +kernel
def self02Row08 : List Jet := [[(22971/43120),(-671401/431200),(2365411/17248000)],[(2537659/24948000),(53713531/399168000),(-15767863/399168000)],[(-1387/935550),(1663351/598752000),(643339/74844000)],[(-5683/43659000),(-53/218295),(13/539000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self02Rows08 : List (List Jet) := self02Rows07 ++ [self02Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows08_correct : jetRows 2 true 2 8 = self02Rows08 := by
  rw [jetRows, self02Rows07_correct]
  change self02Rows07 ++ [jetStep 2 true 2 8 self02Rows07] = self02Rows07 ++ [self02Row08]
  congr 1
  decide +kernel
def self02Row09 : List Jet := [[(-2795/2156),(61653/86240),(3054361/3880800)],[(68045807/3143448000),(-273684199/1862784000),(-6120208453/50295168000)],[(336773/47151720),(411668273/37721376000),(-176547559/75442752000)],[(33067/214326000),(19747741/37721376000),(10507999/18860688000)],[(667/157172400),(39353/2514758400),(12673/628689600)],[0,0,0],[0,0,0]]
def self02Rows09 : List (List Jet) := self02Rows08 ++ [self02Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows09_correct : jetRows 2 true 2 9 = self02Rows09 := by
  rw [jetRows, self02Rows08_correct]
  change self02Rows08 ++ [jetStep 2 true 2 9 self02Rows08] = self02Rows08 ++ [self02Row09]
  congr 1
  decide +kernel
def self02Row10 : List Jet := [[(113243/161700),(16092061/12936000),(-1407898411/1164240000)],[(-5394808141/31434480000),(-23861768549/502951680000),(3236071843/15717240000)],[(-8676139/2886840000),(-454641703/30177100800),(-11723564099/754427520000)],[(18017/80831520),(238229/769824000),(-3334151/8981280000)],[(114791/15717240000),(2761103/125737920000),(184607/11430720000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self02Rows10 : List (List Jet) := self02Rows09 ++ [self02Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows10_correct : jetRows 2 true 2 10 = self02Rows10 := by
  rw [jetRows, self02Rows09_correct]
  change self02Rows09 ++ [jetStep 2 true 2 10 self02Rows09] = self02Rows09 ++ [self02Row10]
  congr 1
  decide +kernel
def self02Row11 : List Jet := [[(212381/169400),(-7859447/3388000),(26147419/609840000)],[(656902441/6286896000),(55062339587/167650560000),(53939809393/1844156160000)],[(-44170907933/3112013520000),(-629627984801/49792216320000),(8336978789/395176320000)],[(-25958939/51866892000),(-42550591/25933446000),(-607951697/395176320000)],[(-406247/74095560000),(-4956949/153679680000),(-91822793/1383117120000)],[(-793/3457792800),(-793/737662464),(-793/409812480)],[0,0,0]]
def self02Rows11 : List (List Jet) := self02Rows10 ++ [self02Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows11_correct : jetRows 2 true 2 11 = self02Rows11 := by
  rw [jetRows, self02Rows10_correct]
  change self02Rows10 ++ [jetStep 2 true 2 11 self02Rows10] = self02Rows10 ++ [self02Row11]
  congr 1
  decide +kernel
def self02Row12 : List Jet := [[(-1427829/948640),(-1396393/758912),(3237142351/1138368000)],[(24736196693/53887680000),(-150762358793/6035420160000),(-873420596891/1383117120000)],[(3534642773/233401014000),(268511915653/4267904256000),(1288653459553/24896108160000)],[(-20197160989/18672081120000),(-364272731509/298753297920000),(267177133873/99584432640000)],[(-5207401/106697606400),(-677039563/4267904256000),(-479635799/3556586880000)],[(-103483/94303440000),(-32083/7056720000),(-10601/1646568000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self02Rows12 : List (List Jet) := self02Rows11 ++ [self02Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Rows12_correct : jetRows 2 true 2 12 = self02Rows12 := by
  rw [jetRows, self02Rows11_correct]
  change self02Rows11 ++ [jetStep 2 true 2 12 self02Rows11] = self02Rows11 ++ [self02Row12]
  congr 1
  decide +kernel
def self02Coeffs : List Jet := [[(5799573/118580),(-31228821/592900),(1163950961/71148000)],[(-72377929637/14113440000),(20359405039753/1580705280000),(-5317041287809/1580705280000)],[(-30940149959/42436548000),(-21487996560257/37344162240000),(129967513853/181062604800)],[(-2810485691/333430020000),(-27987901387/484989120000),(-1483361472431/24896108160000)],[(9062819/16208403750),(-14695847/155600676000),(-1566555043/518668920000)],[(150803/8104201875),(49937/1600830000),(-1789523/43222410000)],[(-32/108056025),(-2/1440747),(-2/800415)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self02Coeffs_correct : widthCoefficients 2 true 2 = self02Coeffs := by
  rw [widthCoefficients,self02Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
