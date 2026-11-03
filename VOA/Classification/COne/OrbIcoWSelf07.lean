import VOA.Classification.COne.OrbIcoWSelf06

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self07Rows00 := jetRows 2 true 7 0
theorem self07Rows00_correct : jetRows 2 true 7 0 = self07Rows00 := rfl
def self07Row01 : List Jet := [[(11/6),(-5/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self07Rows01 : List (List Jet) := self07Rows00 ++ [self07Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows01_correct : jetRows 2 true 7 1 = self07Rows01 := by
  rw [jetRows, self07Rows00_correct]
  change self07Rows00 ++ [jetStep 2 true 7 1 self07Rows00] = self07Rows00 ++ [self07Row01]
  congr 1
  decide +kernel
def self07Row02 : List Jet := [[(-95/132),(-283/132),(95/66)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self07Rows02 : List (List Jet) := self07Rows01 ++ [self07Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows02_correct : jetRows 2 true 7 2 = self07Rows02 := by
  rw [jetRows, self07Rows01_correct]
  change self07Rows01 ++ [jetStep 2 true 7 2 self07Rows01] = self07Rows01 ++ [self07Row02]
  congr 1
  decide +kernel
def self07Row03 : List Jet := [[(-415/396),(221/90),(2077/1980)],[(-17/180),(-17/1980),(17/198)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self07Rows03 : List (List Jet) := self07Rows02 ++ [self07Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows03_correct : jetRows 2 true 7 3 = self07Rows03 := by
  rw [jetRows, self07Rows02_correct]
  change self07Rows02 ++ [jetStep 2 true 7 3 self07Rows02] = self07Rows02 ++ [self07Row03]
  congr 1
  decide +kernel
def self07Row04 : List Jet := [[(24215/14256),(1769/4752),(-67103/23760)],[(293/8910),(244/1485),(137/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self07Rows04 : List (List Jet) := self07Rows03 ++ [self07Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows04_correct : jetRows 2 true 7 4 = self07Rows04 := by
  rw [jetRows, self07Rows03_correct]
  change self07Rows03 ++ [jetStep 2 true 7 4 self07Rows03] = self07Rows03 ++ [self07Row04]
  congr 1
  decide +kernel
def self07Row05 : List Jet := [[(-50135/57024),(-4756211/1425600),(25631/19008)],[(2329/29700),(-1801/26400),(-9089/39600)],[(11/3600),(1/300),(-1/400)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self07Rows05 : List (List Jet) := self07Rows04 ++ [self07Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows05_correct : jetRows 2 true 7 5 = self07Rows05 := by
  rw [jetRows, self07Rows04_correct]
  change self07Rows04 ++ [jetStep 2 true 7 5 self07Rows04] = self07Rows04 ++ [self07Row05]
  congr 1
  decide +kernel
def self07Row06 : List Jet := [[(-256915/342144),(3472697/935550),(2489287/997920)],[(-68063/598752),(-5620327/29937600),(1364983/9979200)],[(-12773/14968800),(-104147/14968800),(-8051/997920)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self07Rows06 : List (List Jet) := self07Rows05 ++ [self07Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows06_correct : jetRows 2 true 7 6 = self07Rows06 := by
  rw [jetRows, self07Rows05_correct]
  change self07Rows05 ++ [jetStep 2 true 7 6 self07Rows05] = self07Rows05 ++ [self07Row06]
  congr 1
  decide +kernel
def self07Row07 : List Jet := [[(2080495/1026432),(-22209233/35925120),(-486922783/89812800)],[(33645343/1257379200),(209416957/628689600),(163361717/628689600)],[(-80077/20956320),(-424759/209563200),(75307/6350400)],[(-281/3175200),(-6463/34927200),(-281/11642400)],[0,0,0],[0,0,0],[0,0,0]]
def self07Rows07 : List (List Jet) := self07Rows06 ++ [self07Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows07_correct : jetRows 2 true 7 7 = self07Rows07 := by
  rw [jetRows, self07Rows06_correct]
  change self07Rows06 ++ [jetStep 2 true 7 7 self07Rows06] = self07Rows06 ++ [self07Row07]
  congr 1
  decide +kernel
def self07Row08 : List Jet := [[(-15177995/8211456),(-41179247/9580032),(9089153561/2395008000)],[(1089008029/8382528000),(-1066694819/8382528000),(-1300433077/2095632000)],[(227587/46569600),(22853399/1397088000),(5063459/698544000)],[(3677/261954000),(6343/26195400),(8543/16372125)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self07Rows08 : List (List Jet) := self07Rows07 ++ [self07Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows08_correct : jetRows 2 true 7 8 = self07Rows08 := by
  rw [jetRows, self07Rows07_correct]
  change self07Rows07 ++ [jetStep 2 true 7 8 self07Rows07] = self07Rows07 ++ [self07Row08]
  congr 1
  decide +kernel
def self07Row09 : List Jet := [[(-2575195/13436928),(758040391/107775360),(2869910377/783820800)],[(-996426479/4618944000),(-846196867/1959552000),(892449077/2395008000)],[(76441727/45265651200),(-303499291/18860688000),(-1522123637/37721376000)],[(214591/1178793000),(13198441/37721376000),(-685057/2357586000)],[(667/228614400),(11339/1257379200),(8671/1257379200)],[0,0,0],[0,0,0]]
def self07Rows09 : List (List Jet) := self07Rows08 ++ [self07Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows09_correct : jetRows 2 true 7 9 = self07Rows09 := by
  rw [jetRows, self07Rows08_correct]
  change self07Rows08 ++ [jetStep 2 true 7 9 self07Rows08] = self07Rows08 ++ [self07Row09]
  congr 1
  decide +kernel
def self07Row10 : List Jet := [[(2745758561/886837248),(-400652222083/155196518400),(-16221005100043/1293304320000)],[(65256481883/1234517760000),(6067946810861/6789847680000),(4039417089749/4526565120000)],[(-1635013997/125737920000),(-1269469291/64665216000),(28770161891/754427520000)],[(-4283171/22632825600),(-42798011/37721376000),(-79490069/47151720000)],[(119159/377213760000),(-1085627/125737920000),(-502981/15717240000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self07Rows10 : List (List Jet) := self07Rows09 ++ [self07Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows10_correct : jetRows 2 true 7 10 = self07Rows10 := by
  rw [jetRows, self07Rows09_correct]
  change self07Rows09 ++ [jetStep 2 true 7 10 self07Rows09] = self07Rows09 ++ [self07Row10]
  congr 1
  decide +kernel
def self07Row11 : List Jet := [[(-34956381019/9755209728),(-2387050152301/213395212800),(185957975633053/21339521280000)],[(8647494834211/19916886528000),(-15040670270897/99584432640000),(-245087189601313/99584432640000)],[(21764185649/1778293440000),(5883724513/71850240000),(29055570721/323326080000)],[(-2209713719/4979221632000),(207632311/4979221632000),(7985490517/2074675680000)],[(-52046377/4149351360000),(-59437681/1383117120000),(-4131181/172889640000)],[(-793/5029516800),(-793/1229437440),(-793/922078080)],[0,0,0]]
def self07Rows11 : List (List Jet) := self07Rows10 ++ [self07Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows11_correct : jetRows 2 true 7 11 = self07Rows11 := by
  rw [jetRows, self07Rows10_correct]
  change self07Rows10 ++ [jetStep 2 true 7 11 self07Rows10] = self07Rows10 ++ [self07Row11]
  congr 1
  decide +kernel
def self07Row12 : List Jet := [[(-58399410055/10642046976),(78763660729351/4097188085760),(134616428405387/3658203648000)],[(-628256872830679/896259893760000),(-404750868067621/112032486720000),(-716614387473913/896259893760000)],[(3341396209597/71700791500800),(-2860569881959/179251978752000),(-1962461872157/5092385760000)],[(494264051621/298753297920000),(258419694499/33194810880000),(2078747055859/298753297920000)],[(12866863/4267904256000),(39391111/339492384000),(6320961223/16597405440000)],[(-117373/565820640000),(57283/222286680000),(43849/11855289600)],[(1/479001600),(1/79833600),(1/31933440)]]
def self07Rows12 : List (List Jet) := self07Rows11 ++ [self07Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Rows12_correct : jetRows 2 true 7 12 = self07Rows12 := by
  rw [jetRows, self07Rows11_correct]
  change self07Rows11 ++ [jetStep 2 true 7 12 self07Rows11] = self07Rows11 ++ [self07Row12]
  congr 1
  decide +kernel
def self07Coeffs : List Jet := [[(-2031489599825/58531258368),(-14393797367597/29265629184),(2365801391780213/5121485107200)],[(1106202466626167/56016243360000),(-5969750829488189/896259893760000),(-100650179736097183/896259893760000)],[(5967395116241/14937664896000),(35224649661319/8298702720000),(29221213568803/14937664896000)],[(-43284873439/1333720080000),(64427759771/1778293440000),(3381667093691/10669760640000)],[(-2474501149/2334010140000),(-2985241687/933604056000),(695174197/518668920000)],[(-470443/32416807500),(-3201241/43222410000),(-3976853/43222410000)],[(-2/9823275),(-2/2401245),(-8/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self07Coeffs_correct : widthCoefficients 2 true 7 = self07Coeffs := by
  rw [widthCoefficients,self07Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
