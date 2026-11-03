import VOA.Classification.COne.OrbIcoWSelf13

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self14Rows00 := jetRows 2 true 14 0
theorem self14Rows00_correct : jetRows 2 true 14 0 = self14Rows00 := rfl
def self14Row01 : List Jet := [[(2/3),(-17/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self14Rows01 : List (List Jet) := self14Rows00 ++ [self14Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows01_correct : jetRows 2 true 14 1 = self14Rows01 := by
  rw [jetRows, self14Rows00_correct]
  change self14Rows00 ++ [jetStep 2 true 14 1 self14Rows00] = self14Rows00 ++ [self14Row01]
  congr 1
  decide +kernel
def self14Row02 : List Jet := [[(-19/11),(-15/44),(17/4)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self14Rows02 : List (List Jet) := self14Rows01 ++ [self14Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows02_correct : jetRows 2 true 14 2 = self14Rows02 := by
  rw [jetRows, self14Rows01_correct]
  change self14Rows01 ++ [jetStep 2 true 14 2 self14Rows01] = self14Rows01 ++ [self14Row02]
  congr 1
  decide +kernel
def self14Row03 : List Jet := [[(12/11),(1753/330),(-314/165)],[(-17/495),(221/1980),(289/1980)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self14Rows03 : List (List Jet) := self14Rows02 ++ [self14Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows03_correct : jetRows 2 true 14 3 = self14Rows03 := by
  rw [jetRows, self14Rows02_correct]
  change self14Rows02 ++ [jetStep 2 true 14 3 self14Rows02] = self14Rows02 ++ [self14Row03]
  congr 1
  decide +kernel
def self14Row04 : List Jet := [[(9/11),(-76837/11880),(-1629/220)],[(47/495),(181/1485),(-334/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self14Rows04 : List (List Jet) := self14Rows03 ++ [self14Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows04_correct : jetRows 2 true 14 4 = self14Rows04 := by
  rw [jetRows, self14Rows03_correct]
  change self14Rows03 ++ [jetStep 2 true 14 4 self14Rows03] = self14Rows03 ++ [self14Row04]
  congr 1
  decide +kernel
def self14Row05 : List Jet := [[(-30/11),(1091/990),(241627/15840)],[(-221/3960),(-95813/237600),(-4793/19800)],[(1/900),(-1/400),(-1/120)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self14Rows05 : List (List Jet) := self14Rows04 ++ [self14Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows05_correct : jetRows 2 true 14 5 = self14Rows05 := by
  rw [jetRows, self14Rows04_correct]
  change self14Rows04 ++ [jetStep 2 true 14 5 self14Rows04] = self14Rows04 ++ [self14Row05]
  congr 1
  decide +kernel
def self14Row06 : List Jet := [[(35/11),(30829/3465),(-2399723/221760)],[(-13103/166320),(381233/1108800),(10246387/9979200)],[(-1391/415800),(-39989/4989600),(2059/554400)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self14Rows06 : List (List Jet) := self14Rows05 ++ [self14Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows06_correct : jetRows 2 true 14 6 = self14Rows06 := by
  rw [jetRows, self14Rows05_correct]
  change self14Rows05 ++ [jetStep 2 true 14 6 self14Rows05] = self14Rows05 ++ [self14Row06]
  congr 1
  decide +kernel
def self14Row07 : List Jet := [[(-40/33),(-711413/41580),(-3785743/332640)],[(257791/1164240),(1774501/6350400),(-9322661/7761600)],[(6101/3492720),(3920533/209563200),(5993881/209563200)],[(-281/8731800),(281/6985440),(3653/11642400)],[0,0,0],[0,0,0],[0,0,0]]
def self14Rows07 : List (List Jet) := self14Rows06 ++ [self14Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows07_correct : jetRows 2 true 14 7 = self14Rows07 := by
  rw [jetRows, self14Rows06_correct]
  change self14Rows06 ++ [jetStep 2 true 14 7 self14Rows06] = self14Rows06 ++ [self14Row07]
  congr 1
  decide +kernel
def self14Row08 : List Jet := [[-3,(106049/7392),(38676269/887040)],[(-2111227/9313920),(-701919359/558835200),(-220162169/558835200)],[(155123/31752000),(-36844823/4191264000),(-70438729/1047816000)],[(59/539000),(4243/10914750),(611/3969000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self14Rows08 : List (List Jet) := self14Rows07 ++ [self14Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows08_correct : jetRows 2 true 14 8 = self14Rows08 := by
  rw [jetRows, self14Rows07_correct]
  change self14Rows07 ++ [jetStep 2 true 14 8 self14Rows07] = self14Rows07 ++ [self14Row08]
  congr 1
  decide +kernel
def self14Row09 : List Jet := [[(82/11),(45033/6160),(-77143177/1330560)],[(-1234967/23950080),(352285403/205286400),(1979864311/479001600)],[(-39930301/3143448000),(-1485571039/37721376000),(2675657609/75442752000)],[(-28099/628689600),(-30352787/37721376000),(-38678663/18860688000)],[(667/628689600),(-667/2514758400),(-667/57153600)],[0,0,0],[0,0,0]]
def self14Rows09 : List (List Jet) := self14Rows08 ++ [self14Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows09_correct : jetRows 2 true 14 9 = self14Rows09 := by
  rw [jetRows, self14Rows08_correct]
  change self14Rows08 ++ [jetStep 2 true 14 9 self14Rows08] = self14Rows08 ++ [self14Row09]
  congr 1
  decide +kernel
def self14Row10 : List Jet := [[(-23/3),(-570511/12320),(5482237/1596672)],[(19544393/30481920),(-46219457/4023613440),(-15990868567/2095632000)],[(1882285687/188606880000),(36140142361/323326080000),(142982520473/754427520000)],[(-2996263/9430344000),(-69365237/565820640000),(725941177/188606880000)],[(-46447/10478160000),(-2673241/125737920000),(-3005663/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self14Rows10 : List (List Jet) := self14Rows09 ++ [self14Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows10_correct : jetRows 2 true 14 10 = self14Rows10 := by
  rw [jetRows, self14Rows09_correct]
  change self14Rows09 ++ [jetStep 2 true 14 10 self14Rows09] = self14Rows09 ++ [self14Row10]
  congr 1
  decide +kernel
def self14Row11 : List Jet := [[-4,(221929/3080),(66811819/365904)],[(-388875803/335301120),(-1328141040029/221298739200),(1391634692507/1106493696000)],[(2208898787/84680640000),(-648374783647/7113173760000),(-474068156167/711317376000)],[(109519/125737920),(28146103/5893965000),(27452547523/8298702720000)],[(40079/69155856000),(195743017/4149351360000),(253612571/1383117120000)],[(-793/13831171200),(-793/18441561600),(793/1229437440)],[0,0,0]]
def self14Rows11 : List (List Jet) := self14Rows10 ++ [self14Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows11_correct : jetRows 2 true 14 11 = self14Rows11 := by
  rw [jetRows, self14Rows10_correct]
  change self14Rows10 ++ [jetStep 2 true 14 11 self14Rows10] = self14Rows10 ++ [self14Row11]
  congr 1
  decide +kernel
def self14Row12 : List Jet := [[39,(668769/12320),(-32254027/69696)],[(-1672259069/4023613440),(42464027005273/2655584870400),(53858663551853/1106493696000)],[(-329209640269/2489610816000),(-16353789666229/29875329792000),(999736949917/1697461920000)],[(131250353/2263282560000),(-390939991711/27159390720000),(-16515842910317/298753297920000)],[(7096489/161663040000),(17077920611/149376648960000),(-5203547221/14937664896000)],[(144623/345779280000),(78313/29638224000),(60101/12349260000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self14Rows12 : List (List Jet) := self14Rows11 ++ [self14Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Rows12_correct : jetRows 2 true 14 12 = self14Rows12 := by
  rw [jetRows, self14Rows11_correct]
  change self14Rows11 ++ [jetStep 2 true 14 12 self14Rows11] = self14Rows11 ++ [self14Row12]
  congr 1
  decide +kernel
def self14Coeffs : List Jet := [[0,(41990/11),(157416943/40656)],[(-755018485/12192768),(-1169564990971/8047226880),(388126029954077/442597478400)],[(209757289999/1556006760000),(-581122473776923/37344162240000),(-5782410055783447/149376648960000)],[(4643733443/63510480000),(778095164687/5334880320000),(-10690574718011/10669760640000)],[(48292243/64833615000),(1259134829/155600676000),(21217325659/1556006760000)],[(-821/196465500),(566567/11787930000),(11382281/43222410000)],[(-8/108056025),(-2/36018675),(2/2401245)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self14Coeffs_correct : widthCoefficients 2 true 14 = self14Coeffs := by
  rw [widthCoefficients,self14Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
