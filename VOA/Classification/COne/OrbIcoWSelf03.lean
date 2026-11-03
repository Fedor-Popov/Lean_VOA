import VOA.Classification.COne.OrbIcoWSelf02

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self03Rows00 := jetRows 2 true 3 0
theorem self03Rows00_correct : jetRows 2 true 3 0 = self03Rows00 := rfl
def self03Row01 : List Jet := [[(5/2),-1,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self03Rows01 : List (List Jet) := self03Rows00 ++ [self03Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows01_correct : jetRows 2 true 3 1 = self03Rows01 := by
  rw [jetRows, self03Rows00_correct]
  change self03Rows00 ++ [jetStep 2 true 3 1 self03Rows00] = self03Rows00 ++ [self03Row01]
  congr 1
  decide +kernel
def self03Row02 : List Jet := [[(23/44),(-81/44),(1/2)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self03Rows02 : List (List Jet) := self03Rows01 ++ [self03Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows02_correct : jetRows 2 true 3 2 = self03Rows02 := by
  rw [jetRows, self03Rows01_correct]
  change self03Rows01 ++ [jetStep 2 true 3 2 self03Rows01] = self03Rows01 ++ [self03Row02]
  congr 1
  decide +kernel
def self03Row03 : List Jet := [[(-1073/660),(47/66),(383/660)],[(-17/132),(-17/220),(17/330)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self03Rows03 : List (List Jet) := self03Rows02 ++ [self03Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows03_correct : jetRows 2 true 3 3 = self03Rows03 := by
  rw [jetRows, self03Rows02_correct]
  change self03Rows02 ++ [jetStep 2 true 3 3 self03Rows02] = self03Rows02 ++ [self03Row03]
  congr 1
  decide +kernel
def self03Row04 : List Jet := [[(6667/7920),(9059/7920),(-6097/7920)],[(-25/594),(104/1485),(49/594)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self03Rows04 : List (List Jet) := self03Rows03 ++ [self03Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows04_correct : jetRows 2 true 3 4 = self03Rows04 := by
  rw [jetRows, self03Rows03_correct]
  change self03Rows03 ++ [jetStep 2 true 3 4 self03Rows03] = self03Rows03 ++ [self03Row04]
  congr 1
  decide +kernel
def self03Row05 : List Jet := [[(85781/158400),(-18169/10560),(-4687/158400)],[(6343/59400),(17927/237600),(-333/4400)],[(1/240),(1/150),(1/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self03Rows05 : List (List Jet) := self03Rows04 ++ [self03Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows05_correct : jetRows 2 true 3 5 = self03Rows05 := by
  rw [jetRows, self03Rows04_correct]
  change self03Rows04 ++ [jetStep 2 true 3 5 self03Rows04] = self03Rows04 ++ [self03Row05]
  congr 1
  decide +kernel
def self03Row06 : List Jet := [[(-255059/190080),(80573/118800),(45643/47520)],[(-24581/712800),(-202991/1425600),(-61241/1108800)],[(2089/997920),(-1313/4989600),(-9421/1663200)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self03Rows06 : List (List Jet) := self03Rows05 ++ [self03Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows06_correct : jetRows 2 true 3 6 = self03Rows06 := by
  rw [jetRows, self03Rows05_correct]
  change self03Rows05 ++ [jetStep 2 true 3 6 self03Rows05] = self03Rows05 ++ [self03Row06]
  congr 1
  decide +kernel
def self03Row07 : List Jet := [[(6685339/6652800),(800753/739200),(-59387/52800)],[(-988469/11975040),(937/20160),(33123011/209563200)],[(-474451/104781600),(-199667/23284800),(-263029/209563200)],[(-281/2328480),(-3653/11642400),(-281/1293600)],[0,0,0],[0,0,0],[0,0,0]]
def self03Rows07 : List (List Jet) := self03Rows06 ++ [self03Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows07_correct : jetRows 2 true 3 7 = self03Rows07 := by
  rw [jetRows, self03Rows06_correct]
  change self03Rows06 ++ [jetStep 2 true 3 7 self03Rows06] = self03Rows06 ++ [self03Row07]
  congr 1
  decide +kernel
def self03Row08 : List Jet := [[(5520527/24192000),(-8023613/3801600),(15758363/88704000)],[(4258813/34214400),(24251717/171072000),(-14473399/149688000)],[(-3751/63504000),(3099989/465696000),(7829981/698544000)],[(-1681/17463600),(-1753/14553000),(173/992250)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self03Rows08 : List (List Jet) := self03Rows07 ++ [self03Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows08_correct : jetRows 2 true 3 8 = self03Rows08 := by
  rw [jetRows, self03Rows07_correct]
  change self03Rows07 ++ [jetStep 2 true 3 8 self03Rows07] = self03Rows07 ++ [self03Row08]
  congr 1
  decide +kernel
def self03Row09 : List Jet := [[(-6757219717/4790016000),(163816921/133056000),(6410529331/4790016000)],[(-9462773/431101440),(-5078823493/21555072000),(-20641858001/150885504000)],[(10743617/1539648000),(157856129/18860688000),(-309862741/37721376000)],[(48401/269438400),(21694153/37721376000),(4924529/9430344000)],[(667/167650560),(667/46569600),(667/38102400)],[0,0,0],[0,0,0]]
def self03Rows09 : List (List Jet) := self03Rows08 ++ [self03Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows09_correct : jetRows 2 true 3 9 = self03Rows09 := by
  rw [jetRows, self03Rows08_correct]
  change self03Rows08 ++ [jetStep 2 true 3 9 self03Rows08] = self03Rows08 ++ [self03Row09]
  congr 1
  decide +kernel
def self03Row10 : List Jet := [[(5498539561/4354560000),(14134258409/9580032000),(-93931787009/47900160000)],[(-10007120957/58786560000),(11377285889/323326080000),(10480968671/30792960000)],[(-38929537/6466521600),(-1412317343/64665216000),(-593080357/35925120000)],[(26726899/188606880000),(-3665063/188606880000),(-19653929/23575860000)],[(142493/25147584000),(1810909/125737920000),(91913/31434480000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self03Rows10 : List (List Jet) := self03Rows09 ++ [self03Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows10_correct : jetRows 2 true 3 10 = self03Rows10 := by
  rw [jetRows, self03Rows09_correct]
  change self03Rows09 ++ [jetStep 2 true 3 10 self03Rows09] = self03Rows09 ++ [self03Row10]
  congr 1
  decide +kernel
def self03Row11 : List Jet := [[(843143639/870912000),(-13951724713/3991680000),(-10062962423/52690176000)],[(262345562879/1293304320000),(2152849923619/4742115840000),(-1124181561439/14226347520000)],[(-347784511/29638224000),(80491099/368831232000),(339705736879/8298702720000)],[(-9113347/15396480000),(-121695463/68584320000),(-275755933/230519520000)],[(-7099801/829870272000),(-179916883/4149351360000),(-8850619/115259760000)],[(-793/3688312320),(-18239/18441561600),(-793/461039040)],[0,0,0]]
def self03Rows11 : List (List Jet) := self03Rows10 ++ [self03Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows11_correct : jetRows 2 true 3 11 = self03Rows11 := by
  rw [jetRows, self03Rows10_correct]
  change self03Rows10 ++ [jetStep 2 true 3 11 self03Rows10] = self03Rows10 ++ [self03Row11]
  congr 1
  decide +kernel
def self03Row12 : List Jet := [[(-155609183171/52254720000),(-162804094709/82114560000),(57352757981/11290752000)],[(328668185963/775982592000),(-557305662313/1422634752000),(-46759375093253/42679042560000)],[(2506678621577/85358085120000),(1299697515299/14226347520000),(300931794853/6789847680000)],[(-91619323/155196518400),(7197577/7838208000),(49846161457/8535808512000)],[(-189839423/4526565120000),(-1424728103/12448054080000),(-439217957/16597405440000)],[(-369221/414935136000),(-250361/74095560000),(-374497/98794080000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self03Rows12 : List (List Jet) := self03Rows11 ++ [self03Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Rows12_correct : jetRows 2 true 3 12 = self03Rows12 := by
  rw [jetRows, self03Rows11_correct]
  change self03Rows11 ++ [jetStep 2 true 3 12 self03Rows11] = self03Rows11 ++ [self03Row12]
  congr 1
  decide +kernel
def self03Coeffs : List Jet := [[(87165995449/1244160000),(-674923453217/6842880000),(59736634351/2787840000)],[(-2115911269/2519424000),(128246432207/6842880000),(-42353706166033/6097006080000)],[(-1245482305187/1524251520000),(-707549924849/3556586880000),(116285859747773/74688324480000)],[(-1728391157/74095560000),(-150314626541/1778293440000),(-159039847751/3556586880000)],[(59630911/778003380000),(-2714130833/1556006760000),(-784222253/172889640000)],[(1189/147349125),(-131933/11787930000),(-1402211/14407470000)],[(-2/7203735),(-46/36018675),(-16/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self03Coeffs_correct : widthCoefficients 2 true 3 = self03Coeffs := by
  rw [widthCoefficients,self03Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
