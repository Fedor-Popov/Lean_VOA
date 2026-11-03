import VOA.Classification.COne.OrbIcoWSelf15

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self16Rows00 := jetRows 1 true 16 0
theorem self16Rows00_correct : jetRows 1 true 16 0 = self16Rows00 := rfl
def self16Row01 : List Jet := [[(1/3),(-19/6)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self16Rows01 : List (List Jet) := self16Rows00 ++ [self16Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows01_correct : jetRows 1 true 16 1 = self16Rows01 := by
  rw [jetRows, self16Rows00_correct]
  change self16Rows00 ++ [jetStep 1 true 16 1 self16Rows00] = self16Rows00 ++ [self16Row01]
  congr 1
  decide +kernel
def self16Row02 : List Jet := [[(-115/66),(95/132)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self16Rows02 : List (List Jet) := self16Rows01 ++ [self16Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows02_correct : jetRows 1 true 16 2 = self16Rows02 := by
  rw [jetRows, self16Rows01_correct]
  change self16Rows01 ++ [jetStep 1 true 16 2 self16Rows01] = self16Rows01 ++ [self16Row02]
  congr 1
  decide +kernel
def self16Row03 : List Jet := [[(856/495),(532/99)],[(-17/990),(289/1980)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self16Rows03 : List (List Jet) := self16Rows02 ++ [self16Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows03_correct : jetRows 1 true 16 3 = self16Rows03 := by
  rw [jetRows, self16Rows02_correct]
  change self16Rows02 ++ [jetStep 1 true 16 3 self16Rows02] = self16Rows02 ++ [self16Row03]
  congr 1
  decide +kernel
def self16Row04 : List Jet := [[(-259/8910),(-5453/594)],[(86/891),(91/1485)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def self16Rows04 : List (List Jet) := self16Rows03 ++ [self16Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows04_correct : jetRows 1 true 16 4 = self16Rows04 := by
  rw [jetRows, self16Rows03_correct]
  change self16Rows03 ++ [jetStep 1 true 16 4 self16Rows03] = self16Rows03 ++ [self16Row04]
  congr 1
  decide +kernel
def self16Row05 : List Jet := [[(-5071/2025),(985967/178200)],[(-2317/23760),(-35867/79200)],[(1/1800),(-1/240)],[0,0],[0,0],[0,0],[0,0]]
def self16Rows05 : List (List Jet) := self16Rows04 ++ [self16Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows05_correct : jetRows 1 true 16 5 = self16Rows05 := by
  rw [jetRows, self16Rows04_correct]
  change self16Rows04 ++ [jetStep 1 true 16 5 self16Rows04] = self16Rows04 ++ [self16Row05]
  congr 1
  decide +kernel
def self16Row06 : List Jet := [[(4001891/935550),(49565167/7484400)],[(-869/38880),(2602547/4276800)],[(-5141/1496880),(-87191/14968800)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def self16Rows06 : List (List Jet) := self16Rows05 ++ [self16Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows06_correct : jetRows 1 true 16 6 = self16Rows06 := by
  rw [jetRows, self16Rows05_correct]
  change self16Rows05 ++ [jetStep 1 true 16 6 self16Rows05] = self16Rows05 ++ [self16Row06]
  congr 1
  decide +kernel
def self16Row07 : List Jet := [[(-1391722/392931),(-174019309/7858620)],[(9901183/44906400),(-6683993/89812800)],[(374449/104781600),(960583/41912640)],[(-281/17463600),(3653/34927200)],[0,0],[0,0],[0,0]]
def self16Rows07 : List (List Jet) := self16Rows06 ++ [self16Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows07_correct : jetRows 1 true 16 7 = self16Rows07 := by
  rw [jetRows, self16Rows06_correct]
  change self16Rows06 ++ [jetStep 1 true 16 7 self16Rows06] = self16Rows06 ++ [self16Row07]
  congr 1
  decide +kernel
def self16Row08 : List Jet := [[(-79364381/98232750),(7627759399/261954000)],[(-212735497/598752000),(-307840783/239500800)],[(231961/99792000),(-5042503/199584000)],[(373/3274425),(20731/65488500)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def self16Rows08 : List (List Jet) := self16Rows07 ++ [self16Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows08_correct : jetRows 1 true 16 8 = self16Rows08 := by
  rw [jetRows, self16Rows07_correct]
  change self16Rows07 ++ [jetStep 1 true 16 8 self16Rows07] = self16Rows07 ++ [self16Row08]
  congr 1
  decide +kernel
def self16Row09 : List Jet := [[(3588515176/442047375),(-12562499819/1178793000)],[(8988185783/45265651200),(424920398323/150885504000)],[(-196211291/14145516000),(-795125483/37721376000)],[(-473107/3772137600),(-40891019/37721376000)],[(667/1257379200),(-667/228614400)],[0,0],[0,0]]
def self16Rows09 : List (List Jet) := self16Rows08 ++ [self16Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows09_correct : jetRows 1 true 16 9 = self16Rows09 := by
  rw [jetRows, self16Rows08_correct]
  change self16Rows08 ++ [jetStep 1 true 16 9 self16Rows08] = self16Rows08 ++ [self16Row09]
  congr 1
  decide +kernel
def self16Row10 : List Jet := [[(-8584793348/602791875),(-5130786348421/106091370000)],[(676782064489/1357969536000),(-32460663816011/13579695360000)],[(234405943/10777536000),(63386855177/452656512000)],[(-7892821/40415760000),(25587967/26943840000)],[(-177697/37721376000),(-2313029/125737920000)],[(-1/39916800),(-1/7983360)],[0,0]]
def self16Rows10 : List (List Jet) := self16Rows09 ++ [self16Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows10_correct : jetRows 1 true 16 10 = self16Rows10 := by
  rw [jetRows, self16Rows09_correct]
  change self16Rows09 ++ [jetStep 1 true 16 10 self16Rows09] = self16Rows09 ++ [self16Row10]
  congr 1
  decide +kernel
def self16Row11 : List Jet := [[(83433535952/10419688125),(580750542703/4167875250)],[(-8825630010191/4979221632000),(-238461079465537/49792216320000)],[(705595427/199168865280),(-177280556479/663896217600)],[(6777378119/6224027040000),(2203985221/565820640000)],[(51011/8468064000),(33571841/461039040000)],[(-793/27662342400),(793/6147187200)],[0,0]]
def self16Rows11 : List (List Jet) := self16Rows10 ++ [self16Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows11_correct : jetRows 1 true 16 11 = self16Rows11 := by
  rw [jetRows, self16Rows10_correct]
  change self16Rows10 ++ [jetStep 1 true 16 11 self16Rows10] = self16Rows10 ++ [self16Row11]
  congr 1
  decide +kernel
def self16Row12 : List Jet := [[(1853925597368/43762690125),(-83377205494619/700203042000)],[(286468105155011/128037127680000),(53231244794396237/1792519787520000)],[(-636579102289/4073908608000),(-11747362961713/64018563840000)],[(-287760921131/149376648960000),(-219403614853/9053130240000)],[(348529327/10669760640000),(-2754707/77598259200)],[(144437/311201352000),(152003/63510480000)],[(1/479001600),(1/79833600)]]
def self16Rows12 : List (List Jet) := self16Rows11 ++ [self16Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Rows12_correct : jetRows 1 true 16 12 = self16Rows12 := by
  rw [jetRows, self16Rows11_correct]
  change self16Rows11 ++ [jetStep 1 true 16 12 self16Rows11] = self16Rows11 ++ [self16Row12]
  congr 1
  decide +kernel
def self16Coeffs : List Jet := [[(149497506859376/218813450625),(1230908346568771/218813450625)],[(-4465071145955699/64018563840000),(4934015325495251/25607425536000)],[(-17071919961983/7468832448000),(-151845801156613/6224027040000)],[(15886574731/266744016000),(-127504492631/592764480000)],[(74410657/53045685000),(19399565747/2334010140000)],[(51449/12966723000),(1325651/14407470000)],[(-4/108056025),(2/12006225)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self16Coeffs_correct : widthCoefficients 1 true 16 = self16Coeffs := by
  rw [widthCoefficients,self16Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
