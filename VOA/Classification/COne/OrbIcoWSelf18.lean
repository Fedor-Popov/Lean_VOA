import VOA.Classification.COne.OrbIcoWSelf17

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self18Rows00 := jetRows 1 true 18 0
theorem self18Rows00_correct : jetRows 1 true 18 0 = self18Rows00 := rfl
def self18Row01 : List Jet := [[0,(-7/2)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self18Rows01 : List (List Jet) := self18Rows00 ++ [self18Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows01_correct : jetRows 1 true 18 1 = self18Rows01 := by
  rw [jetRows, self18Rows00_correct]
  change self18Rows00 ++ [jetStep 1 true 18 1 self18Rows00] = self18Rows00 ++ [self18Row01]
  congr 1
  decide +kernel
def self18Row02 : List Jet := [[(-18/11),(89/44)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self18Rows02 : List (List Jet) := self18Rows01 ++ [self18Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows02_correct : jetRows 1 true 18 2 = self18Rows02 := by
  rw [jetRows, self18Rows01_correct]
  change self18Rows01 ++ [jetStep 1 true 18 2 self18Rows01] = self18Rows01 ++ [self18Row02]
  congr 1
  decide +kernel
def self18Row03 : List Jet := [[(126/55),(29/6)],[0,(119/660)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self18Rows03 : List (List Jet) := self18Rows02 ++ [self18Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows03_correct : jetRows 1 true 18 3 = self18Rows03 := by
  rw [jetRows, self18Rows02_correct]
  change self18Rows02 ++ [jetStep 1 true 18 3 self18Rows02] = self18Rows02 ++ [self18Row03]
  congr 1
  decide +kernel
def self18Row04 : List Jet := [[(-119/110),(-15491/1320)],[(1/11),(-31/1485)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def self18Rows04 : List (List Jet) := self18Rows03 ++ [self18Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows04_correct : jetRows 1 true 18 4 = self18Rows04 := by
  rw [jetRows, self18Rows03_correct]
  change self18Rows03 ++ [jetStep 1 true 18 4 self18Rows03] = self18Rows03 ++ [self18Row04]
  congr 1
  decide +kernel
def self18Row05 : List Jet := [[(-973/550),(3787/330)],[(-37/275),(-108653/237600)],[0,(-7/1200)],[0,0],[0,0],[0,0],[0,0]]
def self18Rows05 : List (List Jet) := self18Rows04 ++ [self18Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows05_correct : jetRows 1 true 18 5 = self18Rows05 := by
  rw [jetRows, self18Rows04_correct]
  change self18Rows04 ++ [jetStep 1 true 18 5 self18Rows04] = self18Rows04 ++ [self18Row05]
  congr 1
  decide +kernel
def self18Row06 : List Jet := [[(3241/660),(8819/9900)],[(391/7700),(8794013/9979200)],[(-1/308),(-12613/4989600)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def self18Rows06 : List (List Jet) := self18Rows05 ++ [self18Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows06_correct : jetRows 1 true 18 6 = self18Rows06 := by
  rw [jetRows, self18Rows05_correct]
  change self18Rows05 ++ [jetStep 1 true 18 6 self18Rows05] = self18Rows05 ++ [self18Row06]
  congr 1
  decide +kernel
def self18Row07 : List Jet := [[(-3371/550),(-553411/23100)],[(5699/32340),(-25748299/41912640)],[(281/53900),(5219737/209563200)],[0,(281/1663200)],[0,0],[0,0],[0,0]]
def self18Rows07 : List (List Jet) := self18Rows06 ++ [self18Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows07_correct : jetRows 1 true 18 7 = self18Rows07 := by
  rw [jetRows, self18Rows06_correct]
  change self18Rows06 ++ [jetStep 1 true 18 7 self18Rows06] = self18Rows06 ++ [self18Row07]
  congr 1
  decide +kernel
def self18Row08 : List Jet := [[(65107/22000),(48781/1056)],[(-96857/215600),(-7800259657/8382528000)],[(-1297/1078000),(-20219431/465696000)],[(1/9240),(151/779625)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def self18Rows08 : List (List Jet) := self18Rows07 ++ [self18Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows08_correct : jetRows 1 true 18 8 = self18Rows08 := by
  rw [jetRows, self18Rows07_correct]
  change self18Rows07 ++ [jetStep 1 true 18 8 self18Rows07] = self18Rows07 ++ [self18Row08]
  congr 1
  decide +kernel
def self18Row09 : List Jet := [[(27761/4500),(-357563359/8316000)],[(852707/1663200),(50749645579/13716864000)],[(-51143/4158000),(493801393/37721376000)],[(-193/970200),(-47344547/37721376000)],[0,(-667/119750400)],[0,0],[0,0]]
def self18Rows09 : List (List Jet) := self18Rows08 ++ [self18Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows09_correct : jetRows 1 true 18 9 = self18Rows09 := by
  rw [jetRows, self18Rows08_correct]
  change self18Rows08 ++ [jetStep 1 true 18 9 self18Rows08] = self18Rows08 ++ [self18Row09]
  congr 1
  decide +kernel
def self18Row10 : List Jet := [[(-135184/6875),(-18977153/792000)],[(1897829/22680000),(-3763484582827/646652160000)],[(556939/17463600),(12271755931/90531302400)],[(-839/97020000),(418091417/188606880000)],[(-1/221760),(-227303/17962560000)],[(-1/39916800),(-1/7983360)],[0,0]]
def self18Rows10 : List (List Jet) := self18Rows09 ++ [self18Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows10_correct : jetRows 1 true 18 10 = self18Rows10 := by
  rw [jetRows, self18Rows09_correct]
  change self18Rows09 ++ [jetStep 1 true 18 10 self18Rows09] = self18Rows09 ++ [self18Row10]
  congr 1
  decide +kernel
def self18Row11 : List Jet := [[(3269763/121000),(4325824787/21780000)],[(-5443031219/2744280000),(29523559471067/49792216320000)],[(-272633/8712000),(-45624721999/100590336000)],[(3449521/3201660000),(3399901/2701400625)],[(947/85377600),(375527497/4149351360000)],[0,(793/2634508800)],[0,0]]
def self18Rows11 : List (List Jet) := self18Rows10 ++ [self18Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows11_correct : jetRows 1 true 18 11 = self18Rows11 := by
  rw [jetRows, self18Rows10_correct]
  change self18Rows10 ++ [jetStep 1 true 18 11 self18Rows10] = self18Rows10 ++ [self18Row11]
  congr 1
  decide +kernel
def self18Row12 : List Jet := [[(11515987/660000),(-120637844179/261360000)],[(37833454399/6586272000),(637397981650439/17071617024000)],[(-1942160347/16465680000),(13299039077561/21339521280000)],[(-91384739/23051952000),(-1745288840497/59750659584000)],[(281983/25613280000),(-21415873/92378880000)],[(1/2217600),(256513/148191120000)],[(1/479001600),(1/79833600)]]
def self18Rows12 : List (List Jet) := self18Rows11 ++ [self18Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Rows12_correct : jetRows 1 true 18 12 = self18Rows12 := by
  rw [jetRows, self18Rows11_correct]
  change self18Rows11 ++ [jetStep 1 true 18 12 self18Rows11] = self18Rows11 ++ [self18Row12]
  congr 1
  decide +kernel
def self18Coeffs : List Jet := [[(447535081/302500),(3190339817/907500)],[(-10773881111/470448000),(4917207171168997/6097006080000)],[(-1407400013/294030000),(-117060628549951/5334880320000)],[(7125373/1200622500),(-9006185628037/12448054080000)],[(169231/100051875),(3681659981/778003380000)],[(16/1334025),(15946417/129667230000)],[0,(2/5145525)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self18Coeffs_correct : widthCoefficients 1 true 18 = self18Coeffs := by
  rw [widthCoefficients,self18Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
