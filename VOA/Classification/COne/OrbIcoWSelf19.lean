import VOA.Classification.COne.OrbIcoWSelf18

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self19Rows00 := jetRows 1 true 19 0
theorem self19Rows00_correct : jetRows 1 true 19 0 = self19Rows00 := rfl
def self19Row01 : List Jet := [[(-1/6),(-11/3)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self19Rows01 : List (List Jet) := self19Rows00 ++ [self19Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows01_correct : jetRows 1 true 19 1 = self19Rows01 := by
  rw [jetRows, self19Rows00_correct]
  change self19Rows00 ++ [jetStep 1 true 19 1 self19Rows00] = self19Rows00 ++ [self19Row01]
  congr 1
  decide +kernel
def self19Row02 : List Jet := [[(-203/132),(365/132)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self19Rows02 : List (List Jet) := self19Rows01 ++ [self19Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows02_correct : jetRows 1 true 19 2 = self19Rows02 := by
  rw [jetRows, self19Rows01_correct]
  change self19Rows01 ++ [jetStep 1 true 19 2 self19Rows01] = self19Rows01 ++ [self19Row02]
  congr 1
  decide +kernel
def self19Row03 : List Jet := [[(91/36),(4249/990)],[(17/1980),(391/1980)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self19Rows03 : List (List Jet) := self19Rows02 ++ [self19Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows03_correct : jetRows 1 true 19 3 = self19Rows03 := by
  rw [jetRows, self19Rows02_correct]
  change self19Rows02 ++ [jetStep 1 true 19 3 self19Rows02] = self19Rows02 ++ [self19Row03]
  congr 1
  decide +kernel
def self19Row04 : List Jet := [[(-23737/14256),(-33871/2640)],[(761/8910),(-104/1485)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def self19Rows04 : List (List Jet) := self19Rows03 ++ [self19Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows04_correct : jetRows 1 true 19 4 = self19Rows04 := by
  rw [jetRows, self19Rows03_correct]
  change self19Rows03 ++ [jetStep 1 true 19 4 self19Rows03] = self19Rows03 ++ [self19Row04]
  congr 1
  decide +kernel
def self19Row05 : List Jet := [[(-68075/57024),(4257197/285120)],[(-119/792),(-104153/237600)],[(-1/3600),(-1/150)],[0,0],[0,0],[0,0],[0,0]]
def self19Rows05 : List (List Jet) := self19Rows04 ++ [self19Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows05_correct : jetRows 1 true 19 5 = self19Rows05 := by
  rw [jetRows, self19Rows04_correct]
  change self19Rows04 ++ [jetStep 1 true 19 5 self19Rows04] = self19Rows04 ++ [self19Row05]
  congr 1
  decide +kernel
def self19Row06 : List Jet := [[(1698305/342144),(-755779/213840)],[(275699/2993760),(30212981/29937600)],[(-45641/14968800),(-6947/14968800)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def self19Rows06 : List (List Jet) := self19Rows05 ++ [self19Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows06_correct : jetRows 1 true 19 6 = self19Rows06 := by
  rw [jetRows, self19Rows05_correct]
  change self19Rows05 ++ [jetStep 1 true 19 6 self19Rows05] = self19Rows05 ++ [self19Row06]
  congr 1
  decide +kernel
def self19Row07 : List Jet := [[(-7574825/1026432),(-818118713/35925120)],[(34210199/251475840),(-596801591/628689600)],[(281/47520),(743059/29937600)],[(281/34927200),(281/1397088)],[0,0],[0,0],[0,0]]
def self19Rows07 : List (List Jet) := self19Rows06 ++ [self19Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows07_correct : jetRows 1 true 19 7 = self19Rows07 := by
  rw [jetRows, self19Rows06_correct]
  change self19Rows06 ++ [jetStep 1 true 19 7 self19Rows06] = self19Rows06 ++ [self19Row07]
  congr 1
  decide +kernel
def self19Row08 : List Jet := [[(44277493/8211456),(868114627/15966720)],[(-52891117/111767040),(-3452597/6096384)],[(-972761/299376000),(-10458263/199584000)],[(2419/23814000),(14831/130977000)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def self19Rows08 : List (List Jet) := self19Rows07 ++ [self19Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows08_correct : jetRows 1 true 19 8 = self19Rows08 := by
  rw [jetRows, self19Rows07_correct]
  change self19Rows07 ++ [jetStep 1 true 19 8 self19Rows07] = self19Rows07 ++ [self19Row08]
  congr 1
  decide +kernel
def self19Row09 : List Jet := [[(573581659/147806208),(-3979687589/61585920)],[(6138150607/9053130240),(307621673/78382080)],[(-2337761357/226328256000),(680210033/18860688000)],[(-4141/17962560),(-989543/769824000)],[(-667/2514758400),(-8671/1257379200)],[0,0],[0,0]]
def self19Rows09 : List (List Jet) := self19Rows08 ++ [self19Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows09_correct : jetRows 1 true 19 9 = self19Rows09 := by
  rw [jetRows, self19Rows08_correct]
  change self19Rows08 ++ [jetStep 1 true 19 9 self19Rows08] = self19Rows08 ++ [self19Row09]
  congr 1
  decide +kernel
def self19Row10 : List Jet := [[(-18614489803/886837248),(14307781303/4434186240)],[(-25171307863/108637562880),(-2109422118211/271593907200)],[(40068164057/1131641280000),(261575404787/2263282560000)],[(3922727/37721376000),(147712513/51438240000)],[(-1595197/377213760000),(-1094531/125737920000)],[(-1/39916800),(-1/7983360)],[0,0]]
def self19Rows10 : List (List Jet) := self19Rows09 ++ [self19Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows10_correct : jetRows 1 true 19 10 = self19Rows10 := by
  rw [jetRows, self19Rows09_correct]
  change self19Rows09 ++ [jetStep 1 true 19 10 self19Rows09] = self19Rows09 ++ [self19Row10]
  congr 1
  decide +kernel
def self19Row11 : List Jet := [[(372128311373/9755209728),(2568297563993/12194012160)],[(-485251996619/265558487040),(6949633087357/1327792435200)],[(-419094766/8104201875),(-26424956973859/49792216320000)],[(4809658793/4979221632000),(-6243771631/8298702720000)],[(21011/1580705280),(56320171/592764480000)],[(793/55324684800),(793/2049062400)],[0,0]]
def self19Rows11 : List (List Jet) := self19Rows10 ++ [self19Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows11_correct : jetRows 1 true 19 11 = self19Rows11 := by
  rw [jetRows, self19Rows10_correct]
  change self19Rows10 ++ [jetStep 1 true 19 11 self19Rows10] = self19Rows10 ++ [self19Row11]
  congr 1
  decide +kernel
def self19Row12 : List Jet := [[(-1148446403741/117062516736),(-401424880510259/585312583680)],[(7626573332419/1024297021440),(90210264685319/2560742553600)],[(-24782372828359/358503957504000),(8451765527969/7170079150080)],[(-205424763857/42679042560000),(-771662351791/27159390720000)],[(-153348133/49792216320000),(-12641990201/37344162240000)],[(2627749/6224027040000),(55337/44457336000)],[(1/479001600),(1/79833600)]]
def self19Rows12 : List (List Jet) := self19Rows11 ++ [self19Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Rows12_correct : jetRows 1 true 19 12 = self19Rows12 := by
  rw [jetRows, self19Rows11_correct]
  change self19Rows11 ++ [jetStep 1 true 19 12 self19Rows11] = self19Rows11 ++ [self19Row12]
  congr 1
  decide +kernel
def self19Coeffs : List Jet := [[(101366598717475/58531258368),(-8694100199057/29265629184)],[(9316333445465/358503957504),(8297635920536939/7170079150080)],[(-418087828222483/74688324480000),(-90925449202751/6789847680000)],[(-160421199157/4668020280000),(-36634995391601/37344162240000)],[(1270708231/778003380000),(247550741/186720811200)],[(16/1029105),(2421031/18523890000)],[(2/108056025),(2/4002075)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self19Coeffs_correct : widthCoefficients 1 true 19 = self19Coeffs := by
  rw [widthCoefficients,self19Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
