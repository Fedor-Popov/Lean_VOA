import VOA.Classification.COne.OrbIcoWSelf16

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self17Rows00 := jetRows 1 true 17 0
theorem self17Rows00_correct : jetRows 1 true 17 0 = self17Rows00 := rfl
def self17Row01 : List Jet := [[(1/6),(-10/3)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self17Rows01 : List (List Jet) := self17Rows00 ++ [self17Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows01_correct : jetRows 1 true 17 1 = self17Rows01 := by
  rw [jetRows, self17Rows00_correct]
  change self17Rows00 ++ [jetStep 1 true 17 1 self17Rows00] = self17Rows00 ++ [self17Row01]
  congr 1
  decide +kernel
def self17Row02 : List Jet := [[(-75/44),(59/44)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self17Rows02 : List (List Jet) := self17Rows01 ++ [self17Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows02_correct : jetRows 1 true 17 2 = self17Rows02 := by
  rw [jetRows, self17Rows01_correct]
  change self17Rows01 ++ [jetStep 1 true 17 2 self17Rows01] = self17Rows01 ++ [self17Row02]
  congr 1
  decide +kernel
def self17Row03 : List Jet := [[(89/44),(856/165)],[(-17/1980),(323/1980)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self17Rows03 : List (List Jet) := self17Rows02 ++ [self17Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows03_correct : jetRows 1 true 17 3 = self17Rows03 := by
  rw [jetRows, self17Rows02_correct]
  change self17Rows02 ++ [jetStep 1 true 17 3 self17Rows02] = self17Rows02 ++ [self17Row03]
  congr 1
  decide +kernel
def self17Row04 : List Jet := [[(-845/1584),(-49901/4752)],[(281/2970),(34/1485)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def self17Rows04 : List (List Jet) := self17Rows03 ++ [self17Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows04_correct : jetRows 1 true 17 4 = self17Rows04 := by
  rw [jetRows, self17Rows03_correct]
  change self17Rows03 ++ [jetStep 1 true 17 4 self17Rows03] = self17Rows03 ++ [self17Row04]
  congr 1
  decide +kernel
def self17Row05 : List Jet := [[(-23279/10560),(1319111/158400)],[(-13879/118800),(-109669/237600)],[(1/3600),(-1/200)],[0,0],[0,0],[0,0],[0,0]]
def self17Rows05 : List (List Jet) := self17Rows04 ++ [self17Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows05_correct : jetRows 1 true 17 5 = self17Rows05 := by
  rw [jetRows, self17Rows04_correct]
  change self17Rows04 ++ [jetStep 1 true 17 5 self17Rows04] = self17Rows04 ++ [self17Row05]
  congr 1
  decide +kernel
def self17Row06 : List Jet := [[(98627/21120),(336233/79200)],[(221/17820),(1063523/1425600)],[(-1531/453600),(-21529/4989600)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def self17Rows06 : List (List Jet) := self17Rows05 ++ [self17Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows06_correct : jetRows 1 true 17 6 = self17Rows06 := by
  rw [jetRows, self17Rows05_correct]
  change self17Rows05 ++ [jetStep 1 true 17 6 self17Rows05] = self17Rows05 ++ [self17Row06]
  congr 1
  decide +kernel
def self17Row07 : List Jet := [[(-428315/88704),(-31429919/1330560)],[(1358437/6652800),(-3209411/9979200)],[(9277/2095632),(564439/23284800)],[(-281/34927200),(4777/34927200)],[0,0],[0,0],[0,0]]
def self17Rows07 : List (List Jet) := self17Rows06 ++ [self17Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows07_correct : jetRows 1 true 17 7 = self17Rows07 := by
  rw [jetRows, self17Rows06_correct]
  change self17Rows06 ++ [jetStep 1 true 17 7 self17Rows06] = self17Rows06 ++ [self17Row07]
  congr 1
  decide +kernel
def self17Row08 : List Jet := [[(1042429/1182720),(333311969/8870400)],[(-7766221/19008000),(-66426197/57024000)],[(4369/6548850),(-143617823/4191264000)],[(9809/87318000),(761/2910600)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def self17Rows08 : List (List Jet) := self17Rows07 ++ [self17Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows08_correct : jetRows 1 true 17 8 = self17Rows08 := by
  rw [jetRows, self17Rows07_correct]
  change self17Rows07 ++ [jetStep 1 true 17 8 self17Rows07] = self17Rows07 ++ [self17Row08]
  congr 1
  decide +kernel
def self17Row09 : List Jet := [[(324323/43008),(-17706239/709632)],[(104892659/299376000),(23784891191/7185024000)],[(-29021149/2155507200),(-113246171/18860688000)],[(-440707/2694384000),(-44738759/37721376000)],[(667/2514758400),(-667/157172400)],[0,0],[0,0]]
def self17Rows09 : List (List Jet) := self17Rows08 ++ [self17Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows09_correct : jetRows 1 true 17 9 = self17Rows09 := by
  rw [jetRows, self17Rows08_correct]
  change self17Rows08 ++ [jetStep 1 true 17 9 self17Rows08] = self17Rows08 ++ [self17Row09]
  congr 1
  decide +kernel
def self17Row10 : List Jet := [[(-111427663/6451200),(-6156855173/152064000)],[(870698921/2661120000),(-47873725057/11975040000)],[(2199253813/80831520000),(9247117507/64665216000)],[(-2470709/22632825600),(35495939/22632825600)],[(-587197/125737920000),(-1997287/125737920000)],[(-1/39916800),(-1/7983360)],[0,0]]
def self17Rows10 : List (List Jet) := self17Rows09 ++ [self17Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows10_correct : jetRows 1 true 17 10 = self17Rows10 := by
  rw [jetRows, self17Rows09_correct]
  change self17Rows09 ++ [jetStep 1 true 17 10 self17Rows09] = self17Rows09 ++ [self17Row10]
  congr 1
  decide +kernel
def self17Row11 : List Jet := [[(12025113/716800),(3400434581/19712000)],[(-2076069113/1064448000),(-1428525296573/526901760000)],[(-44792930927/3556586880000),(-6017848354957/16597405440000)],[(88219067/79035264000),(1553431283/553246848000)],[(35864833/4149351360000),(344083517/4149351360000)],[(-793/55324684800),(793/3688312320)],[0,0]]
def self17Rows11 : List (List Jet) := self17Rows10 ++ [self17Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows11_correct : jetRows 1 true 17 11 = self17Rows11 := by
  rw [jetRows, self17Rows10_correct]
  change self17Rows10 ++ [jetStep 1 true 17 11 self17Rows10] = self17Rows10 ++ [self17Row11]
  congr 1
  decide +kernel
def self17Row12 : List Jet := [[(3943833/114688),(-76480981757/283852800)],[(5727274397/1451520000),(5022622293191/143700480000)],[(-2499017689111/17071617024000),(467726582207/2845269504000)],[(-126959607827/42679042560000),(-43661101481/1580705280000)],[(688136263/29875329792000),(-214848433/1659740544000)],[(964549/2074675680000),(78313/37047780000)],[(1/479001600),(1/79833600)]]
def self17Rows12 : List (List Jet) := self17Rows11 ++ [self17Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Rows12_correct : jetRows 1 true 17 12 = self17Rows12 := by
  rw [jetRows, self17Rows11_correct]
  change self17Rows11 ++ [jetStep 1 true 17 12 self17Rows11] = self17Rows11 ++ [self17Row12]
  congr 1
  decide +kernel
def self17Coeffs : List Jet := [[(45006837/40960),(53914527379/10137600)],[(-20736455483/380160000),(3951822588187/8363520000)],[(-1101155839519/304850304000),(-12813440241197/508083840000)],[(50264921411/1333720080000),(-816991699499/1778293440000)],[(625130851/389001690000),(199392341/28291032000)],[(523769/64833615000),(14224187/129667230000)],[(-2/108056025),(2/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self17Coeffs_correct : widthCoefficients 1 true 17 = self17Coeffs := by
  rw [widthCoefficients,self17Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
