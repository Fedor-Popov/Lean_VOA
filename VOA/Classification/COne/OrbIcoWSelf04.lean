import VOA.Classification.COne.OrbIcoWSelf03

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self04Rows00 := jetRows 2 true 4 0
theorem self04Rows00_correct : jetRows 2 true 4 0 = self04Rows00 := rfl
def self04Row01 : List Jet := [[(7/3),(-7/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self04Rows01 : List (List Jet) := self04Rows00 ++ [self04Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows01_correct : jetRows 2 true 4 1 = self04Rows01 := by
  rw [jetRows, self04Rows00_correct]
  change self04Rows00 ++ [jetStep 2 true 4 1 self04Rows00] = self04Rows00 ++ [self04Row01]
  congr 1
  decide +kernel
def self04Row02 : List Jet := [[(1/6),(-265/132),(91/132)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self04Rows02 : List (List Jet) := self04Rows01 ++ [self04Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows02_correct : jetRows 2 true 4 2 = self04Rows02 := by
  rw [jetRows, self04Rows01_correct]
  change self04Rows01 ++ [jetStep 2 true 4 2 self04Rows01] = self04Rows01 ++ [self04Row02]
  congr 1
  decide +kernel
def self04Row03 : List Jet := [[(-14/9),(527/495),(373/495)],[(-119/990),(-119/1980),(119/1980)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self04Rows03 : List (List Jet) := self04Rows02 ++ [self04Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows03_correct : jetRows 2 true 4 3 = self04Rows03 := by
  rw [jetRows, self04Rows02_correct]
  change self04Rows02 ++ [jetStep 2 true 4 3 self04Rows02] = self04Rows02 ++ [self04Row03]
  congr 1
  decide +kernel
def self04Row04 : List Jet := [[(91/81),(6839/5940),(-13471/11880)],[(-92/4455),(151/1485),(11/135)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self04Rows04 : List (List Jet) := self04Rows03 ++ [self04Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows04_correct : jetRows 2 true 4 4 = self04Rows04 := by
  rw [jetRows, self04Rows03_correct]
  change self04Rows03 ++ [jetStep 2 true 4 4 self04Rows03] = self04Rows03 ++ [self04Row04]
  congr 1
  decide +kernel
def self04Row05 : List Jet := [[(77/324),(-15463/7128),(85/1584)],[(227/2160),(12167/237600),(-92/825)],[(7/1800),(7/1200),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self04Rows05 : List (List Jet) := self04Rows04 ++ [self04Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows05_correct : jetRows 2 true 4 5 = self04Rows05 := by
  rw [jetRows, self04Rows04_correct]
  change self04Rows04 ++ [jetStep 2 true 4 5 self04Rows04] = self04Rows04 ++ [self04Row05]
  congr 1
  decide +kernel
def self04Row06 : List Jet := [[(-2597/1944),(50173/42768),(16941/12320)],[(-35087/598752),(-5177839/29937600),(-348553/9979200)],[(9377/7484400),(-35207/14968800),(-34369/4989600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self04Rows06 : List (List Jet) := self04Rows05 ++ [self04Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows06_correct : jetRows 2 true 4 6 = self04Rows06 := by
  rw [jetRows, self04Rows05_correct]
  change self04Rows05 ++ [jetStep 2 true 4 6 self04Rows05] = self04Rows05 ++ [self04Row06]
  congr 1
  decide +kernel
def self04Row07 : List Jet := [[(982/729),(238423/224532),(-5533865/3143448)],[(-781661/12573792),(69197629/628689600),(64145647/314344800)],[(-96809/20956320),(-181553/23284800),(266081/209563200)],[(-281/2494800),(-281/997920),(-281/1663200)],[0,0,0],[0,0,0],[0,0,0]]
def self04Rows07 : List (List Jet) := self04Rows06 ++ [self04Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows07_correct : jetRows 2 true 4 7 = self04Rows07 := by
  rw [jetRows, self04Rows06_correct]
  change self04Rows06 ++ [jetStep 2 true 4 7 self04Rows06] = self04Rows06 ++ [self04Row07]
  congr 1
  decide +kernel
def self04Row08 : List Jet := [[(-2107/11664),(-236095/85536),(11959207/29937600)],[(4696907/33530112),(18623389/152409600),(-311559077/1676505600)],[(2816783/2095632000),(4742653/465696000),(8881079/698544000)],[(-607/9355500),(-101/9355500),(509/1701000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self04Rows08 : List (List Jet) := self04Rows07 ++ [self04Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows08_correct : jetRows 2 true 4 8 = self04Rows08 := by
  rw [jetRows, self04Rows07_correct]
  change self04Rows07 ++ [jetStep 2 true 4 8 self04Rows07] = self04Rows07 ++ [self04Row08]
  congr 1
  decide +kernel
def self04Row09 : List Jet := [[(-145727/104976),(2826281/1347192),(21915311/10716300)],[(-18387349/258660864),(-9773800357/30177100800),(-393433309/3353011200)],[(25470383/4041576000),(153184501/37721376000),(-1196278891/75442752000)],[(732223/3772137600),(21791653/37721376000),(1911193/4715172000)],[(667/179625600),(667/51321600),(667/44906400)],[0,0,0],[0,0,0]]
def self04Rows09 : List (List Jet) := self04Rows08 ++ [self04Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows09_correct : jetRows 2 true 4 9 = self04Rows09 := by
  rw [jetRows, self04Rows08_correct]
  change self04Rows08 ++ [jetStep 2 true 4 9 self04Rows08] = self04Rows08 ++ [self04Row09]
  congr 1
  decide +kernel
def self04Row10 : List Jet := [[(1171793/629856),(10143571/6928416),(-66042673/20207880)],[(-20837333/141087744),(1259137913/7054387200),(16574900131/32332608000)],[(-9885684923/1131641280000),(-6664851527/251475840000),(-9430372157/754427520000)],[(629203/11316412800),(-198618197/565820640000),(-234350713/188606880000)],[(111787/26943840000),(19411/2566080000),(-152759/17962560000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self04Rows10 : List (List Jet) := self04Rows09 ++ [self04Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows10_correct : jetRows 2 true 4 10 = self04Rows10 := by
  rw [jetRows, self04Rows09_correct]
  change self04Rows09 ++ [jetStep 2 true 4 10 self04Rows09] = self04Rows09 ++ [self04Row10]
  congr 1
  decide +kernel
def self04Row11 : List Jet := [[(602903/1732104),(-24783313/4763286),(-946625/6062364)],[(243038035/812934144),(93988764893/181062604800),(-3364062457031/9958443264000)],[(-26765122141/3556586880000),(914818988131/49792216320000),(105441622421/1659740544000)],[(-261904303/414935136000),(-10294037837/6224027040000),(-9820306151/24896108160000)],[(-4448363/414935136000),(-205166743/4149351360000),(-35095033/461039040000)],[(-793/3951763200),(-793/878169600),(-793/526901760)],[0,0,0]]
def self04Rows11 : List (List Jet) := self04Rows10 ++ [self04Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows11_correct : jetRows 2 true 4 11 = self04Rows11 := by
  rw [jetRows, self04Rows10_correct]
  change self04Rows10 ++ [jetStep 2 true 4 11 self04Rows10] = self04Rows10 ++ [self04Row11]
  congr 1
  decide +kernel
def self04Row12 : List Jet := [[(-5827661/1299078),(-468782059/457275456),(147811404959/16004640960)],[(58633904381/204859404288),(-1498187531287/1463281459200),(-294735088308557/179251978752000)],[(53034673577/1280371276800),(1333456716187/12803712768000),(20252613287/32009281920000)],[(-609271/45722880000),(960262922939/298753297920000),(2553630756563/298753297920000)],[(-2420762497/74688324480000),(-420281879/7113173760000),(25192063/266744016000)],[(-2767/3969405000),(-205811/88914672000),(-215353/148191120000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self04Rows12 : List (List Jet) := self04Rows11 ++ [self04Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Rows12_correct : jetRows 2 true 4 12 = self04Rows12 := by
  rw [jetRows, self04Rows11_correct]
  change self04Rows11 ++ [jetStep 2 true 4 12 self04Rows11] = self04Rows11 ++ [self04Row12]
  congr 1
  decide +kernel
def self04Coeffs : List Jet := [[(37030525/472392),(-110980072/649539),(38506059689/1143188640)],[(72460809361/14632814592),(24206865555671/1024297021440),(-614694208392001/35850395750400)],[(-1311751889759/1778293440000),(848457742589/1333720080000),(385837768319063/149376648960000)],[(-17811820963/518668920000),(-3376515013321/37344162240000),(592325864563/74688324480000)],[(-51937937/145875633750),(-464961983/155600676000),(-22934894933/4668020280000)],[(-4493/12966723000),(-5413873/129667230000),(-1827863/14407470000)],[(-4/15436575),(-2/1715175),(-2/1029105)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self04Coeffs_correct : widthCoefficients 2 true 4 = self04Coeffs := by
  rw [widthCoefficients,self04Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
