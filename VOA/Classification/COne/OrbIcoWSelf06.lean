import VOA.Classification.COne.OrbIcoWSelf05

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self06Rows00 := jetRows 2 true 6 0
theorem self06Rows00_correct : jetRows 2 true 6 0 = self06Rows00 := rfl
def self06Row01 : List Jet := [[2,(-3/2),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self06Rows01 : List (List Jet) := self06Rows00 ++ [self06Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows01_correct : jetRows 2 true 6 1 = self06Rows01 := by
  rw [jetRows, self06Rows00_correct]
  change self06Rows00 ++ [jetStep 2 true 6 1 self06Rows00] = self06Rows00 ++ [self06Row01]
  congr 1
  decide +kernel
def self06Row02 : List Jet := [[(-5/11),(-95/44),(51/44)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self06Rows02 : List (List Jet) := self06Rows01 ++ [self06Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows02_correct : jetRows 2 true 6 2 = self06Rows02 := by
  rw [jetRows, self06Rows01_correct]
  change self06Rows01 ++ [jetStep 2 true 6 2 self06Rows01] = self06Rows01 ++ [self06Row02]
  congr 1
  decide +kernel
def self06Row03 : List Jet := [[(-208/165),(43/22),(166/165)],[(-17/165),(-17/660),(17/220)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self06Rows03 : List (List Jet) := self06Rows02 ++ [self06Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows03_correct : jetRows 2 true 6 3 = self06Rows03 := by
  rw [jetRows, self06Rows02_correct]
  change self06Rows02 ++ [jetStep 2 true 6 3 self06Rows02] = self06Rows02 ++ [self06Row03]
  congr 1
  decide +kernel
def self06Row04 : List Jet := [[(772/495),(617/792),(-4291/1980)],[(5/297),(221/1485),(94/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self06Rows04 : List (List Jet) := self06Rows03 ++ [self06Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows04_correct : jetRows 2 true 6 4 = self06Rows04 := by
  rw [jetRows, self06Rows03_correct]
  change self06Rows03 ++ [jetStep 2 true 6 4 self06Rows03] = self06Rows03 ++ [self06Row04]
  congr 1
  decide +kernel
def self06Row05 : List Jet := [[(-1204/2475),(-4991/1650),(54691/79200)],[(215/2376),(-589/26400),(-3781/19800)],[(1/300),(1/240),(-1/600)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self06Rows05 : List (List Jet) := self06Rows04 ++ [self06Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows05_correct : jetRows 2 true 6 5 = self06Rows05 := by
  rw [jetRows, self06Rows04_correct]
  change self06Rows04 ++ [jetStep 2 true 6 5 self06Rows04] = self06Rows04 ++ [self06Row05]
  congr 1
  decide +kernel
def self06Row06 : List Jet := [[(-54218/51975),(140873/51975),(7383703/3326400)],[(-49351/498960),(-657509/3326400),(199777/3326400)],[(-1/4536),(-9479/1663200),(-299/36960)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self06Rows06 : List (List Jet) := self06Rows05 ++ [self06Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows06_correct : jetRows 2 true 6 6 = self06Rows06 := by
  rw [jetRows, self06Rows05_correct]
  change self06Rows05 ++ [jetStep 2 true 6 6 self06Rows05] = self06Rows05 ++ [self06Row06]
  congr 1
  decide +kernel
def self06Row07 : List Jet := [[(137204/72765),(5419/19404),(-15123263/3880800)],[(-47617/7484400),(7750139/29937600),(377167/1425600)],[(-222463/52390800),(-185399/41912640),(560627/69854400)],[(-281/2910600),(-281/1293600),(-281/3880800)],[0,0,0],[0,0,0],[0,0,0]]
def self06Rows07 : List (List Jet) := self06Rows06 ++ [self06Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows07_correct : jetRows 2 true 6 7 = self06Rows07 := by
  rw [jetRows, self06Rows06_correct]
  change self06Rows06 ++ [jetStep 2 true 6 7 self06Rows06] = self06Rows06 ++ [self06Row07]
  congr 1
  decide +kernel
def self06Row08 : List Jet := [[(-4535453/3638250),(-231950093/58212000),(28455697/14112000)],[(43048729/299376000),(-2779979/239500800),(-545210537/1197504000)],[(1349891/349272000),(7089713/465696000),(3829579/349272000)],[(-17/1746360),(1861/10914750),(6883/14553000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self06Rows08 : List (List Jet) := self06Rows07 ++ [self06Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows08_correct : jetRows 2 true 6 8 = self06Rows08 := by
  rw [jetRows, self06Rows07_correct]
  change self06Rows07 ++ [jetStep 2 true 6 8 self06Rows07] = self06Rows07 ++ [self06Row08]
  congr 1
  decide +kernel
def self06Row09 : List Jet := [[(-1190087/1488375),(20925361/4158000),(7265888339/2095632000)],[(-1297363471/7544275200),(-66111332227/150885504000),(3537041441/30177100800)],[(4837673/1347192000),(-46326569/5388768000),(-355582481/10777536000)],[(52363/269438400),(17323021/37721376000),(-5381/342921600)],[(667/209563200),(8671/838252800),(667/69854400)],[0,0,0],[0,0,0]]
def self06Rows09 : List (List Jet) := self06Rows08 ++ [self06Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows09_correct : jetRows 2 true 6 9 = self06Rows09 := by
  rw [jetRows, self06Rows08_correct]
  change self06Rows08 ++ [jetStep 2 true 6 9 self06Rows08] = self06Rows08 ++ [self06Row09]
  congr 1
  decide +kernel
def self06Row10 : List Jet := [[(42683849/14883750),(-255131699/873180000),(-176938597841/20956320000)],[(-7886239309/226328256000),(34948473083/55883520000),(79530625037/94303440000)],[(-1403561813/113164128000),(-3919640279/150885504000),(2212912157/150885504000)],[(-595613/5239080000),(-175016231/188606880000),(-12860263/7544275200)],[(1853/1257379200),(-497129/125737920000),(-3265063/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self06Rows10 : List (List Jet) := self06Rows09 ++ [self06Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows10_correct : jetRows 2 true 6 10 = self06Rows10 := by
  rw [jetRows, self06Rows09_correct]
  change self06Rows09 ++ [jetStep 2 true 6 10 self06Rows09] = self06Rows09 ++ [self06Row10]
  congr 1
  decide +kernel
def self06Row11 : List Jet := [[(-14673776/7441875),(-622785281/65488500),(187412614943/57629880000)],[(97048398109/226328256000),(12960774437203/49792216320000),(-2292642768473/1508855040000)],[(817917433/165974054400),(206098165337/3319481088000),(10471029259/110649369600)],[(-41028179/74095560000),(-3760319/5292540000),(297720461/131725440000)],[(-74911/5927644800),(-67375837/1383117120000),(-66468797/1383117120000)],[(-793/4610390400),(-13481/18441561600),(-793/737662464)],[0,0,0]]
def self06Rows11 : List (List Jet) := self06Rows10 ++ [self06Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows11_correct : jetRows 2 true 6 11 = self06Rows11 := by
  rw [jetRows, self06Rows10_correct]
  change self06Rows10 ++ [jetStep 2 true 6 11 self06Rows10] = self06Rows10 ++ [self06Row11]
  congr 1
  decide +kernel
def self06Row12 : List Jet := [[(-112424/18225),(321222397/37422000),(2536273970107/98794080000)],[(-365630765803/1234517760000),(-152347758702941/54318781440000),(-95849436716981/49792216320000)],[(384285587339/7468832448000),(8038778294023/149376648960000),(-130667095613/592764480000)],[(87024602387/74688324480000),(2074608493931/298753297920000),(961292630833/99584432640000)],[(-37818167/4149351360000),(609789253/9958443264000),(2578075939/8298702720000)],[(-14767/41493513600),(-3503/7056720000),(14149/6174630000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self06Rows12 : List (List Jet) := self06Rows11 ++ [self06Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Rows12_correct : jetRows 2 true 6 12 = self06Rows12 := by
  rw [jetRows, self06Rows11_correct]
  change self06Rows11 ++ [jetStep 2 true 6 12 self06Rows11] = self06Rows11 ++ [self06Row12]
  congr 1
  decide +kernel
def self06Coeffs : List Jet := [[(213380752/7441875),(-31875591358/81860625),(951419380831/4802490000)],[(113022851457907/6789847680000),(880016363622157/59750659584000),(-636890727438529/9053130240000)],[(-42674969419/466802028000),(117128433077377/37344162240000),(56232933528649/16597405440000)],[(-24482679167/622402704000),(-343308905501/12448054080000),(114007704101/553246848000)],[(-8725301/9261945000),(-37871683/10103940000),(-12376027/6735960000)],[(-85/7409556),(-444751/6174630000),(-6161/51030000)],[(-8/36018675),(-34/36018675),(-2/1440747)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self06Coeffs_correct : widthCoefficients 2 true 6 = self06Coeffs := by
  rw [widthCoefficients,self06Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
