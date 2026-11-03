import VOA.Classification.COne.OrbIcoWJets

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self00Rows00 := jetRows 2 true 0 0
theorem self00Rows00_correct : jetRows 2 true 0 0 = self00Rows00 := rfl
def self00Row01 : List Jet := [[3,(-1/2),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self00Rows01 : List (List Jet) := self00Rows00 ++ [self00Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows01_correct : jetRows 2 true 0 1 = self00Rows01 := by
  rw [jetRows, self00Rows00_correct]
  change self00Rows00 ++ [jetStep 2 true 0 1 self00Rows00] = self00Rows00 ++ [self00Row01]
  congr 1
  decide +kernel
def self00Row02 : List Jet := [[(39/22),(-43/44),(5/44)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self00Rows02 : List (List Jet) := self00Rows01 ++ [self00Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows02_correct : jetRows 2 true 0 2 = self00Rows02 := by
  rw [jetRows, self00Rows01_correct]
  change self00Rows01 ++ [jetStep 2 true 0 2 self00Rows01] = self00Rows01 ++ [self00Row02]
  congr 1
  decide +kernel
def self00Row03 : List Jet := [[(-16/11),(8/33),(1/11)],[(-17/110),(-17/132),(17/660)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self00Rows03 : List (List Jet) := self00Rows02 ++ [self00Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows03_correct : jetRows 2 true 0 3 = self00Rows03 := by
  rw [jetRows, self00Rows02_correct]
  change self00Rows02 ++ [jetStep 2 true 0 3 self00Rows02] = self00Rows02 ++ [self00Row03]
  congr 1
  decide +kernel
def self00Row04 : List Jet := [[(-3/22),(41/66),(-151/792)],[(-58/495),(-17/297),(79/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self00Rows04 : List (List Jet) := self00Rows03 ++ [self00Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows04_correct : jetRows 2 true 0 4 = self00Rows04 := by
  rw [jetRows, self00Rows03_correct]
  change self00Rows03 ++ [jetStep 2 true 0 4 self00Rows03] = self00Rows03 ++ [self00Row04]
  congr 1
  decide +kernel
def self00Row05 : List Jet := [[(12/11),(-1007/1320),(31/396)],[(3341/39600),(18511/237600),(-139/9900)],[(1/200),(11/1200),(1/300)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self00Rows05 : List (List Jet) := self00Rows04 ++ [self00Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows05_correct : jetRows 2 true 0 5 = self00Rows05 := by
  rw [jetRows, self00Rows04_correct]
  change self00Rows04 ++ [jetStep 2 true 0 5 self00Rows04] = self00Rows04 ++ [self00Row05]
  congr 1
  decide +kernel
def self00Row06 : List Jet := [[(-10/11),(10873/55440),(24931/166320)],[(71179/1663200),(-12779/907200),(-15971/369600)],[(4183/831600),(38243/4989600),(829/1663200)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self00Rows06 : List (List Jet) := self00Rows05 ++ [self00Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows06_correct : jetRows 2 true 0 6 = self00Rows06 := by
  rw [jetRows, self00Rows05_correct]
  change self00Rows05 ++ [jetStep 2 true 0 6 self00Rows05] = self00Rows05 ++ [self00Row06]
  congr 1
  decide +kernel
def self00Row07 : List Jet := [[0,(877/1540),(-257/840)],[(-66049/635040),(-2176369/41912640),(2710417/52390800)],[(-101341/34927200),(-1273901/209563200),(-634559/209563200)],[(-281/1940400),(-4777/11642400),(-281/776160)],[0,0,0],[0,0,0],[0,0,0]]
def self00Rows07 : List (List Jet) := self00Rows06 ++ [self00Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows07_correct : jetRows 2 true 0 7 = self00Rows07 := by
  rw [jetRows, self00Rows06_correct]
  change self00Rows06 ++ [jetStep 2 true 0 7 self00Rows06] = self00Rows06 ++ [self00Row07]
  congr 1
  decide +kernel
def self00Row08 : List Jet := [[(9/11),(-789/880),(587/2640)],[(59715043/1397088000),(49825753/762048000),(1184131/8382528000)],[(-320161/77616000),(-204401/42336000),(1458053/698544000)],[(-34/165375),(-11471/21829500),(-3077/8731800)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self00Rows08 : List (List Jet) := self00Rows07 ++ [self00Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows08_correct : jetRows 2 true 0 8 = self00Rows08 := by
  rw [jetRows, self00Rows07_correct]
  change self00Rows07 ++ [jetStep 2 true 0 8 self00Rows07] = self00Rows07 ++ [self00Row08]
  congr 1
  decide +kernel
def self00Row09 : List Jet := [[(-9/11),(769/1980),(202/1485)],[(294520069/3592512000),(-332265211/21555072000),(-209576141/3079296000)],[(1852903/314344800),(34861727/3429216000),(161238709/75442752000)],[(421523/6286896000),(9425077/37721376000),(3042983/9430344000)],[(667/139708800),(15341/838252800),(667/26195400)],[0,0,0],[0,0,0]]
def self00Rows09 : List (List Jet) := self00Rows08 ++ [self00Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows09_correct : jetRows 2 true 0 9 = self00Rows09 := by
  rw [jetRows, self00Rows08_correct]
  change self00Rows08 ++ [jetStep 2 true 0 9 self00Rows08] = self00Rows08 ++ [self00Row09]
  congr 1
  decide +kernel
def self00Row10 : List Jet := [[(-3/22),(327/440),(-739/1320)],[(-94047036323/754427520000),(-24487015691/411505920000),(26995753523/377213760000)],[(221914201/75442752000),(121769083/323326080000),(-408576227/68584320000)],[(10999789/31434480000),(159244793/188606880000),(86340131/188606880000)],[(229211/20956320000),(448433/11430720000),(6034907/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self00Rows10 : List (List Jet) := self00Rows09 ++ [self00Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows10_correct : jetRows 2 true 0 10 = self00Rows10 := by
  rw [jetRows, self00Rows09_correct]
  change self00Rows09 ++ [jetStep 2 true 0 10 self00Rows09] = self00Rows09 ++ [self00Row10]
  congr 1
  decide +kernel
def self00Row11 : List Jet := [[(12/11),(-72/55),(29/60)],[(-453066759521/8298702720000),(787987806931/9958443264000),(2630624844521/49792216320000)],[(-119405179/8781696000),(-717375871/37635840000),(88661197/43908480000)],[(-8286671/46103904000),(-465380513/691558560000),(-632963327/754427520000)],[(2553437/691558560000),(5951669/829870272000),(-8183383/1383117120000)],[(-793/3073593600),(-22997/18441561600),(-793/335301120)],[0,0,0]]
def self00Rows11 : List (List Jet) := self00Rows10 ++ [self00Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows11_correct : jetRows 2 true 0 11 = self00Rows11 := by
  rw [jetRows, self00Rows10_correct]
  change self00Rows10 ++ [jetStep 2 true 0 11 self00Rows10] = self00Rows10 ++ [self00Row11]
  congr 1
  decide +kernel
def self00Row12 : List Jet := [[(1/2),(-49/40),(203/180)],[(6045560998129/19916886528000),(1112114646487/23900263833600),(-57714177631597/298753297920000)],[(-288472067783/24896108160000),(-535518489469/149376648960000),(664469712899/37344162240000)],[(-79519987873/49792216320000),(-101486365711/27159390720000),(-538258840877/298753297920000)],[(-8512423/169361280000),(-9213657221/49792216320000),(-2932207057/12448054080000)],[(-269131/172889640000),(-1065737/148191120000),(-13901/1097712000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self00Rows12 : List (List Jet) := self00Rows11 ++ [self00Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Rows12_correct : jetRows 2 true 0 12 = self00Rows12 := by
  rw [jetRows, self00Rows11_correct]
  change self00Rows11 ++ [jetStep 2 true 0 12 self00Rows11] = self00Rows11 ++ [self00Row12]
  congr 1
  decide +kernel
def self00Coeffs : List Jet := [[0,0,0],[(-367845062139733/49792216320000),(2161605824434627/298753297920000),(-37422123747143/11950131916800)],[(-2416772239513/12448054080000),(-668253353143/3734416224000),(9944447303579/149376648960000)],[(3537546779/148191120000),(40698739931/1778293440000),(-1859568233/107775360000)],[(18950971/12966723000),(525393709/155600676000),(2416660349/1556006760000)],[(1009607/21611205000),(4047839/25933446000),(7066487/43222410000)],[(-4/12006225),(-58/36018675),(-2/654885)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self00Coeffs_correct : widthCoefficients 2 true 0 = self00Coeffs := by
  rw [widthCoefficients,self00Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
