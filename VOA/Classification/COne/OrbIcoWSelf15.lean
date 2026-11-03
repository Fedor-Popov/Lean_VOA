import VOA.Classification.COne.OrbIcoWSelf14

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self15Rows00 := jetRows 1 true 15 0
theorem self15Rows00_correct : jetRows 1 true 15 0 = self15Rows00 := rfl
def self15Row01 : List Jet := [[(1/2),-3],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self15Rows01 : List (List Jet) := self15Rows00 ++ [self15Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows01_correct : jetRows 1 true 15 1 = self15Rows01 := by
  rw [jetRows, self15Rows00_correct]
  change self15Rows00 ++ [jetStep 1 true 15 1 self15Rows00] = self15Rows00 ++ [self15Row01]
  congr 1
  decide +kernel
def self15Row02 : List Jet := [[(-7/4),(7/44)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self15Rows02 : List (List Jet) := self15Rows01 ++ [self15Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows02_correct : jetRows 1 true 15 2 = self15Rows02 := by
  rw [jetRows, self15Rows01_correct]
  change self15Rows01 ++ [jetStep 1 true 15 2 self15Rows01] = self15Rows01 ++ [self15Row02]
  congr 1
  decide +kernel
def self15Row03 : List Jet := [[(17/12),(119/22)],[(-17/660),(17/132)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def self15Rows03 : List (List Jet) := self15Rows02 ++ [self15Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows03_correct : jetRows 1 true 15 3 = self15Rows03 := by
  rw [jetRows, self15Rows02_correct]
  change self15Rows02 ++ [jetStep 1 true 15 3 self15Rows02] = self15Rows02 ++ [self15Row03]
  congr 1
  decide +kernel
def self15Row04 : List Jet := [[(61/144),(-12389/1584)],[(287/2970),(28/297)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def self15Rows04 : List (List Jet) := self15Rows03 ++ [self15Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows04_correct : jetRows 1 true 15 4 = self15Rows04 := by
  rw [jetRows, self15Rows03_correct]
  change self15Rows03 ++ [jetStep 1 true 15 4 self15Rows03] = self15Rows03 ++ [self15Row04]
  congr 1
  decide +kernel
def self15Row05 : List Jet := [[(-1541/576),(32947/10560)],[(-52/675),(-34283/79200)],[(1/1200),(-1/300)],[0,0],[0,0],[0,0],[0,0]]
def self15Rows05 : List (List Jet) := self15Rows04 ++ [self15Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows05_correct : jetRows 1 true 15 5 = self15Rows05 := by
  rw [jetRows, self15Rows04_correct]
  change self15Rows04 ++ [jetStep 1 true 15 5 self15Rows04] = self15Rows04 ++ [self15Row05]
  congr 1
  decide +kernel
def self15Row06 : List Jet := [[(91201/24192),(676301/83160)],[(-263953/4989600),(524659/1108800)],[(-2441/712800),(-559/79200)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def self15Rows06 : List (List Jet) := self15Rows05 ++ [self15Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows06_correct : jetRows 1 true 15 6 = self15Rows06 := by
  rw [jetRows, self15Rows05_correct]
  change self15Rows05 ++ [jetStep 1 true 15 6 self15Rows05] = self15Rows05 ++ [self15Row06]
  congr 1
  decide +kernel
def self15Row07 : List Jet := [[(-393257/169344),(-61690199/3104640)],[(3787141/16765056),(5273803/41912640)],[(40021/14968800),(629927/29937600)],[(-281/11642400),(281/3880800)],[0,0],[0,0],[0,0]]
def self15Rows07 : List (List Jet) := self15Rows06 ++ [self15Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows07_correct : jetRows 1 true 15 7 = self15Rows07 := by
  rw [jetRows, self15Rows06_correct]
  change self15Rows06 ++ [jetStep 1 true 15 7 self15Rows06] = self15Rows06 ++ [self15Row07]
  congr 1
  decide +kernel
def self15Row08 : List Jet := [[(-2842723/1354752),(792534307/37255680)],[(-2459409707/8382528000),(-997955417/762048000)],[(373063/99792000),(-158659/9504000)],[(1409/12474000),(2239/6237000)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def self15Rows08 : List (List Jet) := self15Rows07 ++ [self15Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows08_correct : jetRows 1 true 15 8 = self15Rows08 := by
  rw [jetRows, self15Rows07_correct]
  change self15Rows07 ++ [jetStep 1 true 15 8 self15Rows07] = self15Rows07 ++ [self15Row08]
  congr 1
  decide +kernel
def self15Row09 : List Jet := [[(28008097/3483648),(-6701/887040)],[(4765184519/75442752000),(342501374513/150885504000)],[(-205047259/15088550400),(-606406819/18860688000)],[(-403019/4715172000),(-36022103/37721376000)],[(667/838252800),(-667/419126400)],[0,0],[0,0]]
def self15Rows09 : List (List Jet) := self15Rows08 ++ [self15Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows09_correct : jetRows 1 true 15 9 = self15Rows09 := by
  rw [jetRows, self15Rows08_correct]
  change self15Rows08 ++ [jetStep 1 true 15 9 self15Rows08] = self15Rows08 ++ [self15Row09]
  congr 1
  decide +kernel
def self15Row10 : List Jet := [[(-533516789/48771072),(-14796953449/298045440)],[(247229074577/411505920000),(-72233201281/68584320000)],[(3596645027/226328256000),(32410096319/251475840000)],[(-2382221/8981280000),(71777113/188606880000)],[(-83197/17962560000),(-51803/2566080000)],[(-1/39916800),(-1/7983360)],[0,0]]
def self15Rows10 : List (List Jet) := self15Rows09 ++ [self15Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows10_correct : jetRows 1 true 15 10 = self15Rows10 := by
  rw [jetRows, self15Rows09_correct]
  change self15Rows09 ++ [jetStep 1 true 15 10 self15Rows09] = self15Rows09 ++ [self15Row10]
  congr 1
  decide +kernel
def self15Row11 : List Jet := [[(562138655/536481792),(192837083861/1844156160)],[(-21264489987871/14226347520000),(-1504265038033/258660864000)],[(2745514927/165974054400),(-2897639704361/16597405440000)],[(1666235171/1659740544000),(37671143249/8298702720000)],[(13735487/4149351360000),(5598977/92207808000)],[(-793/18441561600),(793/18441561600)],[0,0]]
def self15Rows11 : List (List Jet) := self15Rows10 ++ [self15Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows11_correct : jetRows 1 true 15 11 = self15Rows11 := by
  rw [jetRows, self15Rows10_correct]
  change self15Rows10 ++ [jetStep 1 true 15 11 self15Rows10] = self15Rows10 ++ [self15Row11]
  congr 1
  decide +kernel
def self15Row12 : List Jet := [[(278256490265/6437781504),(-162151413301/13113999360)],[(45130196089511/59750659584000),(49064091750029/2133952128000)],[(-89857299671177/597506595840000),(-124961793487873/298753297920000)],[(-24276021353/27159390720000),(-838178030803/42679042560000)],[(219460127/5532468480000),(18142723/389001690000)],[(132949/296382240000),(63463/24698520000)],[(1/479001600),(1/79833600)]]
def self15Rows12 : List (List Jet) := self15Rows11 ++ [self15Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Rows12_correct : jetRows 1 true 15 12 = self15Rows12 := by
  rw [jetRows, self15Rows11_correct]
  change self15Rows11 ++ [jetStep 1 true 15 12 self15Rows11] = self15Rows11 ++ [self15Row12]
  congr 1
  decide +kernel
def self15Coeffs : List Jet := [[(29486532725/97542144),(2665237374683/536481792)],[(-2652236728075181/37344162240000),(-4298470056222823/298753297920000)],[(-10557404715469/10669760640000),(-44305094503667/2133952128000)],[(221552591039/3112013520000),(-117872231363/12448054080000)],[(11467823/10373378400),(2681019139/311201352000)],[(-5617/32416807500),(204817/2881494000)],[(-2/36018675),(2/36018675)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self15Coeffs_correct : widthCoefficients 1 true 15 = self15Coeffs := by
  rw [widthCoefficients,self15Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
