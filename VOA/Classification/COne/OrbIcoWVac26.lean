import VOA.Classification.COne.OrbIcoWVac25

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac26Rows00 := jetRows 2 false 26 0
theorem vac26Rows00_correct : jetRows 2 false 26 0 = vac26Rows00 := rfl
def vac26Row01 : List Jet := [[(5/3),(-16/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac26Rows01 : List (List Jet) := vac26Rows00 ++ [vac26Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows01_correct : jetRows 2 false 26 1 = vac26Rows01 := by
  rw [jetRows, vac26Rows00_correct]
  change vac26Rows00 ++ [jetStep 2 false 26 1 vac26Rows00] = vac26Rows00 ++ [vac26Row01]
  congr 1
  decide +kernel
def vac26Row02 : List Jet := [[(-21/22),(-147/22),(168/11)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac26Rows02 : List (List Jet) := vac26Rows01 ++ [vac26Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows02_correct : jetRows 2 false 26 2 = vac26Rows02 := by
  rw [jetRows, vac26Rows01_correct]
  change vac26Rows01 ++ [jetStep 2 false 26 2 vac26Rows01] = vac26Rows01 ++ [vac26Row02]
  congr 1
  decide +kernel
def vac26Row03 : List Jet := [[(-4/5),(2807/330),(841/66)],[(-17/198),(17/90),(136/495)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac26Rows03 : List (List Jet) := vac26Rows02 ++ [vac26Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows03_correct : jetRows 2 false 26 3 = vac26Rows03 := by
  rw [jetRows, vac26Rows02_correct]
  change vac26Rows02 ++ [jetStep 2 false 26 3 vac26Rows02] = vac26Rows02 ++ [vac26Row03]
  congr 1
  decide +kernel
def vac26Row04 : List Jet := [[(1759/990),(1853/2376),(-96193/2970)],[(14/297),(1351/2970),(-1477/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac26Rows04 : List (List Jet) := vac26Rows03 ++ [vac26Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows04_correct : jetRows 2 false 26 4 = vac26Rows04 := by
  rw [jetRows, vac26Rows03_correct]
  change vac26Rows03 ++ [jetStep 2 false 26 4 vac26Rows03] = vac26Rows03 ++ [vac26Row04]
  congr 1
  decide +kernel
def vac26Row05 : List Jet := [[(-2099/1650),(-461143/39600),(487163/39600)],[(7571/118800),(-5953/13200),(-58969/39600)],[(1/360),(-1/300),(-3/200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac26Rows05 : List (List Jet) := vac26Rows04 ++ [vac26Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows05_correct : jetRows 2 false 26 5 = vac26Rows05 := by
  rw [jetRows, vac26Rows04_correct]
  change vac26Rows04 ++ [jetStep 2 false 26 5 vac26Rows04] = vac26Rows04 ++ [vac26Row05]
  congr 1
  decide +kernel
def vac26Row06 : List Jet := [[(-337/924),(7684403/554400),(15077323/415800)],[(-619147/4989600),(-22931/69300),(261083/118800)],[(-101/71280),(-2263/118800),(41/39600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac26Rows06 : List (List Jet) := vac26Rows05 ++ [vac26Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows06_correct : jetRows 2 false 26 6 = vac26Rows06 := by
  rw [jetRows, vac26Rows05_correct]
  change vac26Rows05 ++ [jetStep 2 false 26 6 vac26Rows05] = vac26Rows05 ++ [vac26Row06]
  congr 1
  decide +kernel
def vac26Row07 : List Jet := [[(248417/121275),(-1683317/582120),(-2426011943/34927200)],[(15931/258720),(4416149/3880800),(508693/646800)],[(-6979/2138400),(7307/534600),(2849/32400)],[(-281/3492720),(281/17463600),(281/529200)],[0,0,0],[0,0,0],[0,0,0]]
def vac26Rows07 : List (List Jet) := vac26Rows06 ++ [vac26Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows07_correct : jetRows 2 false 26 7 = vac26Rows07 := by
  rw [jetRows, vac26Rows06_correct]
  change vac26Rows06 ++ [jetStep 2 false 26 7 vac26Rows06] = vac26Rows06 ++ [vac26Row07]
  congr 1
  decide +kernel
def vac26Row08 : List Jet := [[(-494156/202125),(-63424351/3880800),(17669257933/465696000)],[(3259811/31046400),(-84806251/93139200),(-7789577/1330560)],[(1705871/299376000),(9272287/299376000),(-11724347/149688000)],[(1/28350),(817/1134000),(559/831600)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac26Rows08 : List (List Jet) := vac26Rows07 ++ [vac26Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows08_correct : jetRows 2 false 26 8 = vac26Rows08 := by
  rw [jetRows, vac26Rows07_correct]
  change vac26Rows07 ++ [jetStep 2 false 26 8 vac26Rows07] = vac26Rows07 ++ [vac26Row08]
  congr 1
  decide +kernel
def vac26Row09 : List Jet := [[(10387/16500),(314649/11000),(1621399049/22176000)],[(-139402261/558835200),(-35697223/38102400),(6661372159/1005903360)],[(-547553/1178793000),(-334105549/4715172000),(-253646137/1347192000)],[(613993/3772137600),(-4831637/18860688000),(-42457379/9430344000)],[(667/251475840),(667/314344800),(-11339/628689600)],[0,0,0],[0,0,0]]
def vac26Rows09 : List (List Jet) := vac26Rows08 ++ [vac26Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows09_correct : jetRows 2 false 26 9 = vac26Rows09 := by
  rw [jetRows, vac26Rows08_correct]
  change vac26Rows08 ++ [jetStep 2 false 26 9 vac26Rows08] = vac26Rows08 ++ [vac26Row09]
  congr 1
  decide +kernel
def vac26Row10 : List Jet := [[(72992543/24255000),(-578732839/48510000),(-80738046047/423360000)],[(1455511601/9313920000),(96327723763/27941760000),(470668946347/83825280000)],[(-571149829/45265651200),(25225987/2514758400),(41441547803/75442752000)],[(-10284937/40415760000),(-236606957/94303440000),(8548867/11787930000)],[(-1297/1796256000),(-27053/816480000),(-291469/4490640000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac26Rows10 : List (List Jet) := vac26Rows09 ++ [vac26Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows10_correct : jetRows 2 false 26 10 = vac26Rows10 := by
  rw [jetRows, vac26Rows09_correct]
  change vac26Rows09 ++ [jetStep 2 false 26 10 vac26Rows09] = vac26Rows09 ++ [vac26Row10]
  congr 1
  decide +kernel
def vac26Row11 : List Jet := [[(-3953248/741125),(-4307037547/88935000),(11035407017/133402500)],[(5612504437/14636160000),(-109777050391/43908480000),(-4164444317797/131725440000)],[(97030021727/4979221632000),(1209399455387/4979221632000),(-55369844591/1659740544000)],[(-203775769/691558560000),(4562873551/1037337840000),(19218127463/691558560000)],[(-4916897/414935136000),(-9721051/691558560000),(10602203/34577928000)],[(-793/5532468480),(-793/3073593600),(793/922078080)],[0,0,0]]
def vac26Rows11 : List (List Jet) := vac26Rows10 ++ [vac26Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows11_correct : jetRows 2 false 26 11 = vac26Rows11 := by
  rw [jetRows, vac26Rows10_correct]
  change vac26Rows10 ++ [jetStep 2 false 26 11 vac26Rows10] = vac26Rows10 ++ [vac26Row11]
  congr 1
  decide +kernel
def vac26Row12 : List Jet := [[(-96331911/29645000),(11831536133/118580000),(38118852427493/51226560000)],[(-55382044247/49177497600),(-840653066051/65862720000),(1466598984409/86444820000)],[(2558465223983/74688324480000),(-8418822443881/18672081120000),(-68381127065249/16597405440000)],[(60087532837/29875329792000),(41025512543/3048503040000),(-2805850045249/49792216320000)],[(1084724173/74688324480000),(2932075717/7468832448000),(416674231/553246848000)],[(-1093/14819112000),(351779/98794080000),(1132963/98794080000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac26Rows12 : List (List Jet) := vac26Rows11 ++ [vac26Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Rows12_correct : jetRows 2 false 26 12 = vac26Rows12 := by
  rw [jetRows, vac26Rows11_correct]
  change vac26Rows11 ++ [jetStep 2 false 26 12 vac26Rows11] = vac26Rows11 ++ [vac26Row12]
  congr 1
  decide +kernel
def vac26Coeffs : List Jet := [[(-437356569/3705625),(-71368923249/29645000),(1463808698677/914760000)],[(87389055329/4553472000),(-339827195167/3415104000),(-30737780779943/15367968000)],[(4874149444523/5334880320000),(81282312700817/5334880320000),(-4535968515601/197588160000)],[(-186341446597/9336040560000),(7937823817381/18672081120000),(2389482182251/889146720000)],[(-205313281/194500845000),(-285181033/389001690000),(3767377129/64833615000)],[(-208667/12966723000),(-475009/5402801250),(1855547/4322241000)],[(-4/21611205),(-4/12006225),(8/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac26Coeffs_correct : widthCoefficients 2 false 26 = vac26Coeffs := by
  rw [widthCoefficients,vac26Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
