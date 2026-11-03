import VOA.Classification.COne.OrbIcoWVac21

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac22Rows00 := jetRows 2 false 22 0
theorem vac22Rows00_correct : jetRows 2 false 22 0 = vac22Rows00 := rfl
def vac22Row01 : List Jet := [[(7/3),(-14/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac22Rows01 : List (List Jet) := vac22Rows00 ++ [vac22Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows01_correct : jetRows 2 false 22 1 = vac22Rows01 := by
  rw [jetRows, vac22Rows00_correct]
  change vac22Rows00 ++ [jetStep 2 false 22 1 vac22Rows00] = vac22Rows00 ++ [vac22Row01]
  congr 1
  decide +kernel
def vac22Row02 : List Jet := [[(1/6),(-55/6),(35/3)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac22Rows02 : List (List Jet) := vac22Rows01 ++ [vac22Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows02_correct : jetRows 2 false 22 2 = vac22Rows02 := by
  rw [jetRows, vac22Rows01_correct]
  change vac22Rows01 ++ [jetStep 2 false 22 2 vac22Rows01] = vac22Rows01 ++ [vac22Row02]
  congr 1
  decide +kernel
def vac22Row03 : List Jet := [[(-14/9),(281/90),(1681/90)],[(-119/990),(119/990),(119/495)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac22Rows03 : List (List Jet) := vac22Rows02 ++ [vac22Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows03_correct : jetRows 2 false 22 3 = vac22Rows03 := by
  rw [jetRows, vac22Rows02_correct]
  change vac22Rows02 ++ [jetStep 2 false 22 3 vac22Rows02] = vac22Rows02 ++ [vac22Row03]
  congr 1
  decide +kernel
def vac22Row04 : List Jet := [[(91/81),(7217/1080),(-2969/180)],[(-92/4455),(1583/2970),(-409/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac22Rows04 : List (List Jet) := vac22Rows03 ++ [vac22Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows04_correct : jetRows 2 false 22 4 = vac22Rows04 := by
  rw [jetRows, vac22Rows03_correct]
  change vac22Rows03 ++ [jetStep 2 false 22 4 vac22Rows03] = vac22Rows03 ++ [vac22Row04]
  congr 1
  decide +kernel
def vac22Row05 : List Jet := [[(77/324),(-11725/1296),(-131807/10800)],[(227/2160),(-1051/39600),(-59317/39600)],[(7/1800),0,(-7/600)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac22Rows05 : List (List Jet) := vac22Rows04 ++ [vac22Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows05_correct : jetRows 2 false 22 5 = vac22Rows05 := by
  rw [jetRows, vac22Rows04_correct]
  change vac22Rows04 ++ [jetStep 2 false 22 5 vac22Rows04] = vac22Rows04 ++ [vac22Row05]
  congr 1
  decide +kernel
def vac22Row06 : List Jet := [[(-2597/1944),(17425/7776),(7491917/226800)],[(-35087/598752),(-4918897/7484400),(1111729/2494800)],[(9377/7484400),(-2623/136080),(-39077/2494800)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac22Rows06 : List (List Jet) := vac22Rows05 ++ [vac22Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows06_correct : jetRows 2 false 22 6 = vac22Rows06 := by
  rw [jetRows, vac22Rows05_correct]
  change vac22Rows05 ++ [jetStep 2 false 22 6 vac22Rows05] = vac22Rows05 ++ [vac22Row06]
  congr 1
  decide +kernel
def vac22Row07 : List Jet := [[(982/729),(323755/40824),(-565953637/28576800)],[(-781661/12573792),(187923059/314344800),(92368583/39293100)],[(-96809/20956320),(-399893/52390800),(1167689/17463600)],[(-281/2494800),(-281/2494800),(281/831600)],[0,0,0],[0,0,0],[0,0,0]]
def vac22Rows07 : List (List Jet) := vac22Rows06 ++ [vac22Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows07_correct : jetRows 2 false 22 7 = vac22Rows07 := by
  rw [jetRows, vac22Rows06_correct]
  change vac22Rows06 ++ [jetStep 2 false 22 7 vac22Rows06] = vac22Rows06 ++ [vac22Row07]
  congr 1
  decide +kernel
def vac22Row08 : List Jet := [[(-2107/11664),(-96115/7776),(-264055987/10886400)],[(4696907/33530112),(20281711/55883520),(-539639213/174636000)],[(2816783/2095632000),(81773257/2095632000),(1670563/47628000)],[(-607/9355500),(23257/37422000),(47819/37422000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac22Rows08 : List (List Jet) := vac22Rows07 ++ [vac22Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows08_correct : jetRows 2 false 22 8 = vac22Rows08 := by
  rw [jetRows, vac22Rows07_correct]
  change vac22Rows07 ++ [jetStep 2 false 22 8 vac22Rows07] = vac22Rows07 ++ [vac22Row08]
  congr 1
  decide +kernel
def vac22Row09 : List Jet := [[(-145727/104976),(522535/122472),(41362755593/685843200)],[(-18387349/258660864),(-2099044921/1508855040),(-96632581949/75442752000)],[(25470383/4041576000),(-143969579/9430344000),(-78559991/377213760)],[(732223/3772137600),(14604703/18860688000),(-11287153/4715172000)],[(667/179625600),(667/89812800),(-667/89812800)],[0,0,0],[0,0,0]]
def vac22Rows09 : List (List Jet) := vac22Rows08 ++ [vac22Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows09_correct : jetRows 2 false 22 9 = vac22Rows09 := by
  rw [jetRows, vac22Rows08_correct]
  change vac22Rows08 ++ [jetStep 2 false 22 9 vac22Rows08] = vac22Rows08 ++ [vac22Row09]
  congr 1
  decide +kernel
def vac22Row10 : List Jet := [[(1171793/629856),(8774333/629856),(-16107376129/587865600)],[(-20837333/141087744),(34441132799/38799129600),(109699598047/12933043200)],[(-9885684923/1131641280000),(-11143173179/141455160000),(10914924751/125737920000)],[(629203/11316412800),(-41083249/18860688000),(-99084523/15717240000)],[(111787/26943840000),(-206947/8981280000),(-49123/561330000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac22Rows10 : List (List Jet) := vac22Rows09 ++ [vac22Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows10_correct : jetRows 2 false 22 10 = vac22Rows10 := by
  rw [jetRows, vac22Rows09_correct]
  change vac22Rows09 ++ [jetStep 2 false 22 10 vac22Rows09] = vac22Rows09 ++ [vac22Row10]
  congr 1
  decide +kernel
def vac22Row11 : List Jet := [[(602903/1732104),(-152572631/6928416),(-46570453787/440899200)],[(243038035/812934144),(803321571121/331948108800),(-26805696647861/4979221632000)],[(-26765122141/3556586880000),(3075019373527/24896108160000),(17731480675631/24896108160000)],[(-261904303/414935136000),(-99689869/51866892000),(11556720863/691558560000)],[(-4448363/414935136000),(-59425571/691558560000),(22328279/345779280000)],[(-793/3951763200),(-793/1317254400),0],[0,0,0]]
def vac22Rows11 : List (List Jet) := vac22Rows10 ++ [vac22Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows11_correct : jetRows 2 false 22 11 = vac22Rows11 := by
  rw [jetRows, vac22Rows10_correct]
  change vac22Rows10 ++ [jetStep 2 false 22 11 vac22Rows10] = vac22Rows10 ++ [vac22Row11]
  congr 1
  decide +kernel
def vac22Row12 : List Jet := [[(-5827661/1299078),(-2563742869/83140992),(1048215269573/7274836800)],[(58633904381/204859404288),(-1842074459581/365820364800),(-834397719480403/22406497344000)],[(53034673577/1280371276800),(2563265422303/8002320480000),(-69740037470009/64018563840000)],[(-609271/45722880000),(472804867819/29875329792000),(7390118032373/149376648960000)],[(-2420762497/74688324480000),(432298259/2667440160000),(5273617031/3556586880000)],[(-2767/3969405000),(1403011/889146720000),(68227/5388768000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac22Rows12 : List (List Jet) := vac22Rows11 ++ [vac22Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Rows12_correct : jetRows 2 false 22 12 = vac22Rows12 := by
  rw [jetRows, vac22Rows11_correct]
  change vac22Rows11 ++ [jetStep 2 false 22 12 vac22Rows11] = vac22Rows11 ++ [vac22Row12]
  congr 1
  decide +kernel
def vac22Coeffs : List Jet := [[(37030525/472392),(-353775121/1889568),(-239623411141/37791360)],[(72460809361/14632814592),(39582880793129/256074255360),(70127598871619/2240649734400)],[(-1311751889759/1778293440000),(22065257634613/5334880320000),(441466113547511/7468832448000)],[(-17811820963/518668920000),(-5023474735777/18672081120000),(28477820667119/18672081120000)],[(-51937937/145875633750),(-13163714863/1167005070000),(341277613/194500845000)],[(-4493/12966723000),(-2132503/10805602500),(-1412687/21611205000)],[(-4/15436575),(-4/5145525),0]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac22Coeffs_correct : widthCoefficients 2 false 22 = vac22Coeffs := by
  rw [widthCoefficients,vac22Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
