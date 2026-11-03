import VOA.Classification.COne.OrbIcoWVac27

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac28Rows00 := jetRows 2 false 28 0
theorem vac28Rows00_correct : jetRows 2 false 28 0 = vac28Rows00 := rfl
def vac28Row01 : List Jet := [[(4/3),(-17/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac28Rows01 : List (List Jet) := vac28Rows00 ++ [vac28Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows01_correct : jetRows 2 false 28 1 = vac28Rows01 := by
  rw [jetRows, vac28Rows00_correct]
  change vac28Rows00 ++ [jetStep 2 false 28 1 vac28Rows00] = vac28Rows00 ++ [vac28Row01]
  congr 1
  decide +kernel
def vac28Row02 : List Jet := [[(-4/3),(-335/66),(1139/66)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac28Rows02 : List (List Jet) := vac28Rows01 ++ [vac28Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows02_correct : jetRows 2 false 28 2 = vac28Rows02 := by
  rw [jetRows, vac28Rows01_correct]
  change vac28Rows01 ++ [jetStep 2 false 28 2 vac28Rows01] = vac28Rows01 ++ [vac28Row02]
  congr 1
  decide +kernel
def vac28Row03 : List Jet := [[(-2/9),(5186/495),(1531/198)],[(-34/495),(221/990),(289/990)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac28Rows03 : List (List Jet) := vac28Rows02 ++ [vac28Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows03_correct : jetRows 2 false 28 3 = vac28Rows03 := by
  rw [jetRows, vac28Rows02_correct]
  change vac28Rows02 ++ [jetStep 2 false 28 3 vac28Rows02] = vac28Rows02 ++ [vac28Row03]
  congr 1
  decide +kernel
def vac28Row04 : List Jet := [[(281/162),(-1816/495),(-30443/792)],[(313/4455),(1139/2970),(-2107/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac28Rows04 : List (List Jet) := vac28Rows03 ++ [vac28Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows04_correct : jetRows 2 false 28 4 = vac28Rows04 := by
  rw [jetRows, vac28Rows03_correct]
  change vac28Rows03 ++ [jetStep 2 false 28 4 vac28Rows03] = vac28Rows03 ++ [vac28Row04]
  congr 1
  decide +kernel
def vac28Row05 : List Jet := [[(-323/162),(-88997/8910),(41317/1320)],[(31/1100),(-74837/118800),(-51311/39600)],[(1/450),(-1/200),(-1/60)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac28Rows05 : List (List Jet) := vac28Rows04 ++ [vac28Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows05_correct : jetRows 2 false 28 5 = vac28Rows05 := by
  rw [jetRows, vac28Rows04_correct]
  change vac28Rows04 ++ [jetStep 2 false 28 5 vac28Rows04] = vac28Rows04 ++ [vac28Row05]
  congr 1
  decide +kernel
def vac28Row06 : List Jet := [[(635/972),(256193/13365),(562373/23760)],[(-69623/534600),(-25247/2138400),(478139/155925)],[(-1093/467775),(-129289/7484400),(29629/2494800)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac28Rows06 : List (List Jet) := vac28Rows05 ++ [vac28Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows06_correct : jetRows 2 false 28 6 = vac28Rows06 := by
  rw [jetRows, vac28Rows05_correct]
  change vac28Rows05 ++ [jetStep 2 false 28 6 vac28Rows05] = vac28Rows05 ++ [vac28Row06]
  congr 1
  decide +kernel
def vac28Row07 : List Jet := [[(16805/10206),(-15128287/1122660),(-29083363/320760)],[(26611/204120),(52316441/44906400),(-148875319/157172400)],[(-15989/8731800),(495701/20956320),(2312047/26195400)],[(-281/4365900),(281/3492720),(3653/5821200)],[0,0,0],[0,0,0],[0,0,0]]
def vac28Rows07 : List (List Jet) := vac28Rows06 ++ [vac28Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows07_correct : jetRows 2 false 28 7 = vac28Rows07 := by
  rw [jetRows, vac28Rows06_correct]
  change vac28Rows06 ++ [jetStep 2 false 28 7 vac28Rows06] = vac28Rows06 ++ [vac28Row07]
  congr 1
  decide +kernel
def vac28Row08 : List Jet := [[(-279697/81648),(-2643271/272160),(53805487/544320)],[(55841/2376000),(-47967307/28512000),(-389600363/66528000)],[(3442477/523908000),(34052701/2095632000),(-12213367/83825280)],[(9187/130977000),(181771/261954000),(56921/261954000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac28Rows08 : List (List Jet) := vac28Rows07 ++ [vac28Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows08_correct : jetRows 2 false 28 8 = vac28Rows08 := by
  rw [jetRows, vac28Rows07_correct]
  change vac28Rows07 ++ [jetStep 2 false 28 8 vac28Rows07] = vac28Rows07 ++ [vac28Row08]
  congr 1
  decide +kernel
def vac28Row09 : List Jet := [[(258401/91854),(6804031/174960),(7534883/349920)],[(-2189976221/8083152000),(1930792891/10777536000),(44920683389/3772137600)],[(-2068987/404157600),(-1620228403/18860688000),(-1730159791/18860688000)],[(24071/224532000),(-14908307/18860688000),(-95303941/18860688000)],[(667/314344800),(-667/1257379200),(-667/28576800)],[0,0,0],[0,0,0]]
def vac28Rows09 : List (List Jet) := vac28Rows08 ++ [vac28Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows09_correct : jetRows 2 false 28 9 = vac28Rows09 := by
  rw [jetRows, vac28Rows08_correct]
  change vac28Rows08 ++ [jetStep 2 false 28 9 vac28Rows08] = vac28Rows08 ++ [vac28Row09]
  congr 1
  decide +kernel
def vac28Row10 : List Jet := [[(1686971/1102248),(-958033001/22044960),(-554427439/2099520)],[(92840619401/242494560000),(3694088844431/969978240000),(-165796363673/46189440000)],[(-70293197/8083152000),(4711102811/53887680000),(19179941939/26943840000)],[(-4055851/11787930000),(-531726763/282910320000),(553155473/94303440000)],[(-57487/23575860000),(-425807/12573792000),(-2691781/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac28Rows10 : List (List Jet) := vac28Rows09 ++ [vac28Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows10_correct : jetRows 2 false 28 10 = vac28Rows10 := by
  rw [jetRows, vac28Rows09_correct]
  change vac28Rows09 ++ [jetStep 2 false 28 10 vac28Rows09] = vac28Rows09 ++ [vac28Row10]
  congr 1
  decide +kernel
def vac28Row11 : List Jet := [[(-9231599/1102248),(-463003451/17321040),(4643710055/12124728)],[(2307765083/26943840000),(-30070766213/4199040000),(-19104098787641/508083840000)],[(3255583/104544000),(1510401597349/8298702720000),(-7591044734527/8298702720000)],[(1909339/22228668000),(11056804049/1556006760000),(37113022663/1556006760000)],[(-64643/7203735000),(58660963/2074675680000),(272302031/691558560000)],[(-793/6915585600),(-793/9220780800),(793/614718720)],[0,0,0]]
def vac28Rows11 : List (List Jet) := vac28Rows10 ++ [vac28Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows11_correct : jetRows 2 false 28 11 = vac28Rows11 := by
  rw [jetRows, vac28Rows10_correct]
  change vac28Rows10 ++ [jetStep 2 false 28 11 vac28Rows10] = vac28Rows10 ++ [vac28Row11]
  congr 1
  decide +kernel
def vac28Row12 : List Jet := [[(89458343/13226976),(314097322499/1454967360),(190006497995/290993472)],[(-94522266437/52907904000),(-75614594464153/11639738880000),(6292910331315469/64018563840000)],[(-90571487329/8002320480000),(-6097894200061/6401856384000),(-839607521511193/224064973440000)],[(11654735747/5334880320000),(10708851103/7113173760000),(-2616956042441/21339521280000)],[(6497893/194500845000),(27847566349/74688324480000),(-22775201/339492384000)],[(464657/3112013520000),(499441/127020960000),(2670667/296382240000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac28Rows12 : List (List Jet) := vac28Rows11 ++ [vac28Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Rows12_correct : jetRows 2 false 28 12 = vac28Rows12 := by
  rw [jetRows, vac28Rows11_correct]
  change vac28Rows11 ++ [jetStep 2 false 28 12 vac28Rows11] = vac28Rows11 ++ [vac28Row12]
  congr 1
  decide +kernel
def vac28Coeffs : List Jet := [[(-67714075/236196),(-686798515/472392),(111413407667/5196312)],[(73663982233/18895680000),(-335531545827383/831409920000),(-9093135572632759/4572754560000)],[(159128115203/95265720000),(2059424208509/296382240000),(-4419344106964177/37344162240000)],[(140096029/8660520000),(1546590673/2309472000),(3078557898313/2667440160000)],[(-4612079/6483361500),(8140551679/1167005070000),(19468345783/291751267500)],[(-83927/5402801250),(-859307/64833615000),(3345779/5402801250)],[(-16/108056025),(-4/36018675),(4/2401245)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac28Coeffs_correct : widthCoefficients 2 false 28 = vac28Coeffs := by
  rw [widthCoefficients,vac28Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
