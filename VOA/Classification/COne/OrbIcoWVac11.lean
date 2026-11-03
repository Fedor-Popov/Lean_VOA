import VOA.Classification.COne.OrbIcoWVac10

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac11Rows00 := jetRows 3 false 11 0
theorem vac11Rows00_correct : jetRows 3 false 11 0 = vac11Rows00 := rfl
def vac11Row01 : List Jet := [[(25/6),(-17/6),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac11Rows01 : List (List Jet) := vac11Rows00 ++ [vac11Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows01_correct : jetRows 3 false 11 1 = vac11Rows01 := by
  rw [jetRows, vac11Rows00_correct]
  change vac11Rows00 ++ [jetStep 3 false 11 1 vac11Rows00] = vac11Rows00 ++ [vac11Row01]
  congr 1
  decide +kernel
def vac11Row02 : List Jet := [[(23/4),-11,(17/4),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac11Rows02 : List (List Jet) := vac11Rows01 ++ [vac11Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows02_correct : jetRows 3 false 11 2 = vac11Rows02 := by
  rw [jetRows, vac11Rows01_correct]
  change vac11Rows01 ++ [jetStep 3 false 11 2 vac11Rows01] = vac11Rows01 ++ [vac11Row02]
  congr 1
  decide +kernel
def vac11Row03 : List Jet := [[(39/20),(-131/10),(185/12),(-68/15)],[(-85/396),(-34/495),(289/1980),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac11Rows03 : List (List Jet) := vac11Rows02 ++ [vac11Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows03_correct : jetRows 3 false 11 3 = vac11Rows03 := by
  rw [jetRows, vac11Rows02_correct]
  change vac11Rows02 ++ [jetStep 3 false 11 3 vac11Rows02] = vac11Rows02 ++ [vac11Row03]
  congr 1
  decide +kernel
def vac11Row04 : List Jet := [[(-107/80),(-209/144),(33521/2160),(-33401/2160)],[(-211/594),(901/2970),(604/1485),(-34/135)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac11Rows04 : List (List Jet) := vac11Rows03 ++ [vac11Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows04_correct : jetRows 3 false 11 4 = vac11Rows04 := by
  rw [jetRows, vac11Rows03_correct]
  change vac11Rows03 ++ [jetStep 3 false 11 4 vac11Rows03] = vac11Rows03 ++ [vac11Row04]
  congr 1
  decide +kernel
def vac11Row05 : List Jet := [[(-51/1600),(939/200),(-6523/2400),(-23117/1800)],[(-1969/10800),(96353/118800),(-1373/13200),(-92969/118800)],[(1/144),(11/1200),(-1/400),(-17/3600)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac11Rows05 : List (List Jet) := vac11Rows04 ++ [vac11Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows05_correct : jetRows 3 false 11 5 = vac11Rows05 := by
  rw [jetRows, vac11Rows04_correct]
  change vac11Rows04 ++ [jetStep 3 false 11 5 vac11Rows04] = vac11Rows04 ++ [vac11Row05]
  congr 1
  decide +kernel
def vac11Row06 : List Jet := [[(379/640),(-93161/67200),(-750517/100800),(2201581/302400)],[(110317/1247400),(1025279/2494800),(-2988257/2494800),(-7837/45360)],[(2855/199584),(667/226800),(-5681/207900),(-3121/498960)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac11Rows06 : List (List Jet) := vac11Rows05 ++ [vac11Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows06_correct : jetRows 3 false 11 6 = vac11Rows06 := by
  rw [jetRows, vac11Rows05_correct]
  change vac11Rows05 ++ [jetStep 3 false 11 6 vac11Rows05] = vac11Rows05 ++ [vac11Row06]
  congr 1
  decide +kernel
def vac11Row07 : List Jet := [[(-3637/9600),(-72601/40320),(706987/151200),(1455137/181440)],[(1528141/27941760),(-6288299/15523200),(-4935649/7761600),(2004389/1270080)],[(593807/52390800),(-503213/17463600),(-2007317/52390800),(2109347/52390800)],[(-281/1397088),(-8149/17463600),(-281/1455300),(3653/17463600)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac11Rows07 : List (List Jet) := vac11Rows06 ++ [vac11Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows07_correct : jetRows 3 false 11 7 = vac11Rows07 := by
  rw [jetRows, vac11Rows06_correct]
  change vac11Rows06 ++ [jetStep 3 false 11 7 vac11Rows06] = vac11Rows06 ++ [vac11Row07]
  congr 1
  decide +kernel
def vac11Row08 : List Jet := [[(-8957/128000),(512849/268800),(23520977/8064000),(-102559123/12096000)],[(-40507939/558835200),(-26430511/139708800),(185733239/186278400),(321324547/349272000)],[(-1203317/523908000),(-42214153/1047816000),(1640383/47628000),(8298649/87318000)],[(-1919/3492720),(-20267/29106000),(14881/17463600),(108271/87318000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac11Rows08 : List (List Jet) := vac11Rows07 ++ [vac11Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows08_correct : jetRows 3 false 11 8 = vac11Rows08 := by
  rw [jetRows, vac11Rows07_correct]
  change vac11Rows07 ++ [jetStep 3 false 11 8 vac11Rows07] = vac11Rows07 ++ [vac11Row08]
  congr 1
  decide +kernel
def vac11Row09 : List Jet := [[(67523/256000),(2515117/16128000),(-33437737/6912000),(-89807017/20736000)],[(-364051/44906400),(91368451/239500800),(90420703/179625600),(-759240667/399168000)],[(-571872967/75442752000),(289469893/37721376000),(8170866223/75442752000),(-13772333/571536000)],[(-2732029/3772137600),(11518873/18860688000),(32866651/9430344000),(874487/3143448000)],[(667/100590336),(55361/2514758400),(27347/1257379200),(-667/1257379200)],[0,0,0,0],[0,0,0,0]]
def vac11Rows09 : List (List Jet) := vac11Rows08 ++ [vac11Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows09_correct : jetRows 3 false 11 9 = vac11Rows09 := by
  rw [jetRows, vac11Rows08_correct]
  change vac11Rows08 ++ [jetStep 3 false 11 9 vac11Rows08] = vac11Rows08 ++ [vac11Row09]
  congr 1
  decide +kernel
def vac11Row10 : List Jet := [[(-555347/7680000),(-335175263/241920000),(-191540203/181440000),(140758819/15552000)],[(2753779639/45722880000),(17826586483/167650560000),(-593043792863/502951680000),(-50362367621/33530112000)],[(40785869/22632825600),(322009043/6466521600),(14416909/2095632000),(-304776298021/1131641280000)],[(-145773973/565820640000),(963266939/282910320000),(484036367/188606880000),(-25503911/2886840000)],[(137971/5029516800),(503263/7858620000),(-170257/125737920000),(-56563/582120000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac11Rows10 : List (List Jet) := vac11Rows09 ++ [vac11Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows10_correct : jetRows 3 false 11 10 = vac11Rows10 := by
  rw [jetRows, vac11Rows09_correct]
  change vac11Rows09 ++ [jetStep 3 false 11 10 vac11Rows09] = vac11Rows09 ++ [vac11Row10]
  congr 1
  decide +kernel
def vac11Row11 : List Jet := [[(-877799/5632000),(-106915079/443520000),(1024616741/241920000),(5725378979/725760000)],[(128853015317/11064936960000),(-2325369442511/5532468480000),(-2994007061867/2766234240000),(3722966965001/1383117120000)],[(7114627441/711317376000),(793754413/59276448000),(-3960075901/17782934400),(-184878165047/889146720000)],[(6090681907/8298702720000),(36347867653/8298702720000),(-89093628629/8298702720000),(-174090798571/8298702720000)],[(12565361/165974054400),(117058547/2074675680000),(-28657249/92207808000),(-363967007/1037337840000)],[(-793/2212987392),(-793/512265600),(-793/335301120),(-793/691558560)],[0,0,0,0]]
def vac11Rows11 : List (List Jet) := vac11Rows10 ++ [vac11Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows11_correct : jetRows 3 false 11 11 = vac11Rows11 := by
  rw [jetRows, vac11Rows10_correct]
  change vac11Rows10 ++ [jetStep 3 false 11 11 vac11Rows10] = vac11Rows10 ++ [vac11Row11]
  congr 1
  decide +kernel
def vac11Row12 : List Jet := [[(-20798427/112640000),(598010103/788480000),(32175316823/3548160000),(3745603/32256000)],[(-383056747763/6638962176000),(-9101468153753/11064936960000),(23675968983791/33194810880000),(676969899313/68302080000)],[(6994732688939/597506595840000),(-888826849991/8298702720000),(-147526481685577/298753297920000),(21303956885623/27159390720000)],[(12140263397/5431878144000),(-2609603323/1844156160000),(-7971909998977/149376648960000),(1114689342737/149376648960000)],[(4539808333/21339521280000),(-4251681949/9958443264000),(-51064851449/29875329792000),(11256854857/29875329792000)],[(-60239/16597405440),(-3675773/296382240000),(-43291/4490640000),(320119/29638224000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac11Rows12 : List (List Jet) := vac11Rows11 ++ [vac11Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Rows12_correct : jetRows 3 false 11 12 = vac11Rows12 := by
  rw [jetRows, vac11Rows11_correct]
  change vac11Rows11 ++ [jetStep 3 false 11 12 vac11Rows11] = vac11Rows11 ++ [vac11Row12]
  congr 1
  decide +kernel
def vac11Coeffs : List Jet := [[(38318553/5120000),(-649623637/15360000),(-48773616649/161280000),(132049008971/241920000)],[(2244825739813/1106493696000),(276013244293/11525976000),(-5659598996969/69155856000),(-4834729577791/18441561600)],[(-19719711735883/74688324480000),(39262956886397/8298702720000),(245301203059601/37344162240000),(-2095506943950271/37344162240000)],[(-84414269711/1333720080000),(41644843913/127020960000),(3811383861343/2667440160000),(-11584959996563/2667440160000)],[(-281348483/43222410000),(15236965967/389001690000),(3438527599/389001690000),(-15745761133/129667230000)],[(612853/2593344600),(2577199/8104201875),(-847927/1440747000),(-686458/736745625)],[(-2/4322241),(-8/4002075),(-2/654885),(-32/21611205)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac11Coeffs_correct : widthCoefficients 3 false 11 = vac11Coeffs := by
  rw [widthCoefficients,vac11Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
