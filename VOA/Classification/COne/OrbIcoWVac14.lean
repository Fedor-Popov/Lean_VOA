import VOA.Classification.COne.OrbIcoWVac13

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac14Rows00 := jetRows 3 false 14 0
theorem vac14Rows00_correct : jetRows 3 false 14 0 = vac14Rows00 := rfl
def vac14Row01 : List Jet := [[(11/3),(-10/3),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac14Rows01 : List (List Jet) := vac14Rows00 ++ [vac14Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows01_correct : jetRows 3 false 14 1 = vac14Rows01 := by
  rw [jetRows, vac14Rows00_correct]
  change vac14Rows00 ++ [jetStep 3 false 14 1 vac14Rows00] = vac14Rows00 ++ [vac14Row01]
  congr 1
  decide +kernel
def vac14Row02 : List Jet := [[(85/22),(-247/22),(65/11),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac14Rows02 : List (List Jet) := vac14Rows01 ++ [vac14Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows02_correct : jetRows 3 false 14 2 = vac14Rows02 := by
  rw [jetRows, vac14Rows01_correct]
  change vac14Rows01 ++ [jetStep 3 false 14 2 vac14Rows01] = vac14Rows01 ++ [vac14Row02]
  congr 1
  decide +kernel
def vac14Row03 : List Jet := [[(-6/55),(-3083/330),(2011/110),(-247/33)],[(-17/90),(-17/990),(17/99),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac14Rows03 : List (List Jet) := vac14Rows02 ++ [vac14Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows03_correct : jetRows 3 false 14 3 = vac14Rows03 := by
  rw [jetRows, vac14Rows02_correct]
  change vac14Rows02 ++ [jetStep 3 false 14 3 vac14Rows02] = vac14Rows02 ++ [vac14Row03]
  congr 1
  decide +kernel
def vac14Row04 : List Jet := [[(-206/165),(45071/11880),(65401/5940),(-253511/11880)],[(-8/33),(1279/2970),(959/2970),(-104/297)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac14Rows04 : List (List Jet) := vac14Rows03 ++ [vac14Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows04_correct : jetRows 3 false 14 4 = vac14Rows04 := by
  rw [jetRows, vac14Rows03_correct]
  change vac14Rows03 ++ [jetStep 3 false 14 4 vac14Rows03] = vac14Rows03 ++ [vac14Row04]
  congr 1
  decide +kernel
def vac14Row05 : List Jet := [[(881/1100),(133433/39600),(-453979/39600),(-305663/39600)],[(-67/2640),(84511/118800),(-22541/39600),(-31133/39600)],[(11/1800),(1/150),(-1/200),(-1/180)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac14Rows05 : List (List Jet) := vac14Rows04 ++ [vac14Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows05_correct : jetRows 3 false 14 5 = vac14Rows05 := by
  rw [jetRows, vac14Rows04_correct]
  change vac14Rows04 ++ [jetStep 3 false 14 5 vac14Rows04] = vac14Rows04 ++ [vac14Row05]
  congr 1
  decide +kernel
def vac14Row06 : List Jet := [[(269/2200),(-350903/79200),(-44191/13200),(775369/39600)],[(1789/15840),(-19127/356400),(-3390379/2494800),(283169/415800)],[(1649/166320),(-16067/2494800),(-24223/831600),(601/831600)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac14Rows06 : List (List Jet) := vac14Rows05 ++ [vac14Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows06_correct : jetRows 3 false 14 6 = vac14Rows06 := by
  rw [jetRows, vac14Rows05_correct]
  change vac14Rows05 ++ [jetStep 3 false 14 6 vac14Rows05] = vac14Rows05 ++ [vac14Row06]
  congr 1
  decide +kernel
def vac14Row07 : List Jet := [[(-709/1155),(319567/415800),(898129/79200),(-15599/59400)],[(-6709/184800),(-95861/184800),(1029587/2910600),(173519/77616)],[(110533/34927200),(-69691/2095632),(-645121/52390800),(91991/1455300)],[(-281/1587600),(-6463/17463600),(-281/5821200),(5339/17463600)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac14Rows07 : List (List Jet) := vac14Rows06 ++ [vac14Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows07_correct : jetRows 3 false 14 7 = vac14Rows07 := by
  rw [jetRows, vac14Rows06_correct]
  change vac14Rows06 ++ [jetStep 3 false 14 7 vac14Rows06] = vac14Rows06 ++ [vac14Row07]
  congr 1
  decide +kernel
def vac14Row08 : List Jet := [[(64809/154000),(889563/308000),(-11198127/2464000),(-5904407/288000)],[(-68461/1056000),(876743/3168000),(1134887/792000),(-31455967/33264000)],[(-4437863/698544000),(-32340983/2095632000),(10475021/130977000),(63964163/1047816000)],[(-563/1455300),(-16139/87318000),(111103/87318000),(30781/29106000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac14Rows08 : List (List Jet) := vac14Rows07 ++ [vac14Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows08_correct : jetRows 3 false 14 8 = vac14Rows08 := by
  rw [jetRows, vac14Rows07_correct]
  change vac14Rows07 ++ [jetStep 3 false 14 8 vac14Rows07] = vac14Rows07 ++ [vac14Row08]
  congr 1
  decide +kernel
def vac14Row09 : List Jet := [[(1863/14000),(-94819/34650),(-179934913/22176000),(2330586187/199584000)],[(14051/197120),(237657863/598752000),(-8398843177/8382528000),(-13947654701/4191264000)],[(-736079/449064000),(73653719/1886068800),(591257837/9430344000),(-205910017/1178793000)],[(-7207/25660800),(25882471/18860688000),(606469/235758600),(-19996093/9430344000)],[(667/114307200),(11339/628689600),(8671/628689600),(-667/78586200)],[0,0,0,0],[0,0,0,0]]
def vac14Rows09 : List (List Jet) := vac14Rows08 ++ [vac14Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows09_correct : jetRows 3 false 14 9 = vac14Rows09 := by
  rw [jetRows, vac14Rows08_correct]
  change vac14Rows08 ++ [jetStep 3 false 14 9 vac14Rows08] = vac14Rows08 ++ [vac14Row09]
  congr 1
  decide +kernel
def vac14Row10 : List Jet := [[(-648261/1540000),(-44893217/41580000),(6053505803/665280000),(6385302793/299376000)],[(234737/8064000),(-6138409657/11975040000),(-4138987487/2395008000),(68989571311/27941760000)],[(17249917/2155507200),(119469007/5773680000),(-1635401981/10777536000),(-1306483991/5388768000)],[(27462181/94303440000),(683712049/282910320000),(-44626361/15717240000),(-15670709/1428840000)],[(82333/4191264000),(1990451/62868960000),(-729689/15717240000),(-3439817/31434480000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac14Rows10 : List (List Jet) := vac14Rows09 ++ [vac14Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows10_correct : jetRows 3 false 14 10 = vac14Rows10 := by
  rw [jetRows, vac14Rows09_correct]
  change vac14Rows09 ++ [jetStep 3 false 14 10 vac14Rows09] = vac14Rows09 ++ [vac14Row10]
  congr 1
  decide +kernel
def vac14Row11 : List Jet := [[(-513/4235000),(469666027/152460000),(617146897/67760000),(-83818545527/4390848000)],[(-92725771/975744000),(-67419550817/131725440000),(36444692741/18817920000),(1005525301279/131725440000)],[(112855229/47421158400),(-377214539189/4979221632000),(-4990540877713/24896108160000),(265278613799/553246848000)],[(66045593/98794080000),(-679820023/518668920000),(-1205156033/76839840000),(-9907973/15717240000)],[(5023307/138311712000),(-119786201/2074675680000),(-113512871/345779280000),(-36136279/345779280000)],[(-793/2514758400),(-793/614718720),(-793/461039040),(-793/2766234240)],[0,0,0,0]]
def vac14Rows11 : List (List Jet) := vac14Rows10 ++ [vac14Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows11_correct : jetRows 3 false 14 11 = vac14Rows11 := by
  rw [jetRows, vac14Rows10_correct]
  change vac14Rows10 ++ [jetStep 3 false 14 11 vac14Rows10] = vac14Rows10 ++ [vac14Row11]
  congr 1
  decide +kernel
def vac14Row12 : List Jet := [[(64809/154000),(321571539/67760000),(-22084933889/3659040000),(-2313575033557/29272320000)],[(-7458776837/58544640000),(537279700151/790352640000),(1418626620023/197588160000),(3408749807/6272640000)],[(-1847953513/101616768000),(-406522861793/2667440160000),(2333486328419/5975065958400),(105935727250543/49792216320000)],[(-160416701/7113173760000),(-58300451731/4267904256000),(-339530042573/21339521280000),(257953417433/2371057920000)],[(774768833/24896108160000),(-5522212121/9336040560000),(-46602692713/74688324480000),(1502979661/691558560000)],[(-379/142884000),(-311161/42340320000),(1073/6586272000),(59977/3293136000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac14Rows12 : List (List Jet) := vac14Rows11 ++ [vac14Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Rows12_correct : jetRows 3 false 14 12 = vac14Rows12 := by
  rw [jetRows, vac14Rows11_correct]
  change vac14Rows11 ++ [jetStep 3 false 14 12 vac14Rows11] = vac14Rows11 ++ [vac14Row12]
  congr 1
  decide +kernel
def vac14Coeffs : List Jet := [[(-8147637/605000),(-852136547/7260000),(141546022523/261360000),(2060350786363/1045440000)],[(3677155253/1393920000),(-645700942217/18817920000),(-688827115433/4704480000),(6408843244823/13172544000)],[(1138763339/2032335360),(1657351732529/1066976064000),(-914018944759997/37344162240000),(-223223852365027/12448054080000)],[(519020699/22228668000),(960449177357/2667440160000),(-547656471083/533488032000),(-48336321713/14113440000)],[(20186179/32416807500),(8188228963/389001690000),(-3025408997/64833615000),(-3577102201/43222410000)],[(586517/4322241000),(99557/32416807500),(-15874987/21611205000),(-4966219/10805602500)],[(-4/9823275),(-4/2401245),(-16/7203735),(-8/21611205)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac14Coeffs_correct : widthCoefficients 3 false 14 = vac14Coeffs := by
  rw [widthCoefficients,vac14Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
