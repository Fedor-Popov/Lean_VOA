import VOA.Classification.COne.OrbIcoWVac09

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac10Rows00 := jetRows 3 false 10 0
theorem vac10Rows00_correct : jetRows 3 false 10 0 = vac10Rows00 := rfl
def vac10Row01 : List Jet := [[(13/3),(-8/3),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac10Rows01 : List (List Jet) := vac10Rows00 ++ [vac10Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows01_correct : jetRows 3 false 10 1 = vac10Rows01 := by
  rw [jetRows, vac10Rows00_correct]
  change vac10Rows00 ++ [jetStep 3 false 10 1 vac10Rows00] = vac10Rows00 ++ [vac10Row01]
  congr 1
  decide +kernel
def vac10Row02 : List Jet := [[(425/66),(-713/66),(124/33),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac10Rows02 : List (List Jet) := vac10Rows01 ++ [vac10Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows02_correct : jetRows 3 false 10 2 = vac10Rows02 := by
  rw [jetRows, vac10Rows01_correct]
  change vac10Rows01 ++ [jetStep 3 false 10 2 vac10Rows01] = vac10Rows01 ++ [vac10Row02]
  congr 1
  decide +kernel
def vac10Row03 : List Jet := [[(284/99),(-2791/198),(257/18),(-124/33)],[(-221/990),(-17/198),(68/495),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac10Rows03 : List (List Jet) := vac10Rows02 ++ [vac10Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows03_correct : jetRows 3 false 10 3 = vac10Rows03 := by
  rw [jetRows, vac10Rows02_correct]
  change vac10Rows02 ++ [jetStep 3 false 10 3 vac10Rows02] = vac10Rows02 ++ [vac10Row03]
  congr 1
  decide +kernel
def vac10Row04 : List Jet := [[(-1985/1782),(-2729/792),(3199/198),(-96119/7128)],[(-1766/4455),(743/2970),(1259/2970),(-992/4455)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac10Rows04 : List (List Jet) := vac10Rows03 ++ [vac10Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows04_correct : jetRows 3 false 10 4 = vac10Rows04 := by
  rw [jetRows, vac10Rows03_correct]
  change vac10Rows03 ++ [jetStep 3 false 10 4 vac10Rows03] = vac10Rows03 ++ [vac10Row04]
  congr 1
  decide +kernel
def vac10Row05 : List Jet := [[(-3059/8910),(312557/71280),(203/1584),(-186641/14256)],[(-9943/39600),(8741/10800),(1783/39600),(-9959/13200)],[(13/1800),(1/100),(-1/600),(-1/225)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac10Rows05 : List (List Jet) := vac10Rows04 ++ [vac10Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows05_correct : jetRows 3 false 10 5 = vac10Rows05 := by
  rw [jetRows, vac10Rows04_correct]
  change vac10Rows04 ++ [jetStep 3 false 10 5 vac10Rows04] = vac10Rows04 ++ [vac10Row05]
  congr 1
  decide +kernel
def vac10Row06 : List Jet := [[(229157/374220),(-851507/2993760),(-601999/83160),(1126003/299376)],[(167483/2993760),(522043/935550),(-2629057/2494800),(-716341/1871100)],[(119051/7484400),(49559/7484400),(-64601/2494800),(-60079/7484400)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac10Rows06 : List (List Jet) := vac10Rows05 ++ [vac10Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows06_correct : jetRows 3 false 10 6 = vac10Rows06 := by
  rw [jetRows, vac10Rows05_correct]
  change vac10Rows05 ++ [jetStep 3 false 10 6 vac10Rows05] = vac10Rows05 ++ [vac10Row06]
  congr 1
  decide +kernel
def vac10Row07 : List Jet := [[(-87925/392931),(-31670207/15717240),(151322621/62868960),(251837701/31434480)],[(3644731/44906400),(-12944917/44906400),(-546737/641520),(27871253/22453200)],[(6917/465696),(-650579/26195400),(-2354503/52390800),(276743/8731800)],[(-3653/17463600),(-8711/17463600),(-281/1164240),(281/1587600)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac10Rows07 : List (List Jet) := vac10Rows06 ++ [vac10Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows07_correct : jetRows 3 false 10 7 = vac10Rows07 := by
  rw [jetRows, vac10Rows06_correct]
  change vac10Rows06 ++ [jetStep 3 false 10 7 vac10Rows06] = vac10Rows06 ++ [vac10Row07]
  congr 1
  decide +kernel
def vac10Row08 : List Jet := [[(-59413/357210),(25886551/20956320),(589587533/167650560),(-2400387659/502951680)],[(-1592369/28512000),(-58710979/199584000),(7619729/11088000),(39780437/33264000)],[(28711/38102400),(-19231867/419126400),(3138467/209563200),(2242679/23284800)],[(-19931/32744250),(-46741/52390800),(173237/261954000),(327461/261954000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac10Rows08 : List (List Jet) := vac10Rows07 ++ [vac10Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows08_correct : jetRows 3 false 10 8 = vac10Rows08 := by
  rw [jetRows, vac10Rows07_correct]
  change vac10Rows07 ++ [jetStep 3 false 10 8 vac10Rows07] = vac10Rows07 ++ [vac10Row08]
  congr 1
  decide +kernel
def vac10Row09 : List Jet := [[(2977661/14145516),(4083319/6735960),(-4502621491/1508855040),(-2136414743/411505920)],[(-7125371921/226328256000),(5141728897/18860688000),(11158232489/15088550400),(-33671037563/28291032000)],[(-1693361/202078800),(-1007813/134719200),(5700103/53887680),(49237/2309472)],[(-117017/128304000),(718847/3772137600),(33546673/9430344000),(9553199/9430344000)],[(8671/1257379200),(667/28576800),(15341/628689600),(667/314344800)],[0,0,0,0],[0,0,0,0]]
def vac10Rows09 : List (List Jet) := vac10Rows08 ++ [vac10Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows09_correct : jetRows 3 false 10 9 = vac10Rows09 := by
  rw [jetRows, vac10Rows08_correct]
  change vac10Rows08 ++ [jetStep 3 false 10 9 vac10Rows08] = vac10Rows08 ++ [vac10Row09]
  congr 1
  decide +kernel
def vac10Row10 : List Jet := [[(2222639/192893400),(-4000360363/4243654800),(-17991599587/9053130240),(356990539/77157360)],[(29135764579/617258880000),(1524478259081/6789847680000),(-1578861257783/2263282560000),(-12309829402247/6789847680000)],[(-1953796693/1131641280000),(8737953533/188606880000),(21489652351/377213760000),(-1281009371/5773680000)],[(-2196709/3772137600),(17148527/5143824000),(5131579/1178793000),(-67468409/9430344000)],[(5708767/188606880000),(4795079/62868960000),(542737/31434480000),(-8325671/94303440000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac10Rows10 : List (List Jet) := vac10Rows09 ++ [vac10Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows10_correct : jetRows 3 false 10 10 = vac10Rows10 := by
  rw [jetRows, vac10Rows09_correct]
  change vac10Rows09 ++ [jetStep 3 false 10 10 vac10Rows09] = vac10Rows09 ++ [vac10Row10]
  congr 1
  decide +kernel
def vac10Row11 : List Jet := [[(-2512522/24111675),(-1194544313/2121827400),(166708309261/93360405600),(2183803095931/298753297920)],[(5179400381/150885504000),(-493240923331/2263282560000),(-31346523606929/24896108160000),(2317694260759/2766234240000)],[(72110602337/8298702720000),(31083016039/754427520000),(-1284694890923/8298702720000),(-392474648441/1185528960000)],[(7240687/16166304000),(552947867/88914672000),(-230075807/35565868800),(-2136964693/88914672000)],[(9097799/98794080000),(231005839/2074675680000),(-47033143/172889640000),(-1423661/3492720000)],[(-10309/27662342400),(-15067/9220780800),(-793/307359360),(-793/553246848)],[0,0,0,0]]
def vac10Rows11 : List (List Jet) := vac10Rows10 ++ [vac10Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows11_correct : jetRows 3 false 10 11 = vac10Rows11 := by
  rw [jetRows, vac10Rows10_correct]
  change vac10Rows10 ++ [jetStep 3 false 10 11 vac10Rows10] = vac10Rows10 ++ [vac10Row11]
  congr 1
  decide +kernel
def vac10Row12 : List Jet := [[(-558277/3306744),(-213136021/519631200),(3669426943949/640185638400),(24471396824467/2560742553600)],[(231811680451/81478172160000),(-1795556988167/2546192880000),(-3884418119809/3501015210000),(1523740594451659/224064973440000)],[(805756410673/44812994688000),(-1583860673399/56016243360000),(-35629976951309/64018563840000),(39909501610217/448129946880000)],[(33245875363/13579695360000),(22261717099/3319481088000),(-7940175873251/149376648960000),(-4513530702497/149376648960000)],[(138243313/452656512000),(-9009710851/37344162240000),(-144466822007/74688324480000),(-1452397729/4149351360000)],[(-6200057/1556006760000),(-165049/11547360000),(-364501/26943840000),(648779/88914672000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac10Rows12 : List (List Jet) := vac10Rows11 ++ [vac10Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Rows12_correct : jetRows 3 false 10 12 = vac10Rows12 := by
  rw [jetRows, vac10Rows11_correct]
  change vac10Rows11 ++ [jetStep 3 false 10 12 vac10Rows11] = vac10Rows11 ++ [vac10Row12]
  congr 1
  decide +kernel
def vac10Coeffs : List Jet := [[(105236041/14467005),(1784308213/254619288),(-29336455695377/112032486720),(-13915005454331/896259893760)],[(-302762455889/3703553280000),(53910525733457/2036954304000),(-378774392072071/56016243360000),(-32913335767318627/112032486720000)],[(-4173109457863/7468832448000),(6804215362841/2489610816000),(120629009135671/7468832448000),(-307848458313989/7468832448000)],[(-802287335873/9336040560000),(125371867637/2074675680000),(41762621405479/18672081120000),(-5838909207049/1697461920000)],[(-309131891/27785835000),(6884911267/166715010000),(410360153/11908215000),(-6470390827/55571670000)],[(25933/93555000),(152599/330783750),(-1432231/3087315000),(-396593/385914375)],[(-52/108056025),(-76/36018675),(-8/2401245),(-8/4322241)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac10Coeffs_correct : widthCoefficients 3 false 10 = vac10Coeffs := by
  rw [widthCoefficients,vac10Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
