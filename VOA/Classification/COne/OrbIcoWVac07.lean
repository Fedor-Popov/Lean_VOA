import VOA.Classification.COne.OrbIcoWVac06

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac07Rows00 := jetRows 4 false 7 0
theorem vac07Rows00_correct : jetRows 4 false 7 0 = vac07Rows00 := rfl
def vac07Row01 : List Jet := [[(29/6),(-13/6),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows01 : List (List Jet) := vac07Rows00 ++ [vac07Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows01_correct : jetRows 4 false 7 1 = vac07Rows01 := by
  rw [jetRows, vac07Rows00_correct]
  change vac07Rows00 ++ [jetStep 4 false 7 1 vac07Rows00] = vac07Rows00 ++ [vac07Row01]
  congr 1
  decide +kernel
def vac07Row02 : List Jet := [[(1147/132),(-325/33),(325/132),0,0],[(-1/22),(-1/22),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows02 : List (List Jet) := vac07Rows01 ++ [vac07Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows02_correct : jetRows 4 false 7 2 = vac07Rows02 := by
  rw [jetRows, vac07Rows01_correct]
  change vac07Rows01 ++ [jetStep 4 false 7 2 vac07Rows01] = vac07Rows01 ++ [vac07Row02]
  congr 1
  decide +kernel
def vac07Row03 : List Jet := [[(2537/396),(-15899/990),(20917/1980),(-65/33),0],[(-493/1980),(-68/495),(221/1980),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows03 : List (List Jet) := vac07Rows02 ++ [vac07Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows03_correct : jetRows 4 false 7 3 = vac07Rows03 := by
  rw [jetRows, vac07Rows02_correct]
  change vac07Rows02 ++ [jetStep 4 false 7 3 vac07Rows02] = vac07Rows02 ++ [vac07Row03]
  congr 1
  decide +kernel
def vac07Row04 : List Jet := [[(9419/14256),(-20371/2160),(13741/880),(-572741/71280),(1495/1188)],[(-4729/8910),(173/2970),(658/1485),(-130/891),0],[(1/792),(1/396),(1/792),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows04 : List (List Jet) := vac07Rows03 ++ [vac07Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows04_correct : jetRows 4 false 7 4 = vac07Rows04 := by
  rw [jetRows, vac07Rows03_correct]
  change vac07Rows03 ++ [jetStep 4 false 7 4 vac07Rows03] = vac07Rows03 ++ [vac07Row04]
  congr 1
  decide +kernel
def vac07Row05 : List Jet := [[(-55085/57024),(91169/71280),(1612871/237600),(-175331/16200),(7045051/1425600)],[(-12181/23760),(80297/118800),(5791/13200),(-72833/118800),(325/2376)],[(29/3600),(1/80),(1/1200),(-13/3600),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows05 : List (List Jet) := vac07Rows04 ++ [vac07Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows05_correct : jetRows 4 false 7 5 = vac07Rows05 := by
  rw [jetRows, vac07Rows04_correct]
  change vac07Rows04 ++ [jetStep 4 false 7 5 vac07Rows04] = vac07Rows04 ++ [vac07Row05]
  congr 1
  decide +kernel
def vac07Row06 : List Jet := [[(79955/342144),(3351439/1710720),(-5006911/1425600),(-2607787/855360),(52797563/8553600)],[(-30821/213840),(471457/534600),(-357457/831600),(-1136831/1496880),(276701/467775)],[(316249/14968800),(28927/1496880),(-5959/311850),(-7949/680400),(481/85536)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows06 : List (List Jet) := vac07Rows05 ++ [vac07Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows06_correct : jetRows 4 false 7 6 = vac07Rows06 := by
  rw [jetRows, vac07Rows05_correct]
  change vac07Rows05 ++ [jetStep 4 false 7 6 vac07Rows05] = vac07Rows05 ++ [vac07Row06]
  congr 1
  decide +kernel
def vac07Row07 : List Jet := [[(122615/653184),(-39340379/35925120),(-11665043/6415200),(51961013/12830400),(21765263/25660800)],[(318733/3265920),(39461363/179625600),(-642988387/628689600),(24500023/125737920),(1001990261/1257379200)],[(147089/5239080),(-3887/970200),(-2929403/52390800),(315473/52390800),(408371/17463600)],[(-8149/34927200),(-10397/17463600),(-281/727650),(281/3492720),(3653/34927200)],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows07 : List (List Jet) := vac07Rows06 ++ [vac07Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows07_correct : jetRows 4 false 7 7 = vac07Rows07 := by
  rw [jetRows, vac07Rows06_correct]
  change vac07Rows06 ++ [jetStep 4 false 7 7 vac07Rows06] = vac07Rows06 ++ [vac07Row07]
  congr 1
  decide +kernel
def vac07Row08 : List Jet := [[(-9826661/57480192),(-5372471/15966720),(923247637/479001600),(634518443/513216000),(-390031733/114048000)],[(221407/6842880),(-178421/570240),(-111104629/399168000),(162656173/149688000),(-27187207/399168000)],[(5886953/349272000),(-49075549/1047816000),(-47369969/1047816000),(19270763/261954000),(3662959/209563200)],[(-19091/23814000),(-407531/261954000),(-16537/261954000),(59113/52390800),(30311/130977000)],[(1/1330560),(1/332640),(1/221760),(1/332640),(1/1330560)],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows08 : List (List Jet) := vac07Rows07 ++ [vac07Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows08_correct : jetRows 4 false 7 8 = vac07Rows08 := by
  rw [jetRows, vac07Rows07_correct]
  change vac07Rows07 ++ [jetStep 4 false 7 8 vac07Rows07] = vac07Rows07 ++ [vac07Row08]
  congr 1
  decide +kernel
def vac07Row09 : List Jet := [[(-1349153/1034643456),(938050633/1724405760),(368978857/783820800),(-291037812689/129330432000),(-1301868529/1231718400)],[(-30009979/646652160),(-50191487/431101440),(21699625643/37721376000),(97598408189/226328256000),(-42733641821/37721376000)],[(-69454571/32332608000),(-1983470831/37721376000),(690364387/15088550400),(6128870333/56582064000),(-782127559/10777536000)],[(-866977/538876800),(-31135427/18860688000),(6771781/2357586000),(2881817/1047816000),(-5123743/3772137600)],[(19343/2514758400),(68701/2514758400),(40687/1257379200),(12673/1257379200),(-15341/2514758400)],[0,0,0,0,0],[0,0,0,0,0]]
def vac07Rows09 : List (List Jet) := vac07Rows08 ++ [vac07Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows09_correct : jetRows 4 false 7 9 = vac07Rows09 := by
  rw [jetRows, vac07Rows08_correct]
  change vac07Rows08 ++ [jetStep 4 false 7 9 vac07Rows08] = vac07Rows08 ++ [vac07Row09]
  congr 1
  decide +kernel
def vac07Row10 : List Jet := [[(355108949/6207860736),(1406351843/15519651840),(-1446244397/1616630400),(-104252636267/96997824000),(4067649937013/1939956480000)],[(-259478719/15519651840),(13263535141/77598259200),(50416040347/129330432000),(-10934939708761/13579695360000),(-11495224853419/13579695360000)],[(-67370321/6735960000),(-1009906691/161663040000),(3430873417/26943840000),(-234349/34214400),(-226226819/1154736000)],[(-239940541/113164128000),(67663943/56582064000),(1553215019/188606880000),(-51931423/141455160000),(-370568413/51438240000)],[(14897933/377213760000),(1843319/15717240000),(10550923/125737920000),(-2228353/47151720000),(-8156507/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680),(-1/7983360)],[0,0,0,0,0]]
def vac07Rows10 : List (List Jet) := vac07Rows09 ++ [vac07Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows10_correct : jetRows 4 false 7 10 = vac07Rows10 := by
  rw [jetRows, vac07Rows09_correct]
  change vac07Rows09 ++ [jetStep 4 false 7 10 vac07Rows09] = vac07Rows09 ++ [vac07Row10]
  congr 1
  decide +kernel
def vac07Row11 : List Jet := [[(130970281/6207860736),(-63839789/484989120),(-657422796719/853580851200),(2286985718953/4267904256000),(7760968553819/2667440160000)],[(1966035331/113810780160),(53340167311/284526950400),(-465409841/2258150400),(-2354196145717/1778293440000),(32853563842919/49792216320000)],[(-22078364621/3556586880000),(307558198583/6224027040000),(44874877699/389001690000),(-341214732413/1244805408000),(-446482192391/2489610816000)],[(-298625209/142263475200),(761990093/90531302400),(268727593553/24896108160000),(-477423111161/24896108160000),(-46136701147/3556586880000)],[(126197713/829870272000),(693506027/2074675680000),(-15857993/461039040000),(-481278047/1037337840000),(-617588077/4149351360000)],[(-22997/55324684800),(-793/419126400),(-793/245887488),(-793/345779280),(-793/3688312320)],[0,0,0,0,0]]
def vac07Rows11 : List (List Jet) := vac07Rows10 ++ [vac07Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows11_correct : jetRows 4 false 7 11 = vac07Rows11 := by
  rw [jetRows, vac07Rows10_correct]
  change vac07Rows10 ++ [jetStep 4 false 7 11 vac07Rows10] = vac07Rows10 ++ [vac07Row11]
  congr 1
  decide +kernel
def vac07Row12 : List Jet := [[(362224993/6772211712),(-124096473553/372471644160),(-17050927085257/10242970214400),(6158544218957/2327947776000),(1699513880244011/256074255360000)],[(43846563241/1024297021440),(1490787676867/5121485107200),(-5460730852783/5121485107200),(-156087544698433/64018563840000),(93564483425401/20369543040000)],[(-141606293053/51214851072000),(4695135942817/32009281920000),(32060803133789/896259893760000),(-181089001351057/179251978752000),(29623197666413/89625989376000)],[(-120777486847/42679042560000),(138291842159/4267904256000),(-7731722839/2371057920000),(-17317203769/176359680000),(205525295317/10669760640000)],[(105657670511/149376648960000),(43865397803/49792216320000),(-263186045513/149376648960000),(-354788557439/149376648960000),(53145364823/49792216320000)],[(-31983461/6224027040000),(-2614937/127020960000),(-160357/5927644800),(-561667/88914672000),(2378989/177829344000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080),(1/31933440)]]
def vac07Rows12 : List (List Jet) := vac07Rows11 ++ [vac07Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Rows12_correct : jetRows 4 false 7 12 = vac07Rows12 := by
  rw [jetRows, vac07Rows11_correct]
  change vac07Rows11 ++ [jetStep 4 false 7 12 vac07Rows11] = vac07Rows11 ++ [vac07Row12]
  congr 1
  decide +kernel
def vac07Coeffs : List Jet := [[(-1302428075/483729408),(108575187643/5321023488),(8602905849499/146328145920),(-79242279414337/365820364800),(-288349932979901/3658203648000)],[(-27871960805/14632814592),(-401945069227/36582036480),(1485720490369/22863772800),(92611229310883/3200928192000),(-64613464830973237/224064973440000)],[(147866948773/1524251520000),(-68111892988169/10669760640000),(224267397887/25147584000),(270524169363869/7468832448000),(-1405335047904757/18672081120000)],[(15893360041/166715010000),(-4176229539401/2667440160000),(2504304416029/889146720000),(821593478161/533488032000),(-361247093093/67898476800)],[(-2573468636/72937816875),(21602933/1071630000),(129834767033/1167005070000),(-53656871197/1167005070000),(-38967704431/389001690000)],[(5499959/12966723000),(33147061/32416807500),(447817/2401245000),(-34035467/32416807500),(-29804711/64833615000)],[(-58/108056025),(-8/3274425),(-2/480249),(-64/21611205),(-2/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac07Coeffs_correct : widthCoefficients 4 false 7 = vac07Coeffs := by
  rw [widthCoefficients,vac07Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
