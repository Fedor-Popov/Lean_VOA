import VOA.Classification.COne.OrbIcoWVac04

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac05Rows00 := jetRows 4 false 5 0
theorem vac05Rows00_correct : jetRows 4 false 5 0 = vac05Rows00 := rfl
def vac05Row01 : List Jet := [[(31/6),(-11/6),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows01 : List (List Jet) := vac05Rows00 ++ [vac05Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows01_correct : jetRows 4 false 5 1 = vac05Rows01 := by
  rw [jetRows, vac05Rows00_correct]
  change vac05Rows00 ++ [jetStep 4 false 5 1 vac05Rows00] = vac05Rows00 ++ [vac05Row01]
  congr 1
  decide +kernel
def vac05Row02 : List Jet := [[(455/44),(-98/11),(7/4),0,0],[(-1/22),(-1/22),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows02 : List (List Jet) := vac05Rows01 ++ [vac05Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows02_correct : jetRows 4 false 5 2 = vac05Rows02 := by
  rw [jetRows, vac05Rows01_correct]
  change vac05Rows01 ++ [jetStep 4 false 5 2 vac05Rows01] = vac05Rows01 ++ [vac05Row02]
  congr 1
  decide +kernel
def vac05Row03 : List Jet := [[(417/44),(-49/3),(353/44),(-7/6),0],[(-527/1980),(-17/99),(17/180),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows03 : List (List Jet) := vac05Rows02 ++ [vac05Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows03_correct : jetRows 4 false 5 3 = vac05Rows03 := by
  rw [jetRows, vac05Rows02_correct]
  change vac05Rows02 ++ [jetStep 4 false 5 3 vac05Rows02] = vac05Rows02 ++ [vac05Row03]
  congr 1
  decide +kernel
def vac05Row04 : List Jet := [[(535/176),(-60715/4752),(64109/4752),(-24125/4752),(133/216)],[(-623/990),(-287/2970),(637/1485),(-14/135),0],[(1/792),(1/396),(1/792),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows04 : List (List Jet) := vac05Rows03 ++ [vac05Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows04_correct : jetRows 4 false 5 4 = vac05Rows04 := by
  rw [jetRows, vac05Rows03_correct]
  change vac05Rows03 ++ [jetStep 4 false 5 4 vac05Rows03] = vac05Rows03 ++ [vac05Row04]
  congr 1
  decide +kernel
def vac05Row05 : List Jet := [[(-2439/3520),(-33631/15840),(27985/3168),(-6247/792),(81461/31680)],[(-14599/19800),(55021/118800),(2273/3600),(-1757/3600),(35/432)],[(31/3600),(17/1200),(1/400),(-11/3600),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows05 : List (List Jet) := vac05Rows04 ++ [vac05Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows05_correct : jetRows 4 false 5 5 = vac05Rows05 := by
  rw [jetRows, vac05Rows04_correct]
  change vac05Rows04 ++ [jetStep 4 false 5 5 vac05Rows04] = vac05Rows04 ++ [vac05Row05]
  congr 1
  decide +kernel
def vac05Row06 : List Jet := [[(-10831/49280),(76381/40320),(-16813/110880),(-27013/6336),(238187/63360)],[(-128629/332640),(4593101/4989600),(11527/178200),(-111301/138600),(1936919/4989600)],[(539/21600),(10399/356400),(-743/59400),(-1513/118800),(259/64800)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows06 : List (List Jet) := vac05Rows05 ++ [vac05Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows06_correct : jetRows 4 false 5 6 = vac05Rows06 := by
  rw [jetRows, vac05Rows05_correct]
  change vac05Rows05 ++ [jetStep 4 false 5 6 vac05Rows05] = vac05Rows05 ++ [vac05Row06]
  congr 1
  decide +kernel
def vac05Row07 : List Jet := [[(48061/206976),(-13963/9313920),(-2329361/1164240),(4929643/4656960),(151405/88704)],[(229609/46569600),(8880569/15523200),(-846247/1164240),(-7861103/23284800),(31407661/46569600)],[(39229/997920),(273697/14968800),(-25174/467775),(-11321/1247400),(297613/14968800)],[(-8711/34927200),(-11521/17463600),(-281/582120),(281/17463600),(281/3175200)],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows07 : List (List Jet) := vac05Rows06 ++ [vac05Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows07_correct : jetRows 4 false 5 7 = vac05Rows07 := by
  rw [jetRows, vac05Rows06_correct]
  change vac05Rows06 ++ [jetStep 4 false 5 7 vac05Rows06] = vac05Rows06 ++ [vac05Row07]
  congr 1
  decide +kernel
def vac05Row08 : List Jet := [[(-8061/250880),(-418225/827904),(173949/551936),(1206329/827904),(-22626397/24837120)],[(72701801/931392000),(-7337219/116424000),(-27796799/44352000),(232243/441000),(115259689/310464000)],[(99391/2851200),(-832043/29937600),(-59581/777600),(78343/1871100),(374113/11975040)],[(-1307/1386000),(-5143/2494800),(-109/162000),(3827/4158000),(256/779625)],[(1/1330560),(1/332640),(1/221760),(1/332640),(1/1330560)],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows08 : List (List Jet) := vac05Rows07 ++ [vac05Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows08_correct : jetRows 4 false 5 8 = vac05Rows08 := by
  rw [jetRows, vac05Rows07_correct]
  change vac05Rows07 ++ [jetStep 4 false 5 8 vac05Rows07] = vac05Rows07 ++ [vac05Row08]
  congr 1
  decide +kernel
def vac05Row09 : List Jet := [[(-7747/157696),(75017/788480),(617857/1013760),(-6211241/21288960),(-64182691/63866880)],[(-21109723/8382528000),(-20119181/95256000),(94910477/1676505600),(352817803/523908000),(-606657133/1676505600)],[(70791071/5029516800),(-494072197/7544275200),(-52408879/2155507200),(420011881/3772137600),(-16445311/1371686400)],[(-6898139/3143448000),(-1173131/342921600),(28635791/18860688000),(31346939/9430344000),(-2030663/4715172000)],[(20677/2514758400),(75371/2514758400),(47357/1257379200),(19343/1257379200),(-8671/2514758400)],[0,0,0,0,0],[0,0,0,0,0]]
def vac05Rows09 : List (List Jet) := vac05Rows08 ++ [vac05Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows09_correct : jetRows 4 false 5 9 = vac05Rows09 := by
  rw [jetRows, vac05Rows08_correct]
  change vac05Rows08 ++ [jetStep 4 false 5 9 vac05Rows08] = vac05Rows08 ++ [vac05Row09]
  congr 1
  decide +kernel
def vac05Row10 : List Jet := [[(1335197/165580800),(10573751/82790400),(1887703/186278400),(-879941/1397088),(-311371387/6706022400)],[(-4634966827/167650560000),(-6726674953/167650560000),(20666062649/55883520000),(628606547/5080320000),(-42518029117/55883520000)],[(-1511318461/377213760000),(-16551410213/282910320000),(29532314921/377213760000),(2322497311/20956320000),(-143509141609/1131641280000)],[(-573557/153964800),(-137320069/56582064000),(34943189/4191264000),(41505899/9430344000),(-614683309/113164128000)],[(276893/5987520000),(95083/641520000),(2466839/17962560000),(-4447/561330000),(-1064891/17962560000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680),(-1/7983360)],[0,0,0,0,0]]
def vac05Rows10 : List (List Jet) := vac05Rows09 ++ [vac05Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows10_correct : jetRows 4 false 5 10 = vac05Rows10 := by
  rw [jetRows, vac05Rows09_correct]
  change vac05Rows09 ++ [jetStep 4 false 5 10 vac05Rows09] = vac05Rows09 ++ [vac05Row10]
  congr 1
  decide +kernel
def vac05Row11 : List Jet := [[(4026119/607129600),(4648909/60712960),(-333619619/2732083200),(-4341856487/8196249600),(5615259493/12294374400)],[(-1857226829/105380352000),(17243851937/263450880000),(45915280259/131725440000),(-9370238071/21954240000),(-22455647839/29272320000)],[(-6152222093/518668920000),(-88361591081/3112013520000),(579009292087/3112013520000),(-177832997/32416807500),(-452425870181/1556006760000)],[(-3271573471/553246848000),(6386488921/1659740544000),(19191821/914457600),(-29052229/5269017600),(-30810654367/1659740544000)],[(279190801/1383117120000),(1113574639/2074675680000),(333851911/1383117120000),(-43759663/115259760000),(-1088997347/4149351360000)],[(-24583/55324684800),(-793/384199200),(-13481/3688312320),(-793/276623424),(-793/1229437440)],[0,0,0,0,0]]
def vac05Rows11 : List (List Jet) := vac05Rows10 ++ [vac05Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows11_correct : jetRows 4 false 5 11 = vac05Rows11 := by
  rw [jetRows, vac05Rows10_correct]
  change vac05Rows10 ++ [jetStep 4 false 5 11 vac05Rows10] = vac05Rows10 ++ [vac05Row11]
  congr 1
  decide +kernel
def vac05Row12 : List Jet := [[(9742119/485703680),(579922337/2428518400),(-231727729/546416640),(-1524756953/1024531200),(185012637917/98354995200)],[(-427950965839/11064936960000),(2024230937/10264320000),(2075499325399/2766234240000),(-1337452735561/790352640000),(-1898743810429/1383117120000)],[(-1161572714767/39833773056000),(-400416337621/37344162240000),(161530961443573/298753297920000),(-44338086229499/99584432640000),(-58708459708999/74688324480000)],[(-1618341820253/99584432640000),(139420043219/4267904256000),(8846177363299/149376648960000),(-540643974847/7113173760000),(-399506540507/7468832448000)],[(10957307839/9958443264000),(30418605881/13579695360000),(-85262138279/149376648960000),(-154092476383/49792216320000),(-50706672901/149376648960000)],[(-590981/98794080000),(-7498201/296382240000),(-103237/2744280000),(-177599/9879408000),(454613/59276448000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080),(1/31933440)]]
def vac05Rows12 : List (List Jet) := vac05Rows11 ++ [vac05Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Rows12_correct : jetRows 4 false 5 12 = vac05Rows12 := by
  rw [jetRows, vac05Rows11_correct]
  change vac05Rows11 ++ [jetStep 4 false 5 12 vac05Rows11] = vac05Rows11 ++ [vac05Row12]
  congr 1
  decide +kernel
def vac05Coeffs : List Jet := [[(-267709689/242851840),(-2854073703/242851840),(1465924093/39029760),(16371155767/409812480),(-1557781848319/9835499520)],[(1898750678411/922078080000),(-4633594114339/368831232000),(-22335764603813/922078080000),(27862544915383/230519520000),(-62011461979/873180000)],[(3612003943/2586608640),(-600625427029/426790425600),(-5334371693681/213395212800),(20066814880109/355658688000),(-13606202481253/533488032000)],[(1186397648917/1556006760000),(-51837432275857/18672081120000),(1744615640687/2667440160000),(28406897346337/6224027040000),(-66268389672239/18672081120000)],[(-16385810051/259334460000),(-12529401497/389001690000),(17705161351/129667230000),(58516471/1683990000),(-19944057953/194500845000)],[(1469746/2701400625),(98393329/64833615000),(4783187/5402801250),(-5658811/7203735000),(-5552462/8104201875)],[(-62/108056025),(-32/12006225),(-34/7203735),(-16/4322241),(-2/2401245)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac05Coeffs_correct : widthCoefficients 4 false 5 = vac05Coeffs := by
  rw [widthCoefficients,vac05Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
