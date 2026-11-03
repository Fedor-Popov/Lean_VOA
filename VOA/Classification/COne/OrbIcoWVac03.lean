import VOA.Classification.COne.OrbIcoWVac02

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac03Rows00 := jetRows 4 false 3 0
theorem vac03Rows00_correct : jetRows 4 false 3 0 = vac03Rows00 := rfl
def vac03Row01 : List Jet := [[(11/2),(-3/2),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows01 : List (List Jet) := vac03Rows00 ++ [vac03Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows01_correct : jetRows 4 false 3 1 = vac03Rows01 := by
  rw [jetRows, vac03Rows00_correct]
  change vac03Rows00 ++ [jetStep 4 false 3 1 vac03Rows00] = vac03Rows00 ++ [vac03Row01]
  congr 1
  decide +kernel
def vac03Row02 : List Jet := [[(533/44),(-85/11),(51/44),0,0],[(-1/22),(-1/22),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows02 : List (List Jet) := vac03Rows01 ++ [vac03Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows02_correct : jetRows 4 false 3 2 = vac03Rows02 := by
  rw [jetRows, vac03Rows01_correct]
  change vac03Rows01 ++ [jetStep 4 false 3 2 vac03Rows01] = vac03Rows01 ++ [vac03Row02]
  congr 1
  decide +kernel
def vac03Row03 : List Jet := [[(1739/132),(-1717/110),(739/132),(-34/55),0],[(-17/60),(-34/165),(17/220),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows03 : List (List Jet) := vac03Rows02 ++ [vac03Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows03_correct : jetRows 4 false 3 3 = vac03Rows03 := by
  rw [jetRows, vac03Rows02_correct]
  change vac03Rows02 ++ [jetStep 4 false 3 3 vac03Rows02] = vac03Rows02 ++ [vac03Row03]
  congr 1
  decide +kernel
def vac03Row04 : List Jet := [[(10547/1584),(-118031/7920),(16429/1584),(-22249/7920),(17/66)],[(-2183/2970),(-811/2970),(584/1485),(-34/495),0],[(1/792),(1/396),(1/792),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows04 : List (List Jet) := vac03Rows03 ++ [vac03Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows04_correct : jetRows 4 false 3 4 = vac03Rows04 := by
  rw [jetRows, vac03Rows03_correct]
  change vac03Rows03 ++ [jetStep 4 false 3 4 vac03Rows03] = vac03Rows03 ++ [vac03Row04]
  congr 1
  decide +kernel
def vac03Row05 : List Jet := [[(4151/6336),(-5663/990),(45563/5280),(-18991/3960),(35147/31680)],[(-119527/118800),(5371/39600),(29489/39600),(-42073/118800),(17/396)],[(11/1200),(19/1200),(1/240),(-1/400),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows05 : List (List Jet) := vac03Rows04 ++ [vac03Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows05_correct : jetRows 4 false 3 5 = vac03Rows05 := by
  rw [jetRows, vac03Rows04_correct]
  change vac03Rows04 ++ [jetStep 4 false 3 5 vac03Rows04] = vac03Rows04 ++ [vac03Row05]
  congr 1
  decide +kernel
def vac03Row06 : List Jet := [[(-121735/266112),(617857/1330560),(1507619/665280),(-463721/133056),(2354389/1330560)],[(-462031/623700),(609247/831600),(436633/831600),(-1759111/2494800),(36887/166320)],[(144983/4989600),(33379/831600),(-883/207900),(-31637/2494800),(629/237600)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows06 : List (List Jet) := vac03Rows05 ++ [vac03Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows06_correct : jetRows 4 false 3 6 = vac03Rows06 := by
  rw [jetRows, vac03Rows05_correct]
  change vac03Rows05 ++ [jetStep 4 false 3 6 vac03Rows05] = vac03Rows05 ++ [vac03Row06]
  congr 1
  decide +kernel
def vac03Row07 : List Jet := [[(98185/1862784),(196563/344960),(-662903/776160),(-268561/517440),(3593323/3104640)],[(-2774903/11975040),(6559559/8553600),(-1871627/9979200),(-18277169/29937600),(2470327/5443200)],[(2759341/52390800),(505343/10478160),(-246409/5821200),(-1084529/52390800),(39707/2619540)],[(-281/1058400),(-281/388080),(-281/485100),(-281/5821200),(281/3880800)],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows07 : List (List Jet) := vac03Rows06 ++ [vac03Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows07_correct : jetRows 4 false 3 7 = vac03Rows07 := by
  rw [jetRows, vac03Rows06_correct]
  change vac03Rows06 ++ [jetStep 4 false 3 7 vac03Rows06] = vac03Rows06 ++ [vac03Row07]
  congr 1
  decide +kernel
def vac03Row08 : List Jet := [[(806567/14902272),(-6416503/37255680),(-914563/2759680),(351517/627200),(1128663/13798400)],[(42734189/1197504000),(85891189/299376000),(-646961659/1197504000),(-8216501/149688000),(3001153/6842880)],[(2627671/43659000),(4818421/349272000),(-313111/3492720),(412961/87318000),(5928611/174636000)],[(-95567/87318000),(-228593/87318000),(-13427/9702000),(53359/87318000),(3271/8731800)],[(1/1330560),(1/332640),(1/221760),(1/332640),(1/1330560)],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows08 : List (List Jet) := vac03Rows07 ++ [vac03Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows08_correct : jetRows 4 false 3 8 = vac03Rows08 := by
  rw [jetRows, vac03Rows07_correct]
  change vac03Rows07 ++ [jetStep 4 false 3 8 vac03Rows07] = vac03Rows07 ++ [vac03Row08]
  congr 1
  decide +kernel
def vac03Row09 : List Jet := [[(-398491/24385536),(-4648937/63866880),(191197333/1341204480),(423273377/2235340800),(-82381633/319334400)],[(808725601/18860688000),(-4276718563/75442752000),(-147504977/471517200),(26166351901/75442752000),(2475989297/18860688000)],[(98407651/2155507200),(-230064133/5388768000),(-995344327/10777536000),(38061049/538876800),(322947937/10777536000)],[(-7775923/2694384000),(-107126207/18860688000),(-6509483/9430344000),(6126233/1886068800),(646421/1714608000)],[(667/76204800),(27347/838252800),(667/15523200),(8671/419126400),(-667/838252800)],[0,0,0,0,0],[0,0,0,0,0]]
def vac03Rows09 : List (List Jet) := vac03Rows08 ++ [vac03Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows09_correct : jetRows 4 false 3 9 = vac03Rows09 := by
  rw [jetRows, vac03Rows08_correct]
  change vac03Rows08 ++ [jetStep 4 false 3 9 vac03Rows08] = vac03Rows08 ++ [vac03Row09]
  congr 1
  decide +kernel
def vac03Row10 : List Jet := [[(-2812441/536481792),(844379/447068160),(27209773/335301120),(-3168247/186278400),(-72775919/447068160)],[(2716641607/411505920000),(-152088382949/1508855040000),(-45666364493/1508855040000),(1657514542813/4526565120000),(-267180272531/1508855040000)],[(2873541647/113164128000),(-10477304191/125737920000),(-1710162763/47151720000),(22579455841/161663040000),(-4883053787/188606880000)],[(-1113826991/188606880000),(-794516071/94303440000),(959899271/188606880000),(11310067/1428840000),(-481069649/188606880000)],[(6723811/125737920000),(17881/98232750),(24889063/125737920000),(644459/15717240000),(-5847727/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680),(-1/7983360)],[0,0,0,0,0]]
def vac03Rows10 : List (List Jet) := vac03Rows09 ++ [vac03Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows10_correct : jetRows 4 false 3 10 = vac03Rows10 := by
  rw [jetRows, vac03Rows09_correct]
  change vac03Rows09 ++ [jetStep 4 false 3 10 vac03Rows09] = vac03Rows09 ++ [vac03Row10]
  congr 1
  decide +kernel
def vac03Row11 : List Jet := [[(-35649731/5901299712),(-32588251/7376624640),(1293817703/14753249280),(-2618486777/73766246400),(-1064719529/6147187200)],[(-42152158907/99584432640000),(-4629410826679/49792216320000),(670168261747/8298702720000),(4483096765129/12448054080000),(-21722914867901/49792216320000)],[(28406544073/1659740544000),(-259148965469/2074675680000),(19690598927/345779280000),(62529502747/296382240000),(-61724509213/377213760000)],[(-2900154319/237105792000),(-11336949821/1185528960000),(9033115391/395176320000),(1268614201/107775360000),(-18273135961/1185528960000)],[(154238551/592764480000),(20166323/25613280000),(865998137/1383117120000),(-179167327/1037337840000),(-432059939/1383117120000)],[(-793/1676505600),(-10309/4610390400),(-15067/3688312320),(-793/230519520),(-793/737662464)],[0,0,0,0,0]]
def vac03Rows11 : List (List Jet) := vac03Rows10 ++ [vac03Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows11_correct : jetRows 4 false 3 11 = vac03Rows11 := by
  rw [jetRows, vac03Rows10_correct]
  change vac03Rows10 ++ [jetStep 4 false 3 11 vac03Rows10] = vac03Rows10 ++ [vac03Row11]
  congr 1
  decide +kernel
def vac03Row12 : List Jet := [[(-19296229/919683072),(-14879251/2408693760),(7866970117/25291284480),(-3719339083/21076070400),(-74410077253/126456422400)],[(116977592533/59750659584000),(-84932172334927/298753297920000),(31388397886049/99584432640000),(155988026913707/149376648960000),(-17758232253401/10669760640000)],[(25924170905243/597506595840000),(-5805474350419/14937664896000),(5253362405531/14226347520000),(167768926853909/298753297920000),(-140918183537/176359680000)],[(-13213837157093/298753297920000),(-1339552406587/149376648960000),(5372552507621/49792216320000),(455164718017/149376648960000),(-6201378472519/74688324480000)],[(80430898433/49792216320000),(210722647591/49792216320000),(6223029143/3319481088000),(-136742224313/49792216320000),(-80176781557/49792216320000)],[(-1298417/188606880000),(-429401/14113440000),(-271277/5488560000),(-939641/29638224000),(-701/6586272000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080),(1/31933440)]]
def vac03Rows12 : List (List Jet) := vac03Rows11 ++ [vac03Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Rows12_correct : jetRows 4 false 3 12 = vac03Rows12 := by
  rw [jetRows, vac03Rows11_correct]
  change vac03Rows11 ++ [jetStep 4 false 3 12 vac03Rows11] = vac03Rows11 ++ [vac03Row12]
  congr 1
  decide +kernel
def vac03Coeffs : List Jet := [[(14726976475/11802599424),(-3785450975/3934199808),(-103523457145/5901299712),(29211874871/983549952),(90016646639/21076070400)],[(-19041775306849/149376648960000),(612412392159899/37344162240000),(-14158177088591/389001690000),(-154989964435423/7468832448000),(9224908519327307/74688324480000)],[(-177043405242923/74688324480000),(1785071382883693/74688324480000),(-602147691296609/12448054080000),(831063709826689/37344162240000),(515404336730123/18672081120000)],[(828348946231/345779280000),(-3333489982063/1244805408000),(-7085364081151/2074675680000),(10422519888371/2074675680000),(-194306849171/565820640000)],[(-1156957559/11114334000),(-7407899351/55571670000),(1977773339/18523890000),(6476155663/55571670000),(-3796657243/55571670000)],[(6326543/9261945000),(545509/257276250),(5646013/3087315000),(-564173/2315486250),(-2356561/3087315000)],[(-2/3274425),(-104/36018675),(-38/7203735),(-32/7203735),(-2/1440747)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac03Coeffs_correct : widthCoefficients 4 false 3 = vac03Coeffs := by
  rw [widthCoefficients,vac03Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
