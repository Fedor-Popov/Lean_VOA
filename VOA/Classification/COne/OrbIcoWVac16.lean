import VOA.Classification.COne.OrbIcoWVac15

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac16Rows00 := jetRows 3 false 16 0
theorem vac16Rows00_correct : jetRows 3 false 16 0 = vac16Rows00 := rfl
def vac16Row01 : List Jet := [[(10/3),(-11/3),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac16Rows01 : List (List Jet) := vac16Rows00 ++ [vac16Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows01_correct : jetRows 3 false 16 1 = vac16Rows01 := by
  rw [jetRows, vac16Rows00_correct]
  change vac16Rows00 ++ [jetStep 3 false 16 1 vac16Rows00] = vac16Rows00 ++ [vac16Row01]
  congr 1
  decide +kernel
def vac16Row02 : List Jet := [[(91/33),(-731/66),(43/6),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac16Rows02 : List (List Jet) := vac16Rows01 ++ [vac16Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows02_correct : jetRows 3 false 16 2 = vac16Rows02 := by
  rw [jetRows, vac16Rows01_correct]
  change vac16Rows01 ++ [jetStep 3 false 16 2 vac16Rows01] = vac16Rows01 ++ [vac16Row02]
  congr 1
  decide +kernel
def vac16Row03 : List Jet := [[(-476/495),(-287/45),(3871/198),(-301/30)],[(-17/99),(17/990),(17/90),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac16Rows03 : List (List Jet) := vac16Rows02 ++ [vac16Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows03_correct : jetRows 3 false 16 3 = vac16Rows03 := by
  rw [jetRows, vac16Rows02_correct]
  change vac16Rows02 ++ [jetStep 3 false 16 3 vac16Rows02] = vac16Rows02 ++ [vac16Row03]
  congr 1
  decide +kernel
def vac16Row04 : List Jet := [[(-3437/4455),(7451/1188),(7817/1320),(-440057/17820)],[(-157/891),(1451/2970),(713/2970),(-172/405)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac16Rows04 : List (List Jet) := vac16Rows03 ++ [vac16Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows04_correct : jetRows 3 false 16 4 = vac16Rows04 := by
  rw [jetRows, vac16Rows03_correct]
  change vac16Rows03 ++ [jetStep 3 false 16 4 vac16Rows03] = vac16Rows03 ++ [vac16Row04]
  congr 1
  decide +kernel
def vac16Row05 : List Jet := [[(24346/22275),(39641/44550),(-119381/7425),(4757/178200)],[(2513/59400),(68243/118800),(-1043/1200),(-7609/10800)],[(1/180),(1/200),(-1/150),(-11/1800)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac16Rows05 : List (List Jet) := vac16Rows04 ++ [vac16Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows05_correct : jetRows 3 false 16 5 = vac16Rows05 := by
  rw [jetRows, vac16Rows04_correct]
  change vac16Rows04 ++ [jetStep 3 false 16 5 vac16Rows04] = vac16Rows04 ++ [vac16Row05]
  congr 1
  decide +kernel
def vac16Row06 : List Jet := [[(-5299/13365),(-129109/24300),(2212307/623700),(198910051/7484400)],[(651857/7484400),(-4920191/14968800),(-503047/415800),(59441/42768)],[(499/68040),(-84649/7484400),(-70487/2494800),(10117/1496880)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac16Rows06 : List (List Jet) := vac16Rows05 ++ [vac16Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows06_correct : jetRows 3 false 16 6 = vac16Rows06 := by
  rw [jetRows, vac16Rows05_correct]
  change vac16Rows05 ++ [jetStep 3 false 16 6 vac16Rows05] = vac16Rows05 ++ [vac16Row06]
  congr 1
  decide +kernel
def vac16Row07 : List Jet := [[(-89812/200475),(1024514/280665),(501615941/39293100),(-115062449/7858620)],[(-519163/6286896),(-122873251/314344800),(44669021/39293100),(33885389/15717240)],[(-3679/7484400),(-154493/4989600),(2173/267300),(555521/7484400)],[(-281/1746360),(-5339/17463600),(281/5821200),(6463/17463600)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac16Rows07 : List (List Jet) := vac16Rows06 ++ [vac16Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows07_correct : jetRows 3 false 16 7 = vac16Rows07 := by
  rw [jetRows, vac16Rows06_correct]
  change vac16Rows06 ++ [jetStep 3 false 16 7 vac16Rows06] = vac16Rows06 ++ [vac16Row07]
  congr 1
  decide +kernel
def vac16Row08 : List Jet := [[(133331/182250),(1001381/623700),(-7215389051/523908000),(-4393767029/196465500)],[(-317971/16765056),(160128901/279417600),(301545539/279417600),(-541939973/190512000)],[(-298589/49896000),(962107/299376000),(2558191/27216000),(2055749/149688000)],[(-7627/26195400),(24307/261954000),(6791/4762800),(211973/261954000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac16Rows08 : List (List Jet) := vac16Rows07 ++ [vac16Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows08_correct : jetRows 3 false 16 8 = vac16Rows08 := by
  rw [jetRows, vac16Rows07_correct]
  change vac16Rows07 ++ [jetStep 3 false 16 8 vac16Rows07] = vac16Rows07 ++ [vac16Row08]
  congr 1
  decide +kernel
def vac16Row09 : List Jet := [[(-2386349/9021375),(-14783884/3007125),(-168390589/48114000),(498862448473/14145516000)],[(2211689773/22632825600),(16843723/195955200),(-16928736761/7544275200),(-85566783517/32332608000)],[(77578703/28291032000),(819659399/18860688000),(-45774523/18860688000),(-7242263561/28291032000)],[(-4063/53887680),(372989/244944000),(4121951/2694384000),(-1655299/449064000)],[(667/125737920),(19343/1257379200),(667/78586200),(-8671/628689600)],[0,0,0,0],[0,0,0,0]]
def vac16Rows09 : List (List Jet) := vac16Rows08 ++ [vac16Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows09_correct : jetRows 3 false 16 9 = vac16Rows09 := by
  rw [jetRows, vac16Rows08_correct]
  change vac16Rows08 ++ [jetStep 3 false 16 9 vac16Rows08] = vac16Rows08 ++ [vac16Row09]
  congr 1
  decide +kernel
def vac16Row10 : List Jet := [[(-129910739/270641250),(500054371/270641250),(198718340827/10103940000),(141748637363/12124728000)],[(-148599196973/3394923840000),(-5744717164831/6789847680000),(-1259645865641/2263282560000),(863155861639/123451776000)],[(10787551/1508855040),(-822755699/45265651200),(-3993497447/18860688000),(-2926062401/53887680000)],[(55258603/141455160000),(338681869/282910320000),(-536259149/94303440000),(-27483691/2886840000)],[(283873/18860688000),(859409/62868960000),(-4242691/62868960000),(-9959981/94303440000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac16Rows10 : List (List Jet) := vac16Rows09 ++ [vac16Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows10_correct : jetRows 3 false 16 10 = vac16Rows10 := by
  rw [jetRows, vac16Rows09_correct]
  change vac16Rows09 ++ [jetStep 3 false 16 10 vac16Rows09] = vac16Rows09 ++ [vac16Row10]
  congr 1
  decide +kernel
def vac16Row11 : List Jet := [[(29456882/59541075),(16047592463/2977053750),(-138019083011/83357505000),(-158631489592489/2334010140000)],[(-1509840027779/12448054080000),(4362047815943/24896108160000),(5760800056447/1185528960000),(129276723522313/24896108160000)],[(-17126334839/2489610816000),(-475182956333/4979221632000),(89147167079/4979221632000),(3383053552037/3556586880000)],[(399898721/1556006760000),(-12095265067/3112013520000),(-214738219/17681895000),(55697401259/3112013520000)],[(516319/29638224000),(-28767379/296382240000),(-72139/263450880),(14258749/148191120000)],[(-793/2766234240),(-10309/9220780800),(-793/614718720),(793/2766234240)],[0,0,0,0]]
def vac16Rows11 : List (List Jet) := vac16Rows10 ++ [vac16Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows11_correct : jetRows 3 false 16 11 = vac16Rows11 := by
  rw [jetRows, vac16Rows10_correct]
  change vac16Rows10 ++ [jetStep 3 false 16 11 vac16Rows10] = vac16Rows10 ++ [vac16Row11]
  congr 1
  decide +kernel
def vac16Row12 : List Jet := [[(8293549691/8931161250),(15732230257/35724645000),(-46337398901557/1000290060000),(-77279623599781/800232048000)],[(489627683819/12803712768000),(3924330000743/1662819840000),(325684198116553/64018563840000),(-832302276436823/32009281920000)],[(-2766556873613/112032486720000),(1332127522213/224064973440000),(232792076096291/224064973440000),(283136927930041/224064973440000)],[(-2665086233/2133952128000),(-1644798819773/149376648960000),(1138894141411/49792216320000),(2790972516701/21339521280000)],[(-1018675741/37344162240000),(-217698457/452656512000),(1398207233/7468832448000),(41550558211/14937664896000)],[(-1291517/622402704000),(-3998609/889146720000),(1525759/296382240000),(261281/12702096000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac16Rows12 : List (List Jet) := vac16Rows11 ++ [vac16Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Rows12_correct : jetRows 3 false 16 12 = vac16Rows12 := by
  rw [jetRows, vac16Rows11_correct]
  change vac16Rows11 ++ [jetStep 3 false 16 12 vac16Rows11] = vac16Rows11 ++ [vac16Row12]
  congr 1
  decide +kernel
def vac16Coeffs : List Jet := [[(-100644832624/4465580625),(406428728692/4465580625),(6046845393653/4465580625),(-81639494838599/125036257500)],[(-126179963938487/44812994688000),(-4996305960940979/89625989376000),(4072608238430701/44812994688000),(1087447562748287/1120324867200)],[(172240857377/424365480000),(-79219483244393/18672081120000),(-288400384053343/12448054080000),(2214269686481659/37344162240000)],[(382579810133/9336040560000),(627324766951/18672081120000),(-10815390386803/6224027040000),(-4854372320731/18672081120000)],[(1032662447/583502535000),(2686016017/389001690000),(-618390694/10419688125),(-2519982347/106091370000)],[(11287/132313500),(-1135819/9261945000),(-13931/20582100),(-455347/9261945000)],[(-8/21611205),(-52/36018675),(-4/2401245),(8/21611205)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac16Coeffs_correct : widthCoefficients 3 false 16 = vac16Coeffs := by
  rw [widthCoefficients,vac16Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
