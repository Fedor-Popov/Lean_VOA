import VOA.Classification.COne.OrbIcoWVac01

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac02Rows00 := jetRows 5 false 2 0
theorem vac02Rows00_correct : jetRows 5 false 2 0 = vac02Rows00 := rfl
def vac02Row01 : List Jet := [[(17/3),(-4/3),0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows01 : List (List Jet) := vac02Rows00 ++ [vac02Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows01_correct : jetRows 5 false 2 1 = vac02Rows01 := by
  rw [jetRows, vac02Rows00_correct]
  change vac02Rows00 ++ [jetStep 5 false 2 1 vac02Rows00] = vac02Rows00 ++ [vac02Row01]
  congr 1
  decide +kernel
def vac02Row02 : List Jet := [[(287/22),(-155/22),(10/11),0,0,0],[(-1/22),(-1/22),0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows02 : List (List Jet) := vac02Rows01 ++ [vac02Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows02_correct : jetRows 5 false 2 2 = vac02Rows02 := by
  rw [jetRows, vac02Rows01_correct]
  change vac02Rows01 ++ [jetStep 5 false 2 2 vac02Rows01] = vac02Rows01 ++ [vac02Row02]
  congr 1
  decide +kernel
def vac02Row03 : List Jet := [[(168/11),(-1631/110),(1477/330),(-14/33),0,0],[(-289/990),(-221/990),(34/495),0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows03 : List (List Jet) := vac02Rows02 ++ [vac02Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows03_correct : jetRows 5 false 2 3 = vac02Rows03 := by
  rw [jetRows, vac02Rows02_correct]
  change vac02Rows02 ++ [jetStep 5 false 2 3 vac02Rows02] = vac02Rows02 ++ [vac02Row03]
  congr 1
  decide +kernel
def vac02Row04 : List Jet := [[(595/66),(-6729/440),(12757/1485),(-23141/11880),(91/594),0],[(-1174/1485),(-1097/2970),(1091/2970),(-16/297),0,0],[(1/792),(1/396),(1/792),0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows04 : List (List Jet) := vac02Rows03 ++ [vac02Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows04_correct : jetRows 5 false 2 4 = vac02Rows04 := by
  rw [jetRows, vac02Rows03_correct]
  change vac02Rows03 ++ [jetStep 5 false 2 4 vac02Rows03] = vac02Rows03 ++ [vac02Row04]
  congr 1
  decide +kernel
def vac02Row05 : List Jet := [[(21/11),(-6363/880),(102197/13200),(-135173/39600),(2371/3600),(-91/1980)],[(-27517/23760),(-8953/118800),(3367/4400),(-34223/118800),(35/1188),0],[(17/1800),(1/60),(1/200),(-1/450),0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows05 : List (List Jet) := vac02Rows04 ++ [vac02Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows05_correct : jetRows 5 false 2 5 = vac02Rows05 := by
  rw [jetRows, vac02Rows04_correct]
  change vac02Rows04 ++ [jetStep 5 false 2 5 vac02Rows04] = vac02Rows04 ++ [vac02Row05]
  congr 1
  decide +kernel
def vac02Row06 : List Jet := [[(-7/22),(-3077/5280),(193217/69300),(-446741/166320),(147263/138600),(-103517/554400)],[(-964699/997920),(658873/1247400),(1773379/2494800),(-2741/4455),(778609/4989600),(-91/7128)],[(7079/226800),(22969/498960),(421/831600),(-30533/2494800),(37/17820),0],[(-1/33264),(-1/11088),(-1/11088),(-1/33264),0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows06 : List (List Jet) := vac02Rows05 ++ [vac02Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows06_correct : jetRows 5 false 2 6 = vac02Rows06 := by
  rw [jetRows, vac02Rows05_correct]
  change vac02Rows05 ++ [jetStep 5 false 2 6 vac02Rows05] = vac02Rows05 ++ [vac02Row06]
  congr 1
  decide +kernel
def vac02Row07 : List Jet := [[(-2/33),(13963/27720),(-2529941/11642400),(-12262573/17463600),(6512833/8731800),(-330229/1164240)],[(-2963987/6985440),(960283/1293600),(234617/1940400),(-2222753/3492720),(356537/1058400),(-788533/11642400)],[(180203/2993760),(5909/89100),(-22159/680400),(-92483/3742200),(62801/4989600),(-149/106920)],[(-4777/17463600),(-13207/17463600),(-3653/5821200),(-281/3492720),(281/4365900),0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows07 : List (List Jet) := vac02Rows06 ++ [vac02Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows07_correct : jetRows 5 false 2 7 = vac02Rows07 := by
  rw [jetRows, vac02Rows06_correct]
  change vac02Rows06 ++ [jetStep 5 false 2 7 vac02Rows06] = vac02Rows06 ++ [vac02Row07]
  congr 1
  decide +kernel
def vac02Row08 : List Jet := [[(1/22),(-71/7392),(-8847557/31046400),(91590563/465696000),(35514277/232848000),(-14869721/77616000)],[(-572105/11176704),(23687579/55883520),(-78327989/232848000),(-179967871/698544000),(47558393/127008000),(-70721143/465696000)],[(22762459/299376000),(1226621/27216000),(-12827597/149688000),(-654673/49896000),(379987/11975040),(-247883/27216000)],[(-6407/5457375),(-28283/9702000),(-155209/87318000),(7307/17463600),(11023/29106000),(-83/1091475)],[(1/1330560),(1/332640),(1/221760),(1/332640),(1/1330560),0],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows08 : List (List Jet) := vac02Rows07 ++ [vac02Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows08_correct : jetRows 5 false 2 8 = vac02Rows08 := by
  rw [jetRows, vac02Rows07_correct]
  change vac02Rows07 ++ [jetStep 5 false 2 8 vac02Rows07] = vac02Rows07 ++ [vac02Row08]
  congr 1
  decide +kernel
def vac02Row09 : List Jet := [[0,(-91/1980),(18877/1900800),(164995279/1397088000),(-13473577/209563200),(-107141701/2095632000)],[(6798503/201180672),(72679/855360),(-8204585773/25147584000),(4601947/42768000),(5438505161/25147584000),(-76463047/392931000)],[(325639931/4715172000),(-1498256/147349125),(-215991383/1886068800),(2233849/58212000),(191889707/4715172000),(-127233737/4715172000)],[(-1764229/538876800),(-18880091/2694384000),(-2898563/1347192000),(48529/16632000),(376823/538876800),(-139253/244944000)],[(11339/1257379200),(667/19646550),(28681/628689600),(667/28576800),(667/1257379200),(-667/314344800)],[0,0,0,0,0,0],[0,0,0,0,0,0]]
def vac02Rows09 : List (List Jet) := vac02Rows08 ++ [vac02Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows09_correct : jetRows 5 false 2 9 = vac02Rows09 := by
  rw [jetRows, vac02Rows08_correct]
  change vac02Rows08 ++ [jetStep 5 false 2 9 vac02Rows08] = vac02Rows08 ++ [vac02Row09]
  congr 1
  decide +kernel
def vac02Row10 : List Jet := [[0,(-127/11880),(1039387/79833600),(5443337/149688000),(-922984099/17962560000),(-33116443/8981280000)],[(40081427/2011806720),(-7248109/304819200),(-800120761/4572288000),(6468641659/27941760000),(1375855337/35925120000),(-4180165469/22861440000)],[(61540376287/1131641280000),(-37279138511/565820640000),(-12503834039/125737920000),(457259843/4041576000),(772289737/45265651200),(-3212058931/62868960000)],[(-409867879/56582064000),(-707127467/56582064000),(42291223/23575860000),(16036061/1837080000),(-268242299/282910320000),(-182889257/94303440000)],[(3600473/62868960000),(12574511/62868960000),(7259687/31434480000),(723641/10478160000),(-213881/5715360000),(-923141/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680),(-1/7983360),(-1/39916800)],[0,0,0,0,0,0]]
def vac02Rows10 : List (List Jet) := vac02Rows09 ++ [vac02Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows10_correct : jetRows 5 false 2 10 = vac02Rows10 := by
  rw [jetRows, vac02Rows09_correct]
  change vac02Rows09 ++ [jetStep 5 false 2 10 vac02Rows09] = vac02Rows09 ++ [vac02Row10]
  congr 1
  decide +kernel
def vac02Row11 : List Jet := [[0,(-19/990),(655477/36590400),(1616446781/30735936000),(-8291696711/115259760000),(353423579/153679680000)],[(35649731/2011806720),(-4301044441/110649369600),(-12590189251/79035264000),(927148633423/2766234240000),(-214908817667/2766234240000),(-595145551303/2766234240000)],[(1497494428583/24896108160000),(-377697269137/2766234240000),(-1803793174529/24896108160000),(165269427329/711317376000),(-2004129313/33872256000),(-2096183948107/24896108160000)],[(-6883631959/414935136000),(-4344843563/207467568000),(37238943229/2074675680000),(20106675121/1037337840000),(-22766370937/2074675680000),(-4072652009/1037337840000)],[(17354789/59276448000),(276236201/296382240000),(1184707/1372140000),(-2447171/148191120000),(-8264413/26943840000),(-631403/32931360000)],[(-13481/27662342400),(-793/341510400),(-793/184415616),(-10309/2766234240),(-793/614718720),(793/9220780800)],[0,0,0,0,0,0]]
def vac02Rows11 : List (List Jet) := vac02Rows10 ++ [vac02Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows11_correct : jetRows 5 false 2 11 = vac02Rows11 := by
  rw [jetRows, vac02Rows10_correct]
  change vac02Rows10 ++ [jetStep 5 false 2 11 vac02Rows10] = vac02Rows10 ++ [vac02Row11]
  congr 1
  decide +kernel
def vac02Row12 : List Jet := [[0,(-1/15),(7148783/97574400),(355740827/1951488000),(-479446021/1693440000),(60847893709/1844156160000)],[(19296229/313528320),(-27673511/205286400),(-15616422079/29638224000),(481570710581/395176320000),(-153321465301/338722560000),(-803799293711/1185528960000)],[(2817458012423/14937664896000),(-3176847670201/6224027040000),(-11892052741001/149376648960000),(25225755923171/29875329792000),(-19458391619/44259747840),(-1332419628949/5975065958400)],[(-201481049483/3048503040000),(-567422897423/9958443264000),(16082522984333/149376648960000),(1144662849401/21339521280000),(-413302465771/5532468480000),(-37626006559/29875329792000)],[(143772826073/74688324480000),(22853607479/4149351360000),(275306900941/74688324480000),(-74494582471/37344162240000),(-50998423151/24896108160000),(18777069373/37344162240000)],[(-3816133/518668920000),(-9822983/296382240000),(-1102433/19758816000),(-166577/4234032000),(-12851/2694384000),(635903/98794080000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080),(1/31933440),(1/79833600)]]
def vac02Rows12 : List (List Jet) := vac02Rows11 ++ [vac02Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Rows12_correct : jetRows 5 false 2 12 = vac02Rows12 := by
  rw [jetRows, vac02Rows11_correct]
  change vac02Rows11 ++ [jetStep 5 false 2 12 vac02Rows11] = vac02Rows11 ++ [vac02Row12]
  congr 1
  decide +kernel
def vac02Coeffs : List Jet := [[0,(91/22),(-772133/87120),(-212201281/97574400),(621381066161/30735936000),(-131898791603/5691840000)],[(-2945395295/804722688),(5522594579/461039040),(515084337151/27662342400),(-576714283247/6147187200),(352384805230663/2766234240000),(-41390430925913/461039040000)],[(-401043906315419/37344162240000),(515115684381677/12448054080000),(-61751847760069/1493766489600),(-54531842560133/7468832448000),(164900762325289/4149351360000),(-231302678223787/7468832448000)],[(35396755171081/9336040560000),(-2930873079263/2074675680000),(-104164064195561/18672081120000),(14502060593417/3734416224000),(1447035180821/1244805408000),(-38095244452513/18672081120000)],[(-8464404677/64833615000),(-80943087121/389001690000),(1638850529/27785835000),(6327987299/43222410000),(-7888382503/194500845000),(-11903810251/389001690000)],[(1408079/1852389000),(2853742/1157743125),(2470823/1029105000),(337697/2315486250),(-6786023/9261945000),(-152/2041875)],[(-68/108056025),(-4/1334025),(-8/1440747),(-104/21611205),(-4/2401245),(4/36018675)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac02Coeffs_correct : widthCoefficients 5 false 2 = vac02Coeffs := by
  rw [widthCoefficients,vac02Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
