import VOA.Classification.COne.OrbIcoWVac07

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac08Rows00 := jetRows 4 false 8 0
theorem vac08Rows00_correct : jetRows 4 false 8 0 = vac08Rows00 := rfl
def vac08Row01 : List Jet := [[(14/3),(-7/3),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows01 : List (List Jet) := vac08Rows00 ++ [vac08Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows01_correct : jetRows 4 false 8 1 = vac08Rows01 := by
  rw [jetRows, vac08Rows00_correct]
  change vac08Rows00 ++ [jetStep 4 false 8 1 vac08Rows00] = vac08Rows00 ++ [vac08Row01]
  congr 1
  decide +kernel
def vac08Row02 : List Jet := [[(87/11),(-225/22),(63/22),0,0],[(-1/22),(-1/22),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows02 : List (List Jet) := vac08Rows01 ++ [vac08Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows02_correct : jetRows 4 false 8 2 = vac08Rows02 := by
  rw [jetRows, vac08Rows01_correct]
  change vac08Rows01 ++ [jetStep 4 false 8 2 vac08Rows01] = vac08Rows01 ++ [vac08Row02]
  congr 1
  decide +kernel
def vac08Row03 : List Jet := [[(56/11),(-2573/165),(71/6),(-273/110),0],[(-119/495),(-119/990),(119/990),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows03 : List (List Jet) := vac08Rows02 ++ [vac08Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows03_correct : jetRows 4 false 8 3 = vac08Rows03 := by
  rw [jetRows, vac08Rows02_correct]
  change vac08Rows02 ++ [jetStep 4 false 8 3 vac08Rows02] = vac08Rows02 ++ [vac08Row03]
  congr 1
  decide +kernel
def vac08Row04 : List Jet := [[(-14/99),(-44527/5940),(38449/2376),(-57853/5940),(455/264)],[(-719/1485),(379/2970),(1313/2970),(-28/165),0],[(1/792),(1/396),(1/792),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows04 : List (List Jet) := vac08Rows03 ++ [vac08Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows04_correct : jetRows 4 false 8 4 = vac08Rows04 := by
  rw [jetRows, vac08Rows03_correct]
  change vac08Rows03 ++ [jetStep 4 false 8 4 vac08Rows03] = vac08Rows03 ++ [vac08Row04]
  congr 1
  decide +kernel
def vac08Row05 : List Jet := [[(-28/33),(119/45),(9859/1980),(-47417/3960),(1171/180)],[(-24701/59400),(29441/39600),(12629/39600),(-79363/118800),(91/528)],[(7/900),(7/600),0,(-7/1800),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows05 : List (List Jet) := vac08Rows04 ++ [vac08Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows05_correct : jetRows 4 false 8 5 = vac08Rows05 := by
  rw [jetRows, vac08Rows04_correct]
  change vac08Rows04 ++ [jetStep 4 false 8 5 vac08Rows04] = vac08Rows04 ++ [vac08Row05]
  congr 1
  decide +kernel
def vac08Row06 : List Jet := [[(14/33),(728/495),(-425077/83160),(-81079/55440),(404483/55440)],[(-144839/2494800),(1332229/1663200),(-10203/15400),(-1688111/2494800),(38881/55440)],[(24097/1247400),(12319/831600),(-61/2800),(-26797/2494800),(259/39600)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows06 : List (List Jet) := vac08Rows05 ++ [vac08Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows06_correct : jetRows 4 false 8 6 = vac08Rows06 := by
  rw [jetRows, vac08Rows05_correct]
  change vac08Rows05 ++ [jetStep 4 false 8 6 vac08Rows05] = vac08Rows05 ++ [vac08Row06]
  congr 1
  decide +kernel
def vac08Row07 : List Jet := [[(8/99),(-4733/2970),(-822167/873180),(1992433/349272),(-619831/1164240)],[(24965/232848),(14513/431200),(-1018847/970200),(512717/970200),(2297521/2910600)],[(1215661/52390800),(-262601/20956320),(-117749/2182950),(753091/52390800),(23269/952560)],[(-281/1247400),(-281/498960),(-281/831600),(281/2494800),(281/2494800)],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows07 : List (List Jet) := vac08Rows06 ++ [vac08Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows07_correct : jetRows 4 false 8 7 = vac08Rows07 := by
  rw [jetRows, vac08Rows06_correct]
  change vac08Rows06 ++ [jetStep 4 false 8 7 vac08Rows06] = vac08Rows06 ++ [vac08Row07]
  congr 1
  decide +kernel
def vac08Row08 : List Jet := [[(-7/33),(287/7920),(4635853/1663200),(13009/100800),(-33588229/6652800)],[(-39637/232848000),(-168377701/465696000),(6914609/465696000),(26578859/21168000),(-933217/2116800)],[(10673749/1047816000),(-9483049/190512000),(-10810253/419126400),(89188147/1047816000),(3279253/523908000)],[(-4583/6237000),(-1499/1134000),(11/54000),(14897/12474000),(409/2494800)],[(1/1330560),(1/332640),(1/221760),(1/332640),(1/1330560)],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows08 : List (List Jet) := vac08Rows07 ++ [vac08Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows08_correct : jetRows 4 false 8 8 = vac08Rows08 := by
  rw [jetRows, vac08Rows07_correct]
  change vac08Rows07 ++ [jetStep 4 false 8 8 vac08Rows07] = vac08Rows07 ++ [vac08Row08]
  congr 1
  decide +kernel
def vac08Row09 : List Jet := [[(2/33),(2899/3960),(-196573/970200),(-31350899/8731800),(256349/14968800)],[(-4515383/85536000),(10232183/8382528000),(379455491/502951680),(131780351/3592512000),(-18672645307/12573792000)],[(-1645559/269438400),(-736675453/18860688000),(126243119/1714608000),(168571237/1886068800),(-494665081/4715172000)],[(-1160233/857304000),(-17622527/18860688000),(61589789/18860688000),(15559/6858432),(-8631341/4715172000)],[(667/89812800),(667/25660800),(667/22453200),(667/89812800),(-667/89812800)],[0,0,0,0,0],[0,0,0,0,0]]
def vac08Rows09 : List (List Jet) := vac08Rows08 ++ [vac08Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows09_correct : jetRows 4 false 8 9 = vac08Rows09 := by
  rw [jetRows, vac08Rows08_correct]
  change vac08Rows08 ++ [jetStep 4 false 8 9 vac08Rows08] = vac08Rows08 ++ [vac08Row09]
  congr 1
  decide +kernel
def vac08Row10 : List Jet := [[(7/99),(-2963/23760),(-71527/46200),(-4047511/10478160),(531771967/125737920)],[(2300743/665280000),(2981264311/11975040000),(168703897/1088640000),(-47730315667/35925120000),(-2152204649/5132160000)],[(-950619169/113164128000),(6541147427/377213760000),(1429605503/11787930000),(-13267931399/161663040000),(-12592692929/62868960000)],[(-212615387/141455160000),(7984717/3492720000),(688922303/94303440000),(-397806187/141455160000),(-19605937/2619540000)],[(163007/4490640000),(184819/1796256000),(537967/8981280000),(-284401/4490640000),(-145867/2245320000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680),(-1/7983360)],[0,0,0,0,0]]
def vac08Rows10 : List (List Jet) := vac08Rows09 ++ [vac08Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows10_correct : jetRows 4 false 8 10 = vac08Rows10 := by
  rw [jetRows, vac08Rows09_correct]
  change vac08Rows09 ++ [jetStep 4 false 8 10 vac08Rows09] = vac08Rows09 ++ [vac08Row10]
  congr 1
  decide +kernel
def vac08Row11 : List Jet := [[0,(-119/330),(-2098843/3049200),(22169173/9147600),(1377598493/384199200)],[(85573297/2439360000),(116491932989/922078080000),(-68965187023/102453120000),(-3377750175623/2766234240000),(1925901706481/922078080000)],[(-11981911/71131737600),(1569722067007/24896108160000),(231864737/7620480000),(-810404368967/2263282560000),(-519884307973/24896108160000)],[(-31239763/34577928000),(804180851/94303440000),(18481073/3929310000),(-2666462749/115259760000),(-531592631/74095560000)],[(135053803/1037337840000),(15700331/62868960000),(-93680039/691558560000),(-44025407/94303440000),(-12948533/172889640000)],[(-793/1975881600),(-793/439084800),(-793/263450880),(-793/395176320),0],[0,0,0,0,0]]
def vac08Rows11 : List (List Jet) := vac08Rows10 ++ [vac08Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows11_correct : jetRows 4 false 8 11 = vac08Rows11 := by
  rw [jetRows, vac08Rows10_correct]
  change vac08Rows10 ++ [jetStep 4 false 8 11 vac08Rows10] = vac08Rows10 ++ [vac08Row11]
  congr 1
  decide +kernel
def vac08Row12 : List Jet := [[0,(-3017/3960),(-926587/1355200),(196720031/27442800),(534450929/139708800)],[(1097668273/17563392000),(11162057807/1580705280000),(-10392369579457/5532468480000),(-3983966710811/8298702720000),(65507535656197/8298702720000)],[(58991062429/5334880320000),(263009867389/2133952128000),(-911994956671/3556586880000),(-867601860787/969978240000),(2904599047681/2667440160000)],[(25443598423/74688324480000),(3735274428563/149376648960000),(-125742765319/4526565120000),(-12953782017413/149376648960000),(9058599369637/149376648960000)],[(20561274101/37344162240000),(4259966497/10669760640000),(-101395991/50808384000),(-18909291211/10669760640000),(9067786393/5334880320000)],[(-702313/148191120000),(-605459/32931360000),(-2196611/98794080000),(-3401/2694384000),(25451/1646568000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080),(1/31933440)]]
def vac08Rows12 : List (List Jet) := vac08Rows11 ++ [vac08Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Rows12_correct : jetRows 4 false 8 12 = vac08Rows12 := by
  rw [jetRows, vac08Rows11_correct]
  change vac08Rows11 ++ [jetStep 4 false 8 12 vac08Rows11] = vac08Rows11 ++ [vac08Row12]
  congr 1
  decide +kernel
def vac08Coeffs : List Jet := [[0,(3640/99),(-24169/1452),(-465272729/1372140),(6719803759/24012450)],[(-5579381147/2090880000),(27084142321/7983360000),(889267571363/11383680000),(-205155576049/2095632000),(-5676247428823/21611205000)],[(-37698837523/83357505000),(-1508895238277/381062880000),(230189743498601/12448054080000),(409070782714459/37344162240000),(-3052616499831509/37344162240000)],[(-310996292533/9336040560000),(-3416083195633/3734416224000),(1729498985047/565820640000),(-525022778081/1697461920000),(-97728270878893/18672081120000)],[(-196168213/7780033800),(12907725113/389001690000),(1424224271/16208403750),(-30335285899/389001690000),(-8266327319/97250422500)],[(12025033/32416807500),(17557501/21611205000),(-863077/10805602500),(-70834769/64833615000),(-3309451/10805602500)],[(-8/15436575),(-4/1715175),(-4/1029105),(-8/3087315),0]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac08Coeffs_correct : widthCoefficients 4 false 8 = vac08Coeffs := by
  rw [widthCoefficients,vac08Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
