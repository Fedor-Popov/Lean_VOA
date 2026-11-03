import VOA.Classification.COne.OrbIcoWVac11

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac12Rows00 := jetRows 3 false 12 0
theorem vac12Rows00_correct : jetRows 3 false 12 0 = vac12Rows00 := rfl
def vac12Row01 : List Jet := [[4,-3,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac12Rows01 : List (List Jet) := vac12Rows00 ++ [vac12Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows01_correct : jetRows 3 false 12 1 = vac12Rows01 := by
  rw [jetRows, vac12Rows00_correct]
  change vac12Rows00 ++ [jetStep 3 false 12 1 vac12Rows00] = vac12Rows00 ++ [vac12Row01]
  congr 1
  decide +kernel
def vac12Row02 : List Jet := [[(56/11),(-245/22),(105/22),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac12Rows02 : List (List Jet) := vac12Rows01 ++ [vac12Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows02_correct : jetRows 3 false 12 2 = vac12Rows02 := by
  rw [jetRows, vac12Rows01_correct]
  change vac12Rows01 ++ [jetStep 3 false 12 2 vac12Rows01] = vac12Rows01 ++ [vac12Row02]
  congr 1
  decide +kernel
def vac12Row03 : List Jet := [[(38/33),(-658/55),(5437/330),(-119/22)],[(-34/165),(-17/330),(17/110),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac12Rows03 : List (List Jet) := vac12Rows02 ++ [vac12Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows03_correct : jetRows 3 false 12 3 = vac12Rows03 := by
  rw [jetRows, vac12Rows02_correct]
  change vac12Rows02 ++ [jetStep 3 false 12 3 vac12Rows02] = vac12Rows02 ++ [vac12Row03]
  congr 1
  decide +kernel
def vac12Row04 : List Jet := [[(-281/198),(223/495),(57217/3960),(-8644/495)],[(-469/1485),(1043/2970),(1141/2970),(-28/99)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac12Rows04 : List (List Jet) := vac12Rows03 ++ [vac12Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows04_correct : jetRows 3 false 12 4 = vac12Rows04 := by
  rw [jetRows, vac12Rows03_correct]
  change vac12Rows03 ++ [jetStep 3 false 12 4 vac12Rows03] = vac12Rows03 ++ [vac12Row04]
  congr 1
  decide +kernel
def vac12Row05 : List Jet := [[(5/18),(4573/990),(-12513/2200),(-29503/2475)],[(-145/1188),(953/1200),(-10207/39600),(-94843/118800)],[(1/150),(1/120),(-1/300),(-1/200)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac12Rows05 : List (List Jet) := vac12Rows04 ++ [vac12Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows05_correct : jetRows 3 false 12 5 = vac12Rows05 := by
  rw [jetRows, vac12Rows04_correct]
  change vac12Rows04 ++ [jetStep 3 false 12 5 vac12Rows04] = vac12Rows04 ++ [vac12Row05]
  congr 1
  decide +kernel
def vac12Row06 : List Jet := [[(4135/8316),(-52193/20790),(-5748221/831600),(266879/23760)],[(2437/22680),(4301/16800),(-19297/14850),(38383/498960)],[(569/44550),(-1/2160),(-3367/118800),(-1499/356400)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac12Rows06 : List (List Jet) := vac12Rows05 ++ [vac12Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows06_correct : jetRows 3 false 12 6 = vac12Rows06 := by
  rw [jetRows, vac12Rows05_correct]
  change vac12Rows05 ++ [jetStep 3 false 12 6 vac12Rows05] = vac12Rows05 ++ [vac12Row06]
  congr 1
  decide +kernel
def vac12Row07 : List Jet := [[(-14765/29106),(-13549/10780),(6884257/970200),(13248373/1940400)],[(127483/5239080),(-50736787/104781600),(-6174787/17463600),(9805591/5239080)],[(6157/748440),(-471193/14968800),(-38089/1247400),(363019/7484400)],[(-281/1455300),(-281/646800),(-281/1940400),(281/1164240)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac12Rows07 : List (List Jet) := vac12Rows06 ++ [vac12Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows07_correct : jetRows 3 false 12 7 = vac12Rows07 := by
  rw [jetRows, vac12Rows06_correct]
  change vac12Rows06 ++ [jetStep 3 false 12 7 vac12Rows06] = vac12Rows06 ++ [vac12Row07]
  congr 1
  decide +kernel
def vac12Row08 : List Jet := [[(16169/232848),(5790833/2328480),(1002287/705600),(-984672187/77616000)],[(-3333797/41912640),(-1681301/33530112),(744875749/598752000),(88762687/190512000)],[(-110153/24948000),(-3294103/99792000),(5209717/99792000),(632921/7128000)],[(-439/891000),(-6401/12474000),(4231/4158000),(601/498960)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac12Rows08 : List (List Jet) := vac12Rows07 ++ [vac12Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows08_correct : jetRows 3 false 12 8 = vac12Rows08 := by
  rw [jetRows, vac12Rows07_correct]
  change vac12Rows07 ++ [jetStep 3 false 12 8 vac12Rows07] = vac12Rows07 ++ [vac12Row08]
  congr 1
  decide +kernel
def vac12Row09 : List Jet := [[(5198/18711),(-58367/99792),(-8997143/1360800),(-76972277/49896000)],[(14560261/754427520),(269593609/603542016),(2189457679/18860688000),(-193514127407/75442752000)],[(-28247509/4715172000),(395133637/18860688000),(54743611/538876800),(-696493877/9430344000)],[(-105079/188606880),(17801533/18860688000),(62000003/18860688000),(-4733987/9430344000)],[(667/104781600),(8671/419126400),(667/34927200),(-667/209563200)],[0,0,0,0],[0,0,0,0]]
def vac12Rows09 : List (List Jet) := vac12Rows08 ++ [vac12Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows09_correct : jetRows 3 false 12 9 = vac12Rows09 := by
  rw [jetRows, vac12Rows08_correct]
  change vac12Rows08 ++ [jetStep 3 false 12 9 vac12Rows08] = vac12Rows08 ++ [vac12Row09]
  congr 1
  decide +kernel
def vac12Row10 : List Jet := [[(-17641/95256),(-11641067/6985440),(222445837/209563200),(1975171753/139708800)],[(282112403/4526565120),(-722928221/10059033600),(-237671548679/150885504000),(-142441236731/205752960000)],[(1350574283/282910320000),(17360337941/377213760000),(-9110865391/188606880000),(-66071826463/226328256000)],[(-841/84199500),(61185211/18860688000),(67166377/94303440000),(-158291227/15717240000)],[(991/40095000),(471763/8981280000),(-163243/8981280000),(-465461/4490640000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac12Rows10 : List (List Jet) := vac12Rows09 ++ [vac12Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows10_correct : jetRows 3 false 12 10 = vac12Rows10 := by
  rw [jetRows, vac12Rows09_correct]
  change vac12Rows09 ++ [jetStep 3 false 12 10 vac12Rows09] = vac12Rows09 ++ [vac12Row10]
  congr 1
  decide +kernel
def vac12Row11 : List Jet := [[(-1989109/11525976),(58088003/115259760),(1999532851/288149400),(5559226723/1152597600)],[(-157392451/7113173760),(-81068897171/142263475200),(-111993313937/237105792000),(16905570768131/3556586880000)],[(18920264729/2074675680000),(-156305623451/8298702720000),(-711369365461/2766234240000),(-32039402299/1659740544000)],[(43319743/51866892000),(248638289/103733784000),(-2186137/158760000),(-293128279/18523890000)],[(632803/10373378400),(7118849/691558560000),(-229598057/691558560000),(-290079397/1037337840000)],[(-793/2305195200),(-13481/9220780800),(-793/368831232),(-793/922078080)],[0,0,0,0]]
def vac12Rows11 : List (List Jet) := vac12Rows10 ++ [vac12Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows11_correct : jetRows 3 false 12 11 = vac12Rows11 := by
  rw [jetRows, vac12Rows10_correct]
  change vac12Rows10 ++ [jetStep 3 false 12 11 vac12Rows10] = vac12Rows10 ++ [vac12Row11]
  congr 1
  decide +kernel
def vac12Row12 : List Jet := [[(-12760147/138311712),(1110710113/461039040),(67038937291/6915585600),(-90465087341/4610390400)],[(-67256356331/597506595840),(-97691400803/155196518400),(2841864664949/905313024000),(114253850865727/10669760640000)],[(612441451/339492384000),(-12020079415517/74688324480000),(-267389809403/922078080000),(2161389224539/1493766489600)],[(59998708247/37344162240000),(-6598661947/853580851200),(-2300983581749/49792216320000),(979313768101/21339521280000)],[(427516787/3112013520000),(-13433865721/24896108160000),(-2898766589/2074675680000),(26415317051/24896108160000)],[(-69629/21170160000),(-31777/2993760000),(-39929/6586272000),(37151/2694384000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac12Rows12 : List (List Jet) := vac12Rows11 ++ [vac12Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Rows12_correct : jetRows 3 false 12 12 = vac12Rows12 := by
  rw [jetRows, vac12Rows11_correct]
  change vac12Rows11 ++ [jetStep 3 false 12 12 vac12Rows11] = vac12Rows11 ++ [vac12Row12]
  congr 1
  decide +kernel
def vac12Coeffs : List Jet := [[(20134775/5762988),(-369676939/3841992),(-316641923/1646568),(241732691881/192099600)],[(211505847545/59750659584),(2443083325337/239002638336),(-146110281261463/995844326400),(-199606662674149/1867208112000)],[(60985314091/666860040000),(13649809329949/2667440160000),(-630945400339/118552896000),(-8806387250161/152425152000)],[(-16258528723/518668920000),(2808059287951/6224027040000),(52984908811/98794080000),(-214475668103/46103904000)],[(-27949913/8840947500),(13409765029/389001690000),(-150121319/10805602500),(-6500501177/55571670000)],[(129161/648336150),(4206239/21611205000),(-3635363/5402801250),(-51946259/64833615000)],[(-16/36018675),(-68/36018675),(-4/1440747),(-8/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac12Coeffs_correct : widthCoefficients 3 false 12 = vac12Coeffs := by
  rw [widthCoefficients,vac12Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
