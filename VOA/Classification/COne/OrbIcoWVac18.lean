import VOA.Classification.COne.OrbIcoWVac17

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac18Rows00 := jetRows 3 false 18 0
theorem vac18Rows00_correct : jetRows 3 false 18 0 = vac18Rows00 := rfl
def vac18Row01 : List Jet := [[3,-4,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac18Rows01 : List (List Jet) := vac18Rows00 ++ [vac18Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows01_correct : jetRows 3 false 18 1 = vac18Rows01 := by
  rw [jetRows, vac18Rows00_correct]
  change vac18Rows00 ++ [jetStep 3 false 18 1 vac18Rows00] = vac18Rows00 ++ [vac18Row01]
  congr 1
  decide +kernel
def vac18Row02 : List Jet := [[(39/22),(-235/22),(94/11),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac18Rows02 : List (List Jet) := vac18Rows01 ++ [vac18Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows02_correct : jetRows 3 false 18 2 = vac18Rows02 := by
  rw [jetRows, vac18Rows01_correct]
  change vac18Rows01 ++ [jetStep 3 false 18 2 vac18Rows01] = vac18Rows01 ++ [vac18Row02]
  congr 1
  decide +kernel
def vac18Row03 : List Jet := [[(-16/11),(-1061/330),(443/22),(-2162/165)],[(-17/110),(17/330),(34/165),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac18Rows03 : List (List Jet) := vac18Rows02 ++ [vac18Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows03_correct : jetRows 3 false 18 3 = vac18Rows03 := by
  rw [jetRows, vac18Rows02_correct]
  change vac18Rows02 ++ [jetStep 3 false 18 3 vac18Rows02] = vac18Rows02 ++ [vac18Row03]
  congr 1
  decide +kernel
def vac18Row04 : List Jet := [[(-3/22),(919/120),(-20/33),(-35669/1320)],[(-58/495),(1559/2970),(403/2970),(-752/1485)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac18Rows04 : List (List Jet) := vac18Rows03 ++ [vac18Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows04_correct : jetRows 3 false 18 4 = vac18Rows04 := by
  rw [jetRows, vac18Rows03_correct]
  change vac18Rows03 ++ [jetStep 3 false 18 4 vac18Rows03] = vac18Rows03 ++ [vac18Row04]
  congr 1
  decide +kernel
def vac18Row05 : List Jet := [[(12/11),(-1261/528),(-16189/880),(2759/240)],[(3341/39600),(47143/118800),(-45041/39600),(-7127/13200)],[(1/200),(1/300),(-1/120),(-1/150)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac18Rows05 : List (List Jet) := vac18Rows04 ++ [vac18Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows05_correct : jetRows 3 false 18 5 = vac18Rows05 := by
  rw [jetRows, vac18Rows04_correct]
  change vac18Rows04 ++ [jetStep 3 false 18 5 vac18Rows04] = vac18Rows04 ++ [vac18Row05]
  congr 1
  decide +kernel
def vac18Row06 : List Jet := [[(-10/11),(-511241/110880),(90509/6930),(1624193/55440)],[(71179/1663200),(-668257/1247400),(-26101/30800),(223061/103950)],[(4183/831600),(-37603/2494800),(-7129/277200),(1051/75600)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac18Rows06 : List (List Jet) := vac18Rows05 ++ [vac18Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows06_correct : jetRows 3 false 18 6 = vac18Rows06 := by
  rw [jetRows, vac18Rows05_correct]
  change vac18Rows05 ++ [jetStep 3 false 18 6 vac18Rows05] = vac18Rows05 ++ [vac18Row06]
  congr 1
  decide +kernel
def vac18Row07 : List Jet := [[0,(20171/3080),(996227/110880),(-1980883/55440)],[(-66049/635040),(-13375181/104781600),(96331007/52390800),(25916411/17463600)],[(-101341/34927200),(-6653/261954),(1529909/52390800),(698101/8731800)],[(-281/1940400),(-281/1164240),(281/1940400),(281/646800)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac18Rows07 : List (List Jet) := vac18Rows06 ++ [vac18Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows07_correct : jetRows 3 false 18 7 = vac18Rows07 := by
  rw [jetRows, vac18Rows06_correct]
  change vac18Rows06 ++ [jetStep 3 false 18 7 vac18Rows06] = vac18Rows06 ++ [vac18Row07]
  congr 1
  decide +kernel
def vac18Row08 : List Jet := [[(9/11),(-3071/1760),(-104346211/4435200),(-15829327/1478400)],[(59715043/1397088000),(3068515481/4191264000),(264696503/2095632000),(-10118981549/2095632000)],[(-320161/77616000),(4645009/232848000),(2132957/23284800),(-5856797/116424000)],[(-34/165375),(27917/87318000),(129047/87318000),(13373/29106000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac18Rows08 : List (List Jet) := vac18Rows07 ++ [vac18Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows08_correct : jetRows 3 false 18 8 = vac18Rows08 := by
  rw [jetRows, vac18Rows07_correct]
  change vac18Rows07 ++ [jetStep 3 false 18 8 vac18Rows07] = vac18Rows07 ++ [vac18Row08]
  congr 1
  decide +kernel
def vac18Row09 : List Jet := [[(-9/11),(-2738/495),(37606459/3628800),(2508792589/39916800)],[(294520069/3592512000),(-40780687/96228000),(-6616575061/2155507200),(312378287/2694384000)],[(1852903/314344800),(80126609/2357586000),(-758199083/9430344000),(-275508151/943034400)],[(421523/6286896000),(27197683/18860688000),(2608087/9430344000),(-9511541/1886068800)],[(667/139708800),(667/52390800),(667/209563200),(-667/34927200)],[0,0,0,0],[0,0,0,0]]
def vac18Rows09 : List (List Jet) := vac18Rows08 ++ [vac18Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows09_correct : jetRows 3 false 18 9 = vac18Rows09 := by
  rw [jetRows, vac18Rows08_correct]
  change vac18Rows08 ++ [jetStep 3 false 18 9 vac18Rows08] = vac18Rows08 ++ [vac18Row09]
  congr 1
  decide +kernel
def vac18Row10 : List Jet := [[(-3/22),(1151/165),(663591121/26611200),(-318867431/9979200)],[(-94047036323/754427520000),(-1822216844941/2263282560000),(1546524009731/754427520000),(2745156317411/251475840000)],[(221914201/75442752000),(-4545655621/80831520000),(-74464112029/377213760000),(995738969/3929310000)],[(10999789/31434480000),(-11670781/94303440000),(-173939903/23575860000),(-38256587/6735960000)],[(229211/20956320000),(-18157/12573792000),(-2557253/31434480000),(-2898757/31434480000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac18Rows10 : List (List Jet) := vac18Rows09 ++ [vac18Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows10_correct : jetRows 3 false 18 10 = vac18Rows10 := by
  rw [jetRows, vac18Rows09_correct]
  change vac18Rows09 ++ [jetStep 3 false 18 10 vac18Rows09] = vac18Rows09 ++ [vac18Row10]
  congr 1
  decide +kernel
def vac18Row11 : List Jet := [[(12/11),(629/165),(-1183311761/36590400),(-14479523183/125452800)],[(-453066759521/8298702720000),(32752915364663/24896108160000),(151000736222351/24896108160000),(-49257487050979/8298702720000)],[(-119405179/8781696000),(-24415392871/395176320000),(388832094019/1185528960000),(445410668861/395176320000)],[(-8286671/46103904000),(-151961603/31434480000),(-2918916337/691558560000),(4058483021/115259760000)],[(2553437/691558560000),(-232349057/2074675680000),(-3923897/21611205000),(11563249/38419920000)],[(-793/3073593600),(-793/838252800),(-793/922078080),(793/922078080)],[0,0,0,0]]
def vac18Rows11 : List (List Jet) := vac18Rows10 ++ [vac18Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows11_correct : jetRows 3 false 18 11 = vac18Rows11 := by
  rw [jetRows, vac18Rows10_correct]
  change vac18Rows10 ++ [jetStep 3 false 18 11 vac18Rows10] = vac18Rows10 ++ [vac18Row11]
  congr 1
  decide +kernel
def vac18Row12 : List Jet := [[(1/2),(-27073/1980),(-70255151821/878169600),(55196846519/958003200)],[(6045560998129/19916886528000),(200302862209687/74688324480000),(-61673488847629/9336040560000),(-1364121170878693/24896108160000)],[(-288472067783/24896108160000),(840734004613/3734416224000),(172417413970903/149376648960000),(-22000075206817/16597405440000)],[(-79519987873/49792216320000),(-375178615937/149376648960000),(8115865541293/149376648960000),(434429720719/4526565120000)],[(-8512423/169361280000),(-3487225831/12448054080000),(486394963/553246848000),(3821410927/1383117120000)],[(-269131/172889640000),(-610151/296382240000),(878539/98794080000),(206083/9879408000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac18Rows12 : List (List Jet) := vac18Rows11 ++ [vac18Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Rows12_correct : jetRows 3 false 18 12 = vac18Rows12 := by
  rw [jetRows, vac18Rows11_correct]
  change vac18Rows11 ++ [jetStep 3 false 18 12 vac18Rows11] = vac18Rows11 ++ [vac18Row12]
  congr 1
  decide +kernel
def vac18Coeffs : List Jet := [[0,(4641/11),(2975013/3872),(-2137852090883/292723200)],[(-367845062139733/49792216320000),(-234247083701503/18672081120000),(7882947542297537/18672081120000),(1410724941934621/2489610816000)],[(-2416772239513/12448054080000),(-265703468738681/37344162240000),(7365829068233/3394923840000),(506240836332911/4149351360000)],[(3537546779/148191120000),(-49198053431/177829344000),(-1195827502949/889146720000),(1048100790323/296382240000)],[(18950971/12966723000),(-149489027/35363790000),(-3392284171/64833615000),(5905923257/129667230000)],[(1009607/21611205000),(-1554019/8104201875),(-11400469/21611205000),(691021/1800933750)],[(-4/12006225),(-4/3274425),(-8/7203735),(8/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac18Coeffs_correct : widthCoefficients 3 false 18 = vac18Coeffs := by
  rw [widthCoefficients,vac18Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
