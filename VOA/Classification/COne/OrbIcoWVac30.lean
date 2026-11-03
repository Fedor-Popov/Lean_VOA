import VOA.Classification.COne.OrbIcoWVac29

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac30Rows00 := jetRows 2 false 30 0
theorem vac30Rows00_correct : jetRows 2 false 30 0 = vac30Rows00 := rfl
def vac30Row01 : List Jet := [[1,-6,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac30Rows01 : List (List Jet) := vac30Rows00 ++ [vac30Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows01_correct : jetRows 2 false 30 1 = vac30Rows01 := by
  rw [jetRows, vac30Rows00_correct]
  change vac30Rows00 ++ [jetStep 2 false 30 1 vac30Rows00] = vac30Rows00 ++ [vac30Row01]
  congr 1
  decide +kernel
def vac30Row02 : List Jet := [[(-35/22),(-71/22),(213/11)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac30Rows02 : List (List Jet) := vac30Rows01 ++ [vac30Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows02_correct : jetRows 2 false 30 2 = vac30Rows02 := by
  rw [jetRows, vac30Rows01_correct]
  change vac30Rows01 ++ [jetStep 2 false 30 2 vac30Rows01] = vac30Rows01 ++ [vac30Row02]
  congr 1
  decide +kernel
def vac30Row03 : List Jet := [[(14/33),(259/22),(7/6)],[(-17/330),(17/66),(17/55)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac30Rows03 : List (List Jet) := vac30Rows02 ++ [vac30Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows03_correct : jetRows 2 false 30 3 = vac30Rows03 := by
  rw [jetRows, vac30Rows02_correct]
  change vac30Rows02 ++ [jetStep 2 false 30 3 vac30Rows02] = vac30Rows02 ++ [vac30Row03]
  congr 1
  decide +kernel
def vac30Row04 : List Jet := [[(140/99),(-6935/792),(-16613/396)],[(128/1485),(863/2970),(-2801/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac30Rows04 : List (List Jet) := vac30Rows03 ++ [vac30Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows04_correct : jetRows 2 false 30 4 = vac30Rows04 := by
  rw [jetRows, vac30Rows03_correct]
  change vac30Rows03 ++ [jetStep 2 false 30 4 vac30Rows03] = vac30Rows03 ++ [vac30Row04]
  congr 1
  decide +kernel
def vac30Row05 : List Jet := [[(-4991/1980),(-4193/720),(28295/528)],[(-1519/118800),(-30443/39600),(-37597/39600)],[(1/600),(-1/150),(-11/600)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac30Rows05 : List (List Jet) := vac30Rows04 ++ [vac30Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows05_correct : jetRows 2 false 30 5 = vac30Rows05 := by
  rw [jetRows, vac30Rows04_correct]
  change vac30Rows04 ++ [jetStep 2 false 30 5 vac30Rows04] = vac30Rows04 ++ [vac30Row05]
  congr 1
  decide +kernel
def vac30Row06 : List Jet := [[(22519/11880),(1061791/47520),(-371137/166320)],[(-114997/997920),(321721/831600),(3159151/831600)],[(-7433/2494800),(-11969/831600),(1843/75600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac30Rows06 : List (List Jet) := vac30Rows05 ++ [vac30Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows06_correct : jetRows 2 false 30 6 = vac30Rows06 := by
  rw [jetRows, vac30Rows05_correct]
  change vac30Rows05 ++ [jetStep 2 false 30 6 vac30Rows05] = vac30Rows05 ++ [vac30Row06]
  congr 1
  decide +kernel
def vac30Row07 : List Jet := [[(167/297),(-80847/3080),(-76395299/776160)],[(19669589/104781600),(99943397/104781600),(-5720273/1746360)],[(-323/2993760),(240511/7484400),(7361/92400)],[(-281/5821200),(281/1940400),(281/388080)],[0,0,0],[0,0,0],[0,0,0]]
def vac30Rows07 : List (List Jet) := vac30Rows06 ++ [vac30Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows07_correct : jetRows 2 false 30 7 = vac30Rows07 := by
  rw [jetRows, vac30Rows06_correct]
  change vac30Rows06 ++ [jetStep 2 false 30 7 vac30Rows06] = vac30Rows06 ++ [vac30Row07]
  congr 1
  decide +kernel
def vac30Row08 : List Jet := [[(-89267/23760),(358021/66528),(71377753/413952)],[(-387778133/4191264000),(-9800604259/4191264000),(-4424321417/1047816000)],[(126107/19958400),(-8317/1814400),(-527033/2494800)],[(2071/21829500),(979/1587600),(-299/882000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac30Rows08 : List (List Jet) := vac30Rows07 ++ [vac30Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows08_correct : jetRows 2 false 30 8 = vac30Rows08 := by
  rw [jetRows, vac30Rows07_correct]
  change vac30Rows07 ++ [jetStep 2 false 30 8 vac30Rows07] = vac30Rows07 ++ [vac30Row08]
  congr 1
  decide +kernel
def vac30Row09 : List Jet := [[(228389/42768),(709373/17820),(-316893517/3421440)],[(-15816357257/75442752000),(10029247507/5388768000),(249141683723/15088550400)],[(-17920099/1886068800),(-160172213/1886068800),(11701699/171460800)],[(8683/244944000),(-98149/76982400),(-1721789/336798000)],[(667/419126400),(-667/209563200),(-667/23284800)],[0,0,0],[0,0,0]]
def vac30Rows09 : List (List Jet) := vac30Rows08 ++ [vac30Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows09_correct : jetRows 2 false 30 9 = vac30Rows09 := by
  rw [jetRows, vac30Rows08_correct]
  change vac30Rows08 ++ [jetStep 2 false 30 9 vac30Rows08] = vac30Rows08 ++ [vac30Row09]
  congr 1
  decide +kernel
def vac30Row10 : List Jet := [[(-4416209/2138400),(-58213913/712800),(-61890814429/239500800)],[(1298701882273/2263282560000),(2053829895449/754427520000),(-1279049754191/68584320000)],[(-913639183/1131641280000),(5309096893/31434480000),(275543398321/377213760000)],[(-1386379/3772137600),(-14142113/18860688000),(107874709/9430344000)],[(-231061/62868960000),(-1994141/62868960000),(-212719/15717240000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac30Rows10 : List (List Jet) := vac30Rows09 ++ [vac30Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows10_correct : jetRows 2 false 30 10 = vac30Rows10 := by
  rw [jetRows, vac30Rows09_correct]
  change vac30Rows09 ++ [jetStep 2 false 30 10 vac30Rows09] = vac30Rows09 ++ [vac30Row10]
  congr 1
  decide +kernel
def vac30Row11 : List Jet := [[(-428281/48600),(17435633/427680),(519054571471/658627200)],[(-2315259858829/4979221632000),(-288115984268141/24896108160000),(-4552243574867/169361280000)],[(287983367387/8298702720000),(105171320509/8298702720000),(-45026497361/22861440000)],[(209787353/414935136000),(80308861/9430344000),(29255389/2514758400)],[(-1370773/296382240000),(206923/2993760000),(21785987/49397040000)],[(-793/9220780800),(793/9220780800),(793/461039040)],[0,0,0]]
def vac30Rows11 : List (List Jet) := vac30Rows10 ++ [vac30Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows11_correct : jetRows 2 false 30 11 = vac30Rows11 := by
  rw [jetRows, vac30Rows10_correct]
  change vac30Rows10 ++ [jetStep 2 false 30 11 vac30Rows10] = vac30Rows10 ++ [vac30Row11]
  congr 1
  decide +kernel
def vac30Row12 : List Jet := [[(1341011/58320),(2416769653/8553600),(-203704010473/790352640)],[(-73119602213029/42679042560000),(32713237924039/3048503040000),(343086948011719/1778293440000)],[(-1108873619107/14937664896000),(-23027737278923/18672081120000),(-45808908324167/49792216320000)],[(32395311569/21339521280000),(-459332765477/29875329792000),(-777179928347/4526565120000)],[(218671637/4979221632000),(399912221/1556006760000),(-9002736553/8298702720000)],[(81253/259334460000),(384283/98794080000),(58327/10977120000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac30Rows12 : List (List Jet) := vac30Rows11 ++ [vac30Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Rows12_correct : jetRows 2 false 30 12 = vac30Rows12 := by
  rw [jetRows, vac30Rows11_correct]
  change vac30Rows11 ++ [jetStep 2 false 30 12 vac30Rows11] = vac30Rows11 ++ [vac30Row12]
  congr 1
  decide +kernel
def vac30Coeffs : List Jet := [[(-2997967/9720),(374971513/142560),(830766157811/18817920)],[(-4217421831252193/149376648960000),(-816936308295347/1357969536000),(587986876686481/6224027040000)],[(2284638444677/1493766489600),(-18620760112501/1493766489600),(-98658493563767/497922163200)],[(2309112397/43222410000),(3881558537281/6224027040000),(-348340626059/188606880000)],[(-4042141/97250422500),(5178427603/389001690000),(499644709/9261945000)],[(-103003/9261945000),(10693/171517500),(323677/441045000)],[(-4/36018675),(4/36018675),(16/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac30Coeffs_correct : widthCoefficients 2 false 30 = vac30Coeffs := by
  rw [widthCoefficients,vac30Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
