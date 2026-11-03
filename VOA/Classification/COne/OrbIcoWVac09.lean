import VOA.Classification.COne.OrbIcoWVac08

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac09Rows00 := jetRows 3 false 9 0
theorem vac09Rows00_correct : jetRows 3 false 9 0 = vac09Rows00 := rfl
def vac09Row01 : List Jet := [[(9/2),(-5/2),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac09Rows01 : List (List Jet) := vac09Rows00 ++ [vac09Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows01_correct : jetRows 3 false 9 1 = vac09Rows01 := by
  rw [jetRows, vac09Rows00_correct]
  change vac09Rows00 ++ [jetStep 3 false 9 1 vac09Rows00] = vac09Rows00 ++ [vac09Row01]
  congr 1
  decide +kernel
def vac09Row02 : List Jet := [[(315/44),(-116/11),(145/44),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac09Rows02 : List (List Jet) := vac09Rows01 ++ [vac09Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows02_correct : jetRows 3 false 9 2 = vac09Rows02 := by
  rw [jetRows, vac09Rows01_correct]
  change vac09Rows01 ++ [jetStep 3 false 9 2 vac09Rows01] = vac09Rows01 ++ [vac09Row02]
  congr 1
  decide +kernel
def vac09Row03 : List Jet := [[(861/220),(-224/15),(2877/220),(-203/66)],[(-51/220),(-17/165),(17/132),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac09Rows03 : List (List Jet) := vac09Rows02 ++ [vac09Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows03_correct : jetRows 3 false 9 3 = vac09Rows03 := by
  rw [jetRows, vac09Rows02_correct]
  change vac09Rows02 ++ [jetStep 3 false 9 3 vac09Rows02] = vac09Rows02 ++ [vac09Row03]
  congr 1
  decide +kernel
def vac09Row04 : List Jet := [[(-637/880),(-14467/2640),(14407/880),(-30533/2640)],[(-29/66),(569/2970),(647/1485),(-58/297)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac09Rows04 : List (List Jet) := vac09Rows03 ++ [vac09Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows04_correct : jetRows 3 false 9 4 = vac09Rows04 := by
  rw [jetRows, vac09Rows03_correct]
  change vac09Rows03 ++ [jetStep 3 false 9 4 vac09Rows03] = vac09Rows03 ++ [vac09Row04]
  congr 1
  decide +kernel
def vac09Row05 : List Jet := [[(-11039/17600),(97517/26400),(72059/26400),(-84263/6600)],[(-217/660),(93541/118800),(7399/39600),(-28343/39600)],[(3/400),(13/1200),(-1/1200),(-1/240)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac09Rows05 : List (List Jet) := vac09Rows04 ++ [vac09Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows05_correct : jetRows 3 false 9 5 = vac09Rows05 := by
  rw [jetRows, vac09Rows04_correct]
  change vac09Rows04 ++ [jetStep 3 false 9 5 vac09Rows04] = vac09Rows04 ++ [vac09Row05]
  congr 1
  decide +kernel
def vac09Row06 : List Jet := [[(5327/9600),(221053/316800),(-24683/3850),(907037/1108800)],[(871/110880),(3445007/4989600),(-60509/69300),(-16369/29700)],[(1949/110880),(26393/2494800),(-101/4200),(-7919/831600)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac09Rows06 : List (List Jet) := vac09Rows05 ++ [vac09Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows06_correct : jetRows 3 false 9 6 = vac09Rows06 := by
  rw [jetRows, vac09Rows05_correct]
  change vac09Rows05 ++ [jetStep 3 false 9 6 vac09Rows05] = vac09Rows05 ++ [vac09Row06]
  congr 1
  decide +kernel
def vac09Row07 : List Jet := [[(-89/1408),(-6167/3200),(948823/1940400),(6148001/862400)],[(423767/4233600),(-58384973/419126400),(-9454213/9525600),(12351167/13970880)],[(2843/151200),(-5291/272160),(-187919/3742200),(326/14175)],[(-281/1293600),(-281/529200),(-281/970200),(281/1940400)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac09Rows07 : List (List Jet) := vac09Rows06 ++ [vac09Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows07_correct : jetRows 3 false 9 7 = vac09Rows07 := by
  rw [jetRows, vac09Rows06_correct]
  change vac09Rows06 ++ [jetStep 3 false 9 7 vac09Rows06] = vac09Rows06 ++ [vac09Row07]
  congr 1
  decide +kernel
def vac09Row08 : List Jet := [[(-300407/1408000),(408869/704000),(2109911921/620928000),(-578517881/310464000)],[(-28782587/931392000),(-46391453/130977000),(2918045153/8382528000),(681854851/523908000)],[(17993/3696000),(-819083/16632000),(-179603/33264000),(16091/173250)],[(-1301/1940400),(-96109/87318000),(38873/87318000),(35941/29106000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac09Rows08 : List (List Jet) := vac09Rows07 ++ [vac09Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows08_correct : jetRows 3 false 9 8 = vac09Rows08 := by
  rw [jetRows, vac09Rows07_correct]
  change vac09Rows07 ++ [jetStep 3 false 9 8 vac09Rows07] = vac09Rows07 ++ [vac09Row08]
  congr 1
  decide +kernel
def vac09Row09 : List Jet := [[(3460163/25344000),(3953183/5068800),(-313579043/228096000),(-17667424651/3725568000)],[(-79314401/1676505600),(746784127/5388768000),(61788648967/75442752000),(-2801842877/5388768000)],[(-67288703/8382528000),(-177229793/7544275200),(7093739651/75442752000),(1128795553/18860688000)],[(-109/97200),(-78997/244944000),(1880119/538876800),(323903/192456000)],[(667/93139200),(20677/838252800),(11339/419126400),(667/139708800)],[0,0,0,0],[0,0,0,0]]
def vac09Rows09 : List (List Jet) := vac09Rows08 ++ [vac09Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows09_correct : jetRows 3 false 9 9 = vac09Rows09 := by
  rw [jetRows, vac09Rows08_correct]
  change vac09Rows08 ++ [jetStep 3 false 9 9 vac09Rows08] = vac09Rows08 ++ [vac09Row09]
  congr 1
  decide +kernel
def vac09Row10 : List Jet := [[(1650411/28160000),(-61684903/126720000),(-224973827/110880000),(57572819/39916800)],[(2681500319/100590336000),(111762300959/411505920000),(-68197684321/301771008000),(-2584413184501/1508855040000)],[(-134471473/25147584000),(19999531091/565820640000),(7291485403/75442752000),(-422206727/2694384000)],[(-20831297/20956320000),(280954133/94303440000),(1126068533/188606880000),(-34445351/6735960000)],[(92833/2794176000),(2804633/31434480000),(4738213/125737920000),(-605173/7858620000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac09Rows10 : List (List Jet) := vac09Rows09 ++ [vac09Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows10_correct : jetRows 3 false 9 10 = vac09Rows10 := by
  rw [jetRows, vac09Rows09_correct]
  change vac09Rows09 ++ [jetStep 3 false 9 10 vac09Rows09] = vac09Rows09 ++ [vac09Row10]
  congr 1
  decide +kernel
def vac09Row11 : List Jet := [[(-13999993/309760000),(-772127501/1393920000),(1017442543/9757440000),(612764927347/122943744000)],[(8478073649/201180672000),(-960311136731/49792216320000),(-3834091927741/3556586880000),(-26143886999/51226560000)],[(6335687/1229437440),(2050122037/34577928000),(-33900711821/518668920000),(-268603259/705672000)],[(-23793379/307359360000),(21273453479/2766234240000),(-1112737441/922078080000),(-22847959571/922078080000)],[(1451941/13172544000),(52045297/296382240000),(-42311147/197588160000),(-22088747/49397040000)],[(-793/2049062400),(-793/461039040),(-10309/3688312320),(-793/461039040)],[0,0,0,0]]
def vac09Rows11 : List (List Jet) := vac09Rows10 ++ [vac09Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows11_correct : jetRows 3 false 9 11 = vac09Rows11 := by
  rw [jetRows, vac09Rows10_correct]
  change vac09Rows10 ++ [jetStep 3 false 9 11 vac09Rows10] = vac09Rows10 ++ [vac09Row11]
  congr 1
  decide +kernel
def vac09Row12 : List Jet := [[(-22020593/247808000),(-29608690153/33454080000),(115075485011/58544640000),(201047868313/18817920000)],[(20683988663/431101440000),(-288110599171/762125760000),(-6044238722353/3048503040000),(20565929249543/7113173760000)],[(241828699139/13277924352000),(2109570091183/37344162240000),(-5622175284883/11950131916800),(-50422025791439/99584432640000)],[(9217352651/4742115840000),(474910205261/29875329792000),(-606708270271/13579695360000),(-447652796471/7113173760000)],[(2308882439/5532468480000),(1482865973/49792216320000),(-33875126339/16597405440000),(-17940605321/16597405440000)],[(-18251/4191264000),(-4827377/296382240000),(-43781/2469852000),(1541/470448000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac09Rows12 : List (List Jet) := vac09Rows11 ++ [vac09Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Rows12_correct : jetRows 3 false 9 12 = vac09Rows12 := by
  rw [jetRows, vac09Rows11_correct]
  change vac09Rows11 ++ [jetStep 3 false 9 12 vac09Rows11] = vac09Rows11 ++ [vac09Row12]
  congr 1
  decide +kernel
def vac09Coeffs : List Jet := [[(2508162167/619520000),(534745463/15360000),(-196865253449/1393920000),(-559179520541/1829520000)],[(-996537086437/518668920000),(2717439930632179/149376648960000),(3927100152309707/74688324480000),(-278467924382303/1244805408000)],[(-99493953829/150885504000),(-6963479104403/14937664896000),(774603676599103/37344162240000),(-211473668680537/12448054080000)],[(-5772099139/69155856000),(-2230664535577/6224027040000),(3515434055519/1244805408000),(-1411559581247/691558560000)],[(-1492554671/86444820000),(15456567503/389001690000),(1138422893/18523890000),(-4400698991/43222410000)],[(33139/102910500),(5795617/9261945000),(-456173/1543657500),(-304019/280665000)],[(-2/4002075),(-16/7203735),(-26/7203735),(-16/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac09Coeffs_correct : widthCoefficients 3 false 9 = vac09Coeffs := by
  rw [widthCoefficients,vac09Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
