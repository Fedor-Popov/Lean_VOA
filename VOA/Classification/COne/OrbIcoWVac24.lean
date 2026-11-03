import VOA.Classification.COne.OrbIcoWVac23

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac24Rows00 := jetRows 2 false 24 0
theorem vac24Rows00_correct : jetRows 2 false 24 0 = vac24Rows00 := rfl
def vac24Row01 : List Jet := [[2,-5,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac24Rows01 : List (List Jet) := vac24Rows00 ++ [vac24Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows01_correct : jetRows 2 false 24 1 = vac24Rows01 := by
  rw [jetRows, vac24Rows00_correct]
  change vac24Rows00 ++ [jetStep 2 false 24 1 vac24Rows00] = vac24Rows00 ++ [vac24Row01]
  congr 1
  decide +kernel
def vac24Row02 : List Jet := [[(-5/11),(-177/22),(295/22)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac24Rows02 : List (List Jet) := vac24Rows01 ++ [vac24Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows02_correct : jetRows 2 false 24 2 = vac24Rows02 := by
  rw [jetRows, vac24Rows01_correct]
  change vac24Rows01 ++ [jetStep 2 false 24 2 vac24Rows01] = vac24Rows01 ++ [vac24Row02]
  congr 1
  decide +kernel
def vac24Row03 : List Jet := [[(-208/165),(991/165),(5393/330)],[(-17/165),(17/110),(17/66)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac24Rows03 : List (List Jet) := vac24Rows02 ++ [vac24Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows03_correct : jetRows 2 false 24 3 = vac24Rows03 := by
  rw [jetRows, vac24Rows02_correct]
  change vac24Rows02 ++ [jetStep 2 false 24 3 vac24Rows02] = vac24Rows02 ++ [vac24Row03]
  congr 1
  decide +kernel
def vac24Row04 : List Jet := [[(772/495),(2837/660),(-98161/3960)],[(5/297),(1499/2970),(-911/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac24Rows04 : List (List Jet) := vac24Rows03 ++ [vac24Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows04_correct : jetRows 2 false 24 4 = vac24Rows04 := by
  rw [jetRows, vac24Rows03_correct]
  change vac24Rows03 ++ [jetStep 2 false 24 4 vac24Rows03] = vac24Rows03 ++ [vac24Row04]
  congr 1
  decide +kernel
def vac24Row05 : List Jet := [[(-1204/2475),(-27622/2475),(-23191/9900)],[(215/2376),(-29149/118800),(-6819/4400)],[(1/300),(-1/600),(-1/75)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac24Rows05 : List (List Jet) := vac24Rows04 ++ [vac24Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows05_correct : jetRows 2 false 24 5 = vac24Rows05 := by
  rw [jetRows, vac24Rows04_correct]
  change vac24Rows04 ++ [jetStep 2 false 24 5 vac24Rows04] = vac24Rows04 ++ [vac24Row05]
  congr 1
  decide +kernel
def vac24Row06 : List Jet := [[(-54218/51975),(271279/34650),(589983/15400)],[(-49351/498960),(-2743673/4989600),(19953/15400)],[(-1/4536),(-49187/2494800),(-6773/831600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac24Rows06 : List (List Jet) := vac24Rows05 ++ [vac24Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows06_correct : jetRows 2 false 24 6 = vac24Rows06 := by
  rw [jetRows, vac24Rows05_correct]
  change vac24Rows05 ++ [jetStep 2 false 24 6 vac24Rows05] = vac24Rows05 ++ [vac24Row06]
  congr 1
  decide +kernel
def vac24Row07 : List Jet := [[(137204/72765),(1050667/242550),(-21189463/485100)],[(-47617/7484400),(4624303/4989600),(7023119/3742200)],[(-222463/52390800),(20773/6985440),(23894/297675)],[(-281/2910600),(-281/5821200),(281/646800)],[0,0,0],[0,0,0],[0,0,0]]
def vac24Rows07 : List (List Jet) := vac24Rows06 ++ [vac24Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows07_correct : jetRows 2 false 24 7 = vac24Rows07 := by
  rw [jetRows, vac24Rows06_correct]
  change vac24Rows06 ++ [jetStep 2 false 24 7 vac24Rows06] = vac24Rows06 ++ [vac24Row07]
  congr 1
  decide +kernel
def vac24Row08 : List Jet := [[(-4535453/3638250),(-476788909/29106000),(-62682947/19404000)],[(43048729/299376000),(-112781563/598752000),(-2845966313/598752000)],[(1349891/349272000),(2454749/63504000),(-11343763/698544000)],[(-17/1746360),(20267/29106000),(89563/87318000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac24Rows08 : List (List Jet) := vac24Rows07 ++ [vac24Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows08_correct : jetRows 2 false 24 8 = vac24Rows08 := by
  rw [jetRows, vac24Rows07_correct]
  change vac24Rows07 ++ [jetStep 2 false 24 8 vac24Rows07] = vac24Rows07 ++ [vac24Row08]
  congr 1
  decide +kernel
def vac24Row09 : List Jet := [[(-1190087/1488375),(86071/5544),(1298979988/16372125)],[(-1297363471/7544275200),(-108113952217/75442752000),(74425742981/37721376000)],[(4837673/1347192000),(-24392839/538876800),(-603657613/2694384000)],[(52363/269438400),(5300401/18860688000),(-13492079/3772137600)],[(667/209563200),(667/139708800),(-667/52390800)],[0,0,0],[0,0,0]]
def vac24Rows09 : List (List Jet) := vac24Rows08 ++ [vac24Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows09_correct : jetRows 2 false 24 9 = vac24Rows09 := by
  rw [jetRows, vac24Rows08_correct]
  change vac24Rows08 ++ [jetStep 2 false 24 9 vac24Rows08] = vac24Rows08 ++ [vac24Row09]
  congr 1
  decide +kernel
def vac24Row10 : List Jet := [[(42683849/14883750),(9317452327/1309770000),(-130558137653/1309770000)],[(-7886239309/226328256000),(466642384337/205752960000),(125698580123/13716864000)],[(-1403561813/113164128000),(-54592065823/1131641280000),(1001598247/3143448000)],[(-595613/5239080000),(-245415617/94303440000),(-325656281/94303440000)],[(1853/1257379200),(-1856279/62868960000),(-5017231/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac24Rows10 : List (List Jet) := vac24Rows09 ++ [vac24Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows10_correct : jetRows 2 false 24 10 = vac24Rows10 := by
  rw [jetRows, vac24Rows09_correct]
  change vac24Rows09 ++ [jetStep 2 false 24 10 vac24Rows09] = vac24Rows09 ++ [vac24Row10]
  congr 1
  decide +kernel
def vac24Row11 : List Jet := [[(-14673776/7441875),(-2227219559/54573750),(-1019610459341/14407470000)],[(97048398109/226328256000),(7340251382389/8298702720000),(-457585847015597/24896108160000)],[(817917433/165974054400),(351655172369/1659740544000),(1438134552203/2766234240000)],[(-41028179/74095560000),(56118329/49397040000),(65446661/2646270000)],[(-74911/5927644800),(-111125461/2074675680000),(44393051/230519520000)],[(-793/4610390400),(-793/1844156160),(793/1844156160)],[0,0,0]]
def vac24Rows11 : List (List Jet) := vac24Rows10 ++ [vac24Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows11_correct : jetRows 2 false 24 11 = vac24Rows11 := by
  rw [jetRows, vac24Rows10_correct]
  change vac24Rows10 ++ [jetStep 2 false 24 11 vac24Rows10] = vac24Rows10 ++ [vac24Row11]
  congr 1
  decide +kernel
def vac24Row12 : List Jet := [[(-112424/18225),(367846253/40095000),(11347803410983/24698520000)],[(-365630765803/1234517760000),(-32418066155623/3017710080000),(-4187300403765467/149376648960000)],[(384285587339/7468832448000),(77911268053/2766234240000),(-1234603946189/426790425600)],[(87024602387/74688324480000),(182126674909/9958443264000),(917413667129/149376648960000)],[(-37818167/4149351360000),(7913000309/24896108160000),(16008132977/12448054080000)],[(-14767/41493513600),(117539/42340320000),(250633/19758816000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac24Rows12 : List (List Jet) := vac24Rows11 ++ [vac24Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Rows12_correct : jetRows 2 false 24 12 = vac24Rows12 := by
  rw [jetRows, vac24Rows11_correct]
  change vac24Rows11 ++ [jetStep 2 false 24 12 vac24Rows11] = vac24Rows11 ++ [vac24Row12]
  congr 1
  decide +kernel
def vac24Coeffs : List Jet := [[(213380752/7441875),(-119377806704/81860625),(-25203488680961/3601867500)],[(113022851457907/6789847680000),(1813859305853431/16597405440000),(-73765011564683213/74688324480000)],[(-42674969419/466802028000),(15769610510077/1244805408000),(1562540940446603/37344162240000)],[(-24482679167/622402704000),(324733896353/6224027040000),(13701471587/5122656000)],[(-8725301/9261945000),(-417850481/55571670000),(235297933/6946458750)],[(-85/7409556),(-1411303/9261945000),(98699/514552500)],[(-8/36018675),(-4/7203735),(4/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac24Coeffs_correct : widthCoefficients 2 false 24 = vac24Coeffs := by
  rw [widthCoefficients,vac24Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
