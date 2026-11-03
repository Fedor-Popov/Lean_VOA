import VOA.Classification.COne.OrbIcoWVac19

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac20Rows00 := jetRows 2 false 20 0
theorem vac20Rows00_correct : jetRows 2 false 20 0 = vac20Rows00 := rfl
def vac20Row01 : List Jet := [[(8/3),(-13/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac20Rows01 : List (List Jet) := vac20Rows00 ++ [vac20Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows01_correct : jetRows 2 false 20 1 = vac20Rows01 := by
  rw [jetRows, vac20Rows00_correct]
  change vac20Rows00 ++ [jetStep 2 false 20 1 vac20Rows00] = vac20Rows00 ++ [vac20Row01]
  congr 1
  decide +kernel
def vac20Row02 : List Jet := [[(10/11),(-221/22),(221/22)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac20Rows02 : List (List Jet) := vac20Rows01 ++ [vac20Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows02_correct : jetRows 2 false 20 2 = vac20Rows02 := by
  rw [jetRows, vac20Rows01_correct]
  change vac20Rows01 ++ [jetStep 2 false 20 2 vac20Rows01] = vac20Rows01 ++ [vac20Row02]
  congr 1
  decide +kernel
def vac20Row03 : List Jet := [[(-18/11),0,(1313/66)],[(-68/495),(17/198),(221/990)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac20Rows03 : List (List Jet) := vac20Rows02 ++ [vac20Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows03_correct : jetRows 2 false 20 3 = vac20Rows03 := by
  rw [jetRows, vac20Rows02_correct]
  change vac20Rows02 ++ [jetStep 2 false 20 3 vac20Rows02] = vac20Rows02 ++ [vac20Row03]
  congr 1
  decide +kernel
def vac20Row04 : List Jet := [[(35/66),(1547/198),(-19565/2376)],[(-97/1485),(1603/2970),(29/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac20Rows04 : List (List Jet) := vac20Rows03 ++ [vac20Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows04_correct : jetRows 2 false 20 4 = vac20Rows04 := by
  rw [jetRows, vac20Rows03_correct]
  change vac20Rows03 ++ [jetStep 2 false 20 4 vac20Rows03] = vac20Rows03 ++ [vac20Row04]
  congr 1
  decide +kernel
def vac20Row05 : List Jet := [[(87/110),(-65/11),(-4589/264)],[(1547/14850),(22811/118800),(-17869/13200)],[(1/225),(1/600),(-1/100)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac20Rows05 : List (List Jet) := vac20Rows04 ++ [vac20Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows05_correct : jetRows 2 false 20 5 = vac20Rows05 := by
  rw [jetRows, vac20Rows04_correct]
  change vac20Rows04 ++ [jetStep 2 false 20 5 vac20Rows04] = vac20Rows04 ++ [vac20Row05]
  congr 1
  decide +kernel
def vac20Row06 : List Jet := [[(-177/140),(-9529/4620),(87425/3696)],[(-79/8910),(-463577/712800),(-25409/89100)],[(1873/623700),(-44227/2494800),(-1627/75600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac20Rows06 : List (List Jet) := vac20Rows05 ++ [vac20Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows06_correct : jetRows 2 false 20 6 = vac20Rows06 := by
  rw [jetRows, vac20Rows05_correct]
  change vac20Rows05 ++ [jetStep 2 false 20 6 vac20Rows05] = vac20Rows05 ++ [vac20Row06]
  congr 1
  decide +kernel
def vac20Row07 : List Jet := [[(701/1078),(73723/8820),(-37479/21560)],[(-2741/28350),(123533/554400),(11567/5040)],[(-503/119070),(-2041/117600),(1291721/26195400)],[(-281/2182950),(-281/1587600),(281/1164240)],[0,0,0],[0,0,0],[0,0,0]]
def vac20Rows07 : List (List Jet) := vac20Rows06 ++ [vac20Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows07_correct : jetRows 2 false 20 7 = vac20Rows07 := by
  rw [jetRows, vac20Rows06_correct]
  change vac20Rows06 ++ [jetStep 2 false 20 7 vac20Rows06] = vac20Rows06 ++ [vac20Row07]
  congr 1
  decide +kernel
def vac20Row08 : List Jet := [[(22971/43120),(-1761409/258720),(-5008679/172480)],[(2537659/24948000),(134613371/199584000),(-89203831/66528000)],[(-1387/935550),(1942559/59875200),(859379/11975040)],[(-5683/43659000),(2887/5821200),(124739/87318000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac20Rows08 : List (List Jet) := vac20Rows07 ++ [vac20Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows08_correct : jetRows 2 false 20 8 = vac20Rows08 := by
  rw [jetRows, vac20Rows07_correct]
  change vac20Rows07 ++ [jetStep 2 false 20 8 vac20Rows07] = vac20Rows07 ++ [vac20Row08]
  congr 1
  decide +kernel
def vac20Row09 : List Jet := [[(-2795/2156),(-368173/129360),(77805949/2328480)],[(68045807/3143448000),(-8246421223/8382528000),(-456034879/157172400)],[(336773/47151720),(9801521/754427520),(-584062291/3772137600)],[(33067/214326000),(403603/342921600),(-20187169/18860688000)],[(667/157172400),(12673/1257379200),(-667/314344800)],[0,0,0],[0,0,0]]
def vac20Rows09 : List (List Jet) := vac20Rows08 ++ [vac20Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows09_correct : jetRows 2 false 20 9 = vac20Rows09 := by
  rw [jetRows, vac20Rows08_correct]
  change vac20Rows08 ++ [jetStep 2 false 20 9 vac20Rows08] = vac20Rows08 ++ [vac20Row09]
  congr 1
  decide +kernel
def vac20Row10 : List Jet := [[(113243/161700),(47711131/3880800),(181920271/13970880)],[(-5394808141/31434480000),(-560867543/2540160000),(1383179782223/251475840000)],[(-8676139/2886840000),(-90347171077/1131641280000),(-5990101319/62868960000)],[(18017/80831520),(-10585193/8083152000),(-20545537/2694384000)],[(114791/15717240000),(-860131/62868960000),(-5534201/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac20Rows10 : List (List Jet) := vac20Rows09 ++ [vac20Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows10_correct : jetRows 2 false 20 10 = vac20Rows10 := by
  rw [jetRows, vac20Rows09_correct]
  change vac20Rows09 ++ [jetStep 2 false 20 10 vac20Rows09] = vac20Rows09 ++ [vac20Row10]
  congr 1
  decide +kernel
def vac20Row11 : List Jet := [[(212381/169400),(-5290493/1016400),(-43692662/571725)],[(656902441/6286896000),(6446803650851/2766234240000),(8591917787479/2766234240000)],[(-44170907933/3112013520000),(162472043269/8298702720000),(2159072857093/3556586880000)],[(-25958939/51866892000),(-848051/207467568),(18366499/2963822400)],[(-406247/74095560000),(-221667661/2074675680000),(-14858159/230519520000)],[(-793/3457792800),(-793/1024531200),(-793/1844156160)],[0,0,0]]
def vac20Rows11 : List (List Jet) := vac20Rows10 ++ [vac20Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows11_correct : jetRows 2 false 20 11 = vac20Rows11 := by
  rw [jetRows, vac20Rows10_correct]
  change vac20Rows10 ++ [jetStep 2 false 20 11 vac20Rows10] = vac20Rows10 ++ [vac20Row11]
  congr 1
  decide +kernel
def vac20Row12 : List Jet := [[(-1427829/948640),(-289705923/9486400),(-3310302229/85377600)],[(24736196693/53887680000),(720381997037/3688312320000),(-407677674182591/16597405440000)],[(3534642773/233401014000),(1315033562503/3556586880000),(31757629988057/74688324480000)],[(-20197160989/18672081120000),(77737407989/9958443264000),(890711622259/13579695360000)],[(-5207401/106697606400),(-176320307/3556586880000),(1781787743/1333720080000)],[(-103483/94303440000),(-9971/296382240000),(1125953/98794080000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac20Rows12 : List (List Jet) := vac20Rows11 ++ [vac20Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Rows12_correct : jetRows 2 false 20 12 = vac20Rows12 := by
  rw [jetRows, vac20Rows11_correct]
  change vac20Rows11 ++ [jetStep 2 false 20 12 vac20Rows11] = vac20Rows11 ++ [vac20Row12]
  congr 1
  decide +kernel
def vac20Coeffs : List Jet := [[(5799573/118580),(10078679/21560),(-4785631721/2134440)],[(-72377929637/14113440000),(1444978435381/17563392000),(200221711347223/395176320000)],[(-30940149959/42436548000),(-4996662390431/1244805408000),(282975493768123/7468832448000)],[(-2810485691/333430020000),(-353117346347/889146720000),(-1212706316081/18672081120000)],[(9062819/16208403750),(-4057379587/389001690000),(-2889450353/97250422500)],[(150803/8104201875),(-13846471/64833615000),(-94376/300155625)],[(-32/108056025),(-4/4002075),(-4/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac20Coeffs_correct : widthCoefficients 2 false 20 = vac20Coeffs := by
  rw [widthCoefficients,vac20Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
