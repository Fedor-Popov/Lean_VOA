import VOA.Classification.COne.OrbIcoWVac26

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac27Rows00 := jetRows 2 false 27 0
theorem vac27Rows00_correct : jetRows 2 false 27 0 = vac27Rows00 := rfl
def vac27Row01 : List Jet := [[(3/2),(-11/2),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac27Rows01 : List (List Jet) := vac27Rows00 ++ [vac27Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows01_correct : jetRows 2 false 27 1 = vac27Rows01 := by
  rw [jetRows, vac27Rows00_correct]
  change vac27Rows00 ++ [jetStep 2 false 27 1 vac27Rows00] = vac27Rows00 ++ [vac27Row01]
  congr 1
  decide +kernel
def vac27Row02 : List Jet := [[(-51/44),(-65/11),(65/4)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac27Rows02 : List (List Jet) := vac27Rows01 ++ [vac27Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows02_correct : jetRows 2 false 27 2 = vac27Rows02 := by
  rw [jetRows, vac27Rows01_correct]
  change vac27Rows01 ++ [jetStep 2 false 27 2 vac27Rows01] = vac27Rows01 ++ [vac27Row02]
  congr 1
  decide +kernel
def vac27Row03 : List Jet := [[(-23/44),(287/30),(2293/220)],[(-17/220),(34/165),(17/60)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac27Rows03 : List (List Jet) := vac27Rows02 ++ [vac27Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows03_correct : jetRows 2 false 27 3 = vac27Rows03 := by
  rw [jetRows, vac27Rows02_correct]
  change vac27Rows02 ++ [jetStep 2 false 27 3 vac27Rows02] = vac27Rows02 ++ [vac27Row03]
  congr 1
  decide +kernel
def vac27Row04 : List Jet := [[(315/176),(-1183/880),(-94157/2640)],[(59/990),(1253/2970),(-892/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac27Rows04 : List (List Jet) := vac27Rows03 ++ [vac27Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows04_correct : jetRows 2 false 27 4 = vac27Rows04 := by
  rw [jetRows, vac27Rows03_correct]
  change vac27Rows03 ++ [jetStep 2 false 27 4 vac27Rows03] = vac27Rows03 ++ [vac27Row04]
  congr 1
  decide +kernel
def vac27Row05 : List Jet := [[(-1161/704),(-4889/440),(562519/26400)],[(371/7920),(-64703/118800),(-5077/3600)],[(1/400),(-1/240),(-19/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac27Rows05 : List (List Jet) := vac27Rows04 ++ [vac27Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows05_correct : jetRows 2 false 27 5 = vac27Rows05 := by
  rw [jetRows, vac27Rows04_correct]
  change vac27Rows04 ++ [jetStep 2 false 27 5 vac27Rows04] = vac27Rows04 ++ [vac27Row05]
  congr 1
  decide +kernel
def vac27Row06 : List Jet := [[(1059/9856),(224299/13440),(34896097/1108800)],[(-1541/11880),(-65147/356400),(104633/39600)],[(-289/151200),(-9131/498960),(433/69300)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac27Rows06 : List (List Jet) := vac27Rows05 ++ [vac27Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows06_correct : jetRows 2 false 27 6 = vac27Rows06 := by
  rw [jetRows, vac27Rows05_correct]
  change vac27Rows05 ++ [jetStep 2 false 27 6 vac27Rows05] = vac27Rows05 ++ [vac27Row06]
  congr 1
  decide +kernel
def vac27Row07 : List Jet := [[(132987/68992),(-2695421/344960),(-104961049/1293600)],[(385691/3991680),(10078183/8553600),(-30277/29937600)],[(-9059/3492720),(984917/52390800),(4668707/52390800)],[(-281/3880800),(281/5821200),(281/485100)],[0,0,0],[0,0,0],[0,0,0]]
def vac27Rows07 : List (List Jet) := vac27Rows06 ++ [vac27Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows07_correct : jetRows 2 false 27 7 = vac27Rows07 := by
  rw [jetRows, vac27Rows06_correct]
  change vac27Rows06 ++ [jetStep 2 false 27 7 vac27Rows06] = vac27Rows06 ++ [vac27Row07]
  congr 1
  decide +kernel
def vac27Row08 : List Jet := [[(-149937/50176),(-3861625/275968),(2739852499/41395200)],[(221219/3193344),(-15563687/11975040),(-7217468947/1197504000)],[(5791/924000),(135539/5544000),(-28163/252000)],[(1571/29106000),(62303/87318000),(3631/7938000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac27Rows08 : List (List Jet) := vac27Rows07 ++ [vac27Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows08_correct : jetRows 2 false 27 8 = vac27Rows08 := by
  rw [jetRows, vac27Rows07_correct]
  change vac27Rows07 ++ [jetStep 2 false 27 8 vac27Rows07] = vac27Rows07 ++ [vac27Row08]
  congr 1
  decide +kernel
def vac27Row09 : List Jet := [[(5446015/3311616),(1712251297/49674240),(40400459609/745113600)],[(-6766813/25147584),(-125266013/274337280),(174558245989/18860688000)],[(-69647693/25147584000),(-3020156011/37721376000),(-2232286109/15088550400)],[(172889/1257379200),(-902917/1714608000),(-45565241/9430344000)],[(667/279417600),(667/838252800),(-8671/419126400)],[0,0,0],[0,0,0]]
def vac27Rows09 : List (List Jet) := vac27Rows08 ++ [vac27Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows09_correct : jetRows 2 false 27 9 = vac27Rows09 := by
  rw [jetRows, vac27Rows08_correct]
  change vac27Rows08 ++ [jetStep 2 false 27 9 vac27Rows08] = vac27Rows08 ++ [vac27Row09]
  congr 1
  decide +kernel
def vac27Row10 : List Jet := [[(5549365/2207744),(-145312109/5519360),(-14460251779/62092800)],[(3247168307/12070840320),(682825208809/181062604800),(534029578919/301771008000)],[(-301353739/26943840000),(53343623653/1131641280000),(60706276727/94303440000)],[(-551071/1796256000),(-870011/384912000),(86340137/26943840000)],[(-68743/41912640000),(-266083/7858620000),(-6885377/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac27Rows10 : List (List Jet) := vac27Rows09 ++ [vac27Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows10_correct : jetRows 2 false 27 10 = vac27Rows10 := by
  rw [jetRows, vac27Rows09_correct]
  change vac27Rows09 ++ [jetStep 2 false 27 10 vac27Rows09] = vac27Rows09 ++ [vac27Row10]
  congr 1
  decide +kernel
def vac27Row11 : List Jet := [[(-3479185/495616),(-183967549/4336640),(83890554823/390297600)],[(71278136827/265558487040),(-9448473335423/1991688652800),(-179663066617823/4979221632000)],[(23984971729/922078080000),(155953836197/691558560000),(-9307175629/21170160000)],[(-2352601/20490624000),(1082429849/184415616000),(962668061/35925120000)],[(-420239/39517632000),(14575507/2074675680000),(490116481/1383117120000)],[(-793/6147187200),(-793/4610390400),(793/737662464)],[0,0,0]]
def vac27Rows11 : List (List Jet) := vac27Rows10 ++ [vac27Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows11_correct : jetRows 2 false 27 11 = vac27Rows11 := by
  rw [jetRows, vac27Rows10_correct]
  change vac27Rows10 ++ [jetStep 2 false 27 11 vac27Rows10] = vac27Rows10 ++ [vac27Row11]
  congr 1
  decide +kernel
def vac27Row12 : List Jet := [[(237566405/291422208),(230368557829/1457111040),(25339982988673/32784998400)],[(-172022361463/113810780160),(-11852530545577/1086375628800),(3219334560194531/59750659584000)],[(582262917893/39833773056000),(-1086495403663/1524251520000),(-1253405646919177/298753297920000)],[(218804420897/99584432640000),(247408624241/29875329792000),(-13477849563617/149376648960000)],[(8407331/338722560000),(255362299/646652160000),(887486189/2371057920000)],[(31231/691558560000),(1125667/296382240000),(102691/9879408000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac27Rows12 : List (List Jet) := vac27Rows11 ++ [vac27Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Rows12_correct : jetRows 2 false 27 12 = vac27Rows12 := by
  rw [jetRows, vac27Rows11_correct]
  change vac27Rows11 ++ [jetStep 2 false 27 12 vac27Rows11] = vac27Rows11 ++ [vac27Row12]
  congr 1
  decide +kernel
def vac27Coeffs : List Jet := [[(-10125410175/48570368),(-110269910031/48570368),(1253698302957/121425920)],[(159543919375/11381078016),(-760143578171/3048503040),(-117092486896247/53348803200)],[(3092775535189/2263282560000),(941565629378837/74688324480000),(-20632091714419/298753297920)],[(-466089563/148191120000),(510983347223/889146720000),(13210502751763/6224027040000)],[(-121202029/129667230000),(1224824879/389001690000),(933479053/14407470000)],[(-70789/4322241000),(-415606/8104201875),(11496383/21611205000)],[(-2/12006225),(-8/36018675),(2/1440747)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac27Coeffs_correct : widthCoefficients 2 false 27 = vac27Coeffs := by
  rw [widthCoefficients,vac27Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
