import VOA.Classification.COne.OrbIcoWVac18

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac19Rows00 := jetRows 2 false 19 0
theorem vac19Rows00_correct : jetRows 2 false 19 0 = vac19Rows00 := rfl
def vac19Row01 : List Jet := [[(17/6),(-25/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac19Rows01 : List (List Jet) := vac19Rows00 ++ [vac19Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows01_correct : jetRows 2 false 19 1 = vac19Rows01 := by
  rw [jetRows, vac19Rows00_correct]
  change vac19Rows00 ++ [jetStep 2 false 19 1 vac19Rows00] = vac19Rows00 ++ [vac19Row01]
  congr 1
  decide +kernel
def vac19Row02 : List Jet := [[(175/132),(-343/33),(1225/132)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac19Rows02 : List (List Jet) := vac19Rows01 ++ [vac19Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows02_correct : jetRows 2 false 19 2 = vac19Rows02 := by
  rw [jetRows, vac19Rows01_correct]
  change vac19Rows01 ++ [jetStep 2 false 19 2 vac19Rows01] = vac19Rows01 ++ [vac19Row02]
  congr 1
  decide +kernel
def vac19Row03 : List Jet := [[(-3131/1980),(-1589/990),(3623/180)],[(-289/1980),(34/495),(85/396)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac19Rows03 : List (List Jet) := vac19Rows02 ++ [vac19Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows03_correct : jetRows 2 false 19 3 = vac19Rows03 := by
  rw [jetRows, vac19Rows02_correct]
  change vac19Rows02 ++ [jetStep 2 false 19 3 vac19Rows02] = vac19Rows02 ++ [vac19Row03]
  congr 1
  decide +kernel
def vac19Row04 : List Jet := [[(14263/71280),(20843/2640),(-34127/7920)],[(-161/1782),(1589/2970),(112/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac19Rows04 : List (List Jet) := vac19Rows03 ++ [vac19Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows04_correct : jetRows 2 false 19 4 = vac19Rows04 := by
  rw [jetRows, vac19Rows03_correct]
  change vac19Rows03 ++ [jetStep 2 false 19 4 vac19Rows03] = vac19Rows03 ++ [vac19Row04]
  congr 1
  decide +kernel
def vac19Row05 : List Jet := [[(1391911/1425600),(-33667/8100),(-1454443/79200)],[(767/7920),(35281/118800),(-49631/39600)],[(17/3600),(1/400),(-11/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac19Rows05 : List (List Jet) := vac19Rows04 ++ [vac19Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows05_correct : jetRows 2 false 19 5 = vac19Rows05 := by
  rw [jetRows, vac19Rows04_correct]
  change vac19Rows04 ++ [jetStep 2 false 19 5 vac19Rows04] = vac19Rows04 ++ [vac19Row05]
  congr 1
  decide +kernel
def vac19Row06 : List Jet := [[(-66767191/59875200),(-213782803/59875200),(20345741/1108800)],[(323/18711),(-4533757/7484400),(-210187/356400)],[(1703/427680),(-17683/1069200),(-193/8100)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac19Rows06 : List (List Jet) := vac19Rows05 ++ [vac19Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows06_correct : jetRows 2 false 19 6 = vac19Rows06 := by
  rw [jetRows, vac19Rows05_correct]
  change vac19Rows05 ++ [jetStep 2 false 19 6 vac19Rows05] = vac19Rows05 ++ [vac19Row06]
  congr 1
  decide +kernel
def vac19Row07 : List Jet := [[(77472671/251475840),(9636154343/1257379200),(1431804301/314344800)],[(-130714271/1257379200),(50722181/1257379200),(1325069267/628689600)],[(-9203/2494800),(-32387/1496880),(295457/7484400)],[(-4777/34927200),(-3653/17463600),(281/1455300)],[0,0,0],[0,0,0],[0,0,0]]
def vac19Rows07 : List (List Jet) := vac19Rows06 ++ [vac19Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows07_correct : jetRows 2 false 19 7 = vac19Rows07 := by
  rw [jetRows, vac19Rows06_correct]
  change vac19Rows06 ++ [jetStep 2 false 19 7 vac19Rows06] = vac19Rows06 ++ [vac19Row07]
  congr 1
  decide +kernel
def vac19Row08 : List Jet := [[(36623594153/50295168000),(-34522060967/8382528000),(-455588323633/16765056000)],[(206061049/2794176000),(512613529/698544000),(-73725299/133056000)],[(-107089/37422000),(52189/1944000),(1569203/18711000)],[(-1247/7484400),(1409/3402000),(4987/3402000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac19Rows08 : List (List Jet) := vac19Rows07 ++ [vac19Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows08_correct : jetRows 2 false 19 8 = vac19Rows08 := by
  rw [jetRows, vac19Rows07_correct]
  change vac19Rows07 ++ [jetStep 2 false 19 8 vac19Rows07] = vac19Rows07 ++ [vac19Row08]
  congr 1
  decide +kernel
def vac19Row09 : List Jet := [[(-140356738801/129330432000),(-40485558319/8622028800),(902353294483/43110144000)],[(644487713/11316412800),(-53517298427/75442752000),(-29640853741/9430344000)],[(1534144699/226328256000),(7453937/301771008),(-116739317/979776000)],[(1487/12700800),(25077361/18860688000),(-29611/75442752)],[(11339/2514758400),(28681/2514758400),(667/1257379200)],[0,0,0],[0,0,0]]
def vac19Rows09 : List (List Jet) := vac19Rows08 ++ [vac19Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows09_correct : jetRows 2 false 19 9 = vac19Rows09 := by
  rw [jetRows, vac19Rows08_correct]
  change vac19Rows08 ++ [jetStep 2 false 19 9 vac19Rows08] = vac19Rows08 ++ [vac19Row09]
  congr 1
  decide +kernel
def vac19Row10 : List Jet := [[(6078778354967/27159390720000),(133296913988461/13579695360000),(24809962810543/1131641280000)],[(-420933360181/2715939072000),(-7942457424173/13579695360000),(307475417231/82301184000)],[(7400531/113164128000),(-2958587869/41912640000),(-370972781/2357586000)],[(2641757/8981280000),(-211103701/282910320000),(-1451086697/188606880000)],[(97651/10777536000),(-4447/561330000),(-1537391/17962560000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac19Rows10 : List (List Jet) := vac19Rows09 ++ [vac19Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows10_correct : jetRows 2 false 19 10 = vac19Rows10 := by
  rw [jetRows, vac19Rows09_correct]
  change vac19Rows09 ++ [jetStep 2 false 19 10 vac19Rows09] = vac19Rows09 ++ [vac19Row10]
  congr 1
  decide +kernel
def vac19Row11 : List Jet := [[(3130215229829/2469035520000),(2515061372711/6789847680000),(-8053310180965013/149376648960000)],[(991799363/63228211200),(13421296845647/7113173760000),(2658975776977/508083840000)],[(-982211623/66389621760),(-397947779/15367968000),(1372544611/2857680000)],[(-8979659879/24896108160000),(-10552438979/2263282560000),(1851254243/2263282560000)],[(-394433/276623424000),(-21059671/188606880000),(-173318039/1383117120000)],[(-13481/55324684800),(-793/922078080),(-793/1229437440)],[0,0,0]]
def vac19Rows11 : List (List Jet) := vac19Rows10 ++ [vac19Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows11_correct : jetRows 2 false 19 11 = vac19Rows11 := by
  rw [jetRows, vac19Rows10_correct]
  change vac19Rows10 ++ [jetStep 2 false 19 11 vac19Rows10] = vac19Rows10 ++ [vac19Row11]
  congr 1
  decide +kernel
def vac19Row12 : List Jet := [[(-1805468296021/5925685248000),(-673140433424269/29628426240000),(-132112410672252337/1792519787520000)],[(367653810243707/896259893760000),(234721556638477/128037127680000),(-13751540643509887/896259893760000)],[(299355547709/358503957504000),(70651949915203/224064973440000),(1293042844469/1434015830016)],[(-428040092597/298753297920000),(764714681/284526950400),(856787342669/13579695360000)],[(-862404773/16597405440000),(-24686179291/149376648960000),(170676973499/149376648960000)],[(-234667/177829344000),(-884231/889146720000),(305269/29638224000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac19Rows12 : List (List Jet) := vac19Rows11 ++ [vac19Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Rows12_correct : jetRows 2 false 19 12 = vac19Rows12 := by
  rw [jetRows, vac19Rows11_correct]
  change vac19Rows11 ++ [jetStep 2 false 19 12 vac19Rows11] = vac19Rows11 ++ [vac19Row12]
  congr 1
  decide +kernel
def vac19Coeffs : List Jet := [[(343457544207817/14814213120000),(83387553007562011/162956344320000),(-8089235492729683/18291018240000)],[(-3288699782675723/448129946880000),(29508619631543/925888320000),(7268604297384041/14004060840000)],[(-1075243814297/2133952128000),(-903949528367/142263475200),(107464887552179/5334880320000)],[(611368133/74688324480),(-2285095487107/6224027040000),(-5447919281/6928416000)],[(405407503/389001690000),(-9338985731/1167005070000),(-49705693451/1167005070000)],[(135871/4322241000),(-3371279/16208403750),(-9232477/21611205000)],[(-34/108056025),(-8/7203735),(-2/2401245)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac19Coeffs_correct : widthCoefficients 2 false 19 = vac19Coeffs := by
  rw [widthCoefficients,vac19Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
