import VOA.Classification.COne.OrbIcoWVac14

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac15Rows00 := jetRows 3 false 15 0
theorem vac15Rows00_correct : jetRows 3 false 15 0 = vac15Rows00 := rfl
def vac15Row01 : List Jet := [[(7/2),(-7/2),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac15Rows01 : List (List Jet) := vac15Rows00 ++ [vac15Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows01_correct : jetRows 3 false 15 1 = vac15Rows01 := by
  rw [jetRows, vac15Rows00_correct]
  change vac15Rows00 ++ [jetStep 3 false 15 1 vac15Rows00] = vac15Rows00 ++ [vac15Row01]
  congr 1
  decide +kernel
def vac15Row02 : List Jet := [[(145/44),(-123/11),(287/44),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac15Rows02 : List (List Jet) := vac15Rows01 ++ [vac15Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows02_correct : jetRows 3 false 15 2 = vac15Rows02 := by
  rw [jetRows, vac15Rows01_correct]
  change vac15Rows01 ++ [jetStep 3 false 15 2 vac15Rows01] = vac15Rows01 ++ [vac15Row02]
  congr 1
  decide +kernel
def vac15Row03 : List Jet := [[(-7/12),(-521/66),(2507/132),(-287/33)],[(-119/660),0,(119/660),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac15Rows03 : List (List Jet) := vac15Rows02 ++ [vac15Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows03_correct : jetRows 3 false 15 3 = vac15Rows03 := by
  rw [jetRows, vac15Rows02_correct]
  change vac15Rows02 ++ [jetStep 3 false 15 3 vac15Rows02] = vac15Rows02 ++ [vac15Row03]
  congr 1
  decide +kernel
def vac15Row04 : List Jet := [[(-1645/1584),(2723/528),(13721/1584),(-12203/528)],[(-619/2970),(1373/2970),(422/1485),(-574/1485)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac15Rows04 : List (List Jet) := vac15Rows03 ++ [vac15Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows04_correct : jetRows 3 false 15 4 = vac15Rows04 := by
  rw [jetRows, vac15Rows03_correct]
  change vac15Rows03 ++ [jetStep 3 false 15 4 vac15Rows03] = vac15Rows03 ++ [vac15Row04]
  congr 1
  decide +kernel
def vac15Row05 : List Jet := [[(31087/31680),(17899/7920),(-44315/3168),(-3413/792)],[(1411/118800),(77081/118800),(-9529/13200),(-89681/118800)],[(7/1200),(7/1200),(-7/1200),(-7/1200)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac15Rows05 : List (List Jet) := vac15Rows04 ++ [vac15Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows05_correct : jetRows 3 false 15 5 = vac15Rows05 := by
  rw [jetRows, vac15Rows04_correct]
  change vac15Rows04 ++ [jetStep 3 false 15 5 vac15Rows04] = vac15Rows04 ++ [vac15Row05]
  congr 1
  decide +kernel
def vac15Row06 : List Jet := [[(-24353/190080),(-319427/63360),(-64697/221760),(94415/4032)],[(51437/498960),(-123373/623700),(-363463/277200),(2558467/2494800)],[(42859/4989600),(-22487/2494800),(-1502/51975),(817/226800)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac15Rows06 : List (List Jet) := vac15Rows05 ++ [vac15Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows06_correct : jetRows 3 false 15 6 = vac15Rows06 := by
  rw [jetRows, vac15Rows05_correct]
  change vac15Rows05 ++ [jetStep 3 false 15 6 vac15Rows05] = vac15Rows05 ++ [vac15Row06]
  congr 1
  decide +kernel
def vac15Row07 : List Jet := [[(-21583/38016),(951941/443520),(9750001/776160),(-10122583/1552320)],[(-26010569/419126400),(-22073633/46569600),(31235279/41912640),(473916833/209563200)],[(3067/2619540),(-142189/4365900),(-10813/4762800),(3629573/52390800)],[(-281/1663200),(-281/831600),0,(281/831600)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac15Rows07 : List (List Jet) := vac15Rows06 ++ [vac15Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows07_correct : jetRows 3 false 15 7 = vac15Rows07 := by
  rw [jetRows, vac15Rows06_correct]
  change vac15Rows06 ++ [jetStep 3 false 15 7 vac15Rows06] = vac15Rows06 ++ [vac15Row07]
  congr 1
  decide +kernel
def vac15Row08 : List Jet := [[(901523/1520640),(1897693/760320),(-1498633/168960),(-40146187/1774080)],[(-376916081/8382528000),(913345333/2095632000),(11153392559/8382528000),(-647778179/349272000)],[(-89461/13970880),(-422027/69854400),(6210707/69854400),(231151/5821200)],[(-383/1134000),(-1/25200),(16987/12474000),(11801/12474000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac15Rows08 : List (List Jet) := vac15Rows07 ++ [vac15Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows08_correct : jetRows 3 false 15 8 = vac15Rows08 := by
  rw [jetRows, vac15Rows07_correct]
  change vac15Rows07 ++ [jetStep 3 false 15 8 vac15Rows07] = vac15Rows07 ++ [vac15Row08]
  congr 1
  decide +kernel
def vac15Row09 : List Jet := [[(-200941/5474304),(-16654339/4257792),(-9139028911/1341204480),(10000221929/447068160)],[(479807737/5388768000),(1868726473/6858432000),(-2472425887/1508855040),(-3850349011/1197504000)],[(1382123/2155507200),(324746341/7544275200),(492952003/15088550400),(-275872087/1257379200)],[(-3201839/18860688000),(1116061/754427520),(9830069/4715172000),(-30901/10584000)],[(667/119750400),(667/39916800),(667/59875200),(-667/59875200)],[0,0,0,0],[0,0,0,0]]
def vac15Rows09 : List (List Jet) := vac15Rows08 ++ [vac15Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows09_correct : jetRows 3 false 15 9 = vac15Rows09 := by
  rw [jetRows, vac15Rows08_correct]
  change vac15Rows08 ++ [jetStep 3 false 15 9 vac15Rows08] = vac15Rows08 ++ [vac15Row09]
  congr 1
  decide +kernel
def vac15Row10 : List Jet := [[(-133604653/273715200),(1696093/27371520),(157091579/10886400),(6614829911/335301120)],[(-2546690297/646652160000),(-65631988039/92378880000),(-286597800131/215550720000),(429899924573/92378880000)],[(2282762443/282910320000),(2348106623/1131641280000),(-11910080849/62868960000),(-26748361093/161663040000)],[(910631/2514758400),(34637501/18860688000),(-33066709/7544275200),(-99455617/9430344000)],[(310529/17962560000),(4553/204120000),(-1039211/17962560000),(-81371/748440000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac15Rows10 : List (List Jet) := vac15Rows09 ++ [vac15Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows10_correct : jetRows 3 false 15 10 = vac15Rows10 := by
  rw [jetRows, vac15Rows09_correct]
  change vac15Rows09 ++ [jetStep 3 false 15 10 vac15Rows09] = vac15Rows09 ++ [vac15Row10]
  congr 1
  decide +kernel
def vac15Row11 : List Jet := [[(639912637/3010867200),(186765899/41817600),(62884223657/10538035200),(-20650554407/501811200)],[(-66987391081/569053900800),(-4087745072069/16597405440000),(86008479048691/24896108160000),(91405334941013/12448054080000)],[(-2689367059/1185528960000),(-190359599519/2074675680000),(-6261857687/57629880000),(1525182140077/2074675680000)],[(792808487/1659740544000),(-513102847/184415616000),(-4830524077/331948108800),(14086881913/1659740544000)],[(108650813/4149351360000),(-167464261/2074675680000),(-15705337/51226560000),(-6219167/1037337840000)],[(-793/2634508800),(-793/658627200),(-793/526901760),0],[0,0,0,0]]
def vac15Rows11 : List (List Jet) := vac15Rows10 ++ [vac15Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows11_correct : jetRows 3 false 15 11 = vac15Rows11 := by
  rw [jetRows, vac15Rows10_correct]
  change vac15Rows10 ++ [jetStep 3 false 15 11 vac15Rows10] = vac15Rows10 ++ [vac15Row11]
  congr 1
  decide +kernel
def vac15Row12 : List Jet := [[(5266866059/7226081280),(136785958343/36130406400),(-3038940159613/126456422400),(-6358285868701/63228211200)],[(-2818016048489/42679042560000),(22373478627407/14226347520000),(2161231277383097/298753297920000),(-1663082345266109/149376648960000)],[(-406526537359/17071617024000),(-313652921207/3556586880000),(32086796203849/42679042560000),(81972581308279/42679042560000)],[(-218019190369/298753297920000),(-132289923277/9958443264000),(513488106599/149376648960000),(18856532567993/149376648960000)],[(-10785149/3319481088000),(-560652317/1016167680000),(-1510359469/7113173760000),(6046379047/2371057920000)],[(-698393/296382240000),(-1740181/296382240000),(138829/49397040000),(582383/29638224000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac15Rows12 : List (List Jet) := vac15Rows11 ++ [vac15Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Rows12_correct : jetRows 3 false 15 12 = vac15Rows12 := by
  rw [jetRows, vac15Rows11_correct]
  change vac15Rows11 ++ [jetStep 3 false 15 12 vac15Rows11] = vac15Rows11 ++ [vac15Row12]
  congr 1
  decide +kernel
def vac15Coeffs : List Jet := [[(-25054505021/1204346880),(-52103707201/1204346880),(613781785973/602173440),(233758092157/191600640)],[(683973811453/3048503040000),(-36559167559027/711317376000),(-254917495565933/4668020280000),(29546832208451111/37344162240000)],[(1199636491399/2133952128000),(-332365650821/237105792000),(-201811922891093/7468832448000),(139680650770333/7468832448000)],[(58006548967/1556006760000),(1303462171391/6224027040000),(-3145023609239/2074675680000),(-12558665972863/6224027040000)],[(31207037/21611205000),(5363376343/389001690000),(-21626415157/389001690000),(-7200308293/129667230000)],[(7063159/64833615000),(-2185973/32416807500),(-5178769/7203735000),(-8431037/32416807500)],[(-2/5145525),(-8/5145525),(-2/1029105),0]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac15Coeffs_correct : widthCoefficients 3 false 15 = vac15Coeffs := by
  rw [widthCoefficients,vac15Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
