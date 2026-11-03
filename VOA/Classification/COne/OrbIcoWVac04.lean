import VOA.Classification.COne.OrbIcoWVac03

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac04Rows00 := jetRows 4 false 4 0
theorem vac04Rows00_correct : jetRows 4 false 4 0 = vac04Rows00 := rfl
def vac04Row01 : List Jet := [[(16/3),(-5/3),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows01 : List (List Jet) := vac04Rows00 ++ [vac04Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows01_correct : jetRows 4 false 4 1 = vac04Rows01 := by
  rw [jetRows, vac04Rows00_correct]
  change vac04Rows00 ++ [jetStep 4 false 4 1 vac04Rows00] = vac04Rows00 ++ [vac04Row01]
  congr 1
  decide +kernel
def vac04Row02 : List Jet := [[(370/33),(-551/66),(95/66),0,0],[(-1/22),(-1/22),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows02 : List (List Jet) := vac04Rows01 ++ [vac04Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows02_correct : jetRows 4 false 4 2 = vac04Rows02 := by
  rw [jetRows, vac04Rows01_correct]
  change vac04Rows01 ++ [jetStep 4 false 4 2 vac04Rows01] = vac04Rows01 ++ [vac04Row02]
  congr 1
  decide +kernel
def vac04Row03 : List Jet := [[(506/45),(-7972/495),(6719/990),(-19/22),0],[(-136/495),(-17/90),(17/198),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows03 : List (List Jet) := vac04Rows02 ++ [vac04Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows03_correct : jetRows 4 false 4 3 = vac04Rows03 := by
  rw [jetRows, vac04Rows02_correct]
  change vac04Rows02 ++ [jetStep 4 false 4 3 vac04Rows02] = vac04Rows02 ++ [vac04Row03]
  congr 1
  decide +kernel
def vac04Row04 : List Jet := [[(41681/8910),(-41681/2970),(47629/3960),(-34327/8910),(323/792)],[(-607/891),(-541/2970),(1229/2970),(-76/891),0],[(1/792),(1/396),(1/792),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows04 : List (List Jet) := vac04Rows03 ++ [vac04Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows04_correct : jetRows 4 false 4 4 = vac04Rows04 := by
  rw [jetRows, vac04Rows03_correct]
  change vac04Rows03 ++ [jetStep 4 false 4 4 vac04Rows03] = vac04Rows03 ++ [vac04Row04]
  congr 1
  decide +kernel
def vac04Row05 : List Jet := [[(-8317/44550),(-88268/22275),(535159/59400),(-562553/89100),(309671/178200)],[(-1286/1485),(12457/39600),(27689/39600),(-50059/118800),(95/1584)],[(2/225),(3/200),(1/300),(-1/360),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows05 : List (List Jet) := vac04Rows04 ++ [vac04Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows05_correct : jetRows 4 false 4 5 = vac04Rows05 := by
  rw [jetRows, vac04Rows04_correct]
  change vac04Rows04 ++ [jetStep 4 false 4 5 vac04Rows04] = vac04Rows04 ++ [vac04Row05]
  congr 1
  decide +kernel
def vac04Row06 : List Jet := [[(-106019/267300),(2483461/1871100),(3122431/2494800),(-2762989/680400),(20044909/7484400)],[(-205229/374220),(12871051/14968800),(190339/623700),(-5760043/7484400),(140102/467775)],[(10093/374220),(258359/7484400),(-21419/2494800),(-8741/680400),(703/213840)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows06 : List (List Jet) := vac04Rows05 ++ [vac04Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows06_correct : jetRows 4 false 4 6 = vac04Rows06 := by
  rw [jetRows, vac04Rows05_correct]
  change vac04Rows05 ++ [jetStep 4 false 4 6 vac04Rows05] = vac04Rows05 ++ [vac04Row06]
  congr 1
  decide +kernel
def vac04Row07 : List Jet := [[(13097/80190),(2190487/5613300),(-2425019/1603800),(186419/3207600),(4888963/3207600)],[(-3597313/39293100),(220293539/314344800),(-75253477/157172400),(-8022103/15717240),(8146469/14288400)],[(598753/13097700),(675841/20956320),(-13057/264600),(-807959/52390800),(92329/5239080)],[(-281/1091475),(-12083/17463600),(-281/529200),(-281/17463600),(281/3492720)],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows07 : List (List Jet) := vac04Rows06 ++ [vac04Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows07_correct : jetRows 4 false 4 7 = vac04Rows07 := by
  rw [jetRows, vac04Rows06_correct]
  change vac04Rows06 ++ [jetStep 4 false 4 7 vac04Rows06] = vac04Rows06 ++ [vac04Row07]
  congr 1
  decide +kernel
def vac04Row08 : List Jet := [[(420923/16038000),(-27395491/74844000),(-3232837/21384000),(929003393/898128000),(-3234977/13608000)],[(9657743/130977000),(156154573/1397088000),(-895755067/1397088000),(457122829/2095632000),(8873581/19958400)],[(12186547/261954000),(-21399683/2095632000),(-180477739/2095632000),(24583723/1047816000),(3227941/95256000)],[(-2423/2381400),(-55567/23814000),(-266071/261954000),(203909/261954000),(93733/261954000)],[(1/1330560),(1/332640),(1/221760),(1/332640),(1/1330560)],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows08 : List (List Jet) := vac04Rows07 ++ [vac04Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows08_correct : jetRows 4 false 4 8 = vac04Rows08 := by
  rw [jetRows, vac04Rows07_correct]
  change vac04Rows07 ++ [jetStep 4 false 4 8 vac04Rows07] = vac04Rows07 ++ [vac04Row08]
  congr 1
  decide +kernel
def vac04Row09 : List Jet := [[(-1356449/36085500),(-2360507/67359600),(251748187/673596000),(417251993/4041576000),(-323128693/538876800)],[(2535017/101039400),(-160541491/979776000),(-233285683/1347192000),(18029413673/32332608000),(-21318449/336798000)],[(195141647/7072758000),(-226341491/3772137600),(-1142628511/18860688000),(2710477717/28291032000),(130409/10777536)],[(-14891/5893965),(-84616859/18860688000),(1992187/3772137600),(2895167/857304000),(-42589/9430344000)],[(667/78586200),(39353/1257379200),(12673/314344800),(11339/628689600),(-667/314344800)],[0,0,0,0,0],[0,0,0,0,0]]
def vac04Rows09 : List (List Jet) := vac04Rows08 ++ [vac04Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows09_correct : jetRows 4 false 4 9 = vac04Rows09 := by
  rw [jetRows, vac04Rows08_correct]
  change vac04Rows08 ++ [jetStep 4 false 4 9 vac04Rows08] = vac04Rows08 ++ [vac04Row09]
  congr 1
  decide +kernel
def vac04Row10 : List Jet := [[(-1286189/270641250),(1702626307/30311820000),(31144129/262440000),(-5850830453/24249456000),(-5136941101/22044960000)],[(-119889401/8487309600),(-706323447559/6789847680000),(16410481471/90531302400),(2342024135293/6789847680000),(-3208683234623/6789847680000)],[(95641571/14145516000),(-12571048219/161663040000),(12313339/465696000),(31389335701/226328256000),(-78571687/1028764800)],[(-335046203/70727580000),(-480330217/94303440000),(226722983/31434480000),(129443707/20207880000),(-21392717/5239080000)],[(469631/9430344000),(941671/5715360000),(10482719/62868960000),(1446799/94303440000),(-1691003/31434480000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680),(-1/7983360)],[0,0,0,0,0]]
def vac04Rows10 : List (List Jet) := vac04Rows09 ++ [vac04Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows10_correct : jetRows 4 false 4 10 = vac04Rows10 := by
  rw [jetRows, vac04Rows09_correct]
  change vac04Rows09 ++ [jetStep 4 false 4 10 vac04Rows09] = vac04Rows09 ++ [vac04Row10]
  congr 1
  decide +kernel
def vac04Row11 : List Jet := [[(-56360027/11908215000),(7478039407/166715010000),(780837542/10419688125),(-3837499081/13337200800),(-119147348501/1333720080000)],[(-1318445341/77800338000),(-112148561677/2766234240000),(7424970950783/24896108160000),(2069798576141/24896108160000),(-6159631116379/8298702720000)],[(-4858487/1111433400),(-11523803807/142263475200),(525182644421/3556586880000),(88117330313/711317376000),(-7091837747/28452695040)],[(-250969031/28814940000),(-129281323/86444820000),(12171104261/518668920000),(534471067/172889640000),(-260046511/14407470000)],[(23850553/103733784000),(151165051/230519520000),(289983163/691558560000),(-303804037/1037337840000),(-102600851/345779280000)],[(-793/1728896400),(-793/368831232),(-793/204906240),(-793/251475840),(-793/922078080)],[0,0,0,0,0]]
def vac04Rows11 : List (List Jet) := vac04Rows10 ++ [vac04Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows11_correct : jetRows 4 false 4 11 = vac04Rows11 := by
  rw [jetRows, vac04Rows10_correct]
  change vac04Rows10 ++ [jetStep 4 false 4 11 vac04Rows10] = vac04Rows10 ++ [vac04Row11]
  congr 1
  decide +kernel
def vac04Row12 : List Jet := [[(-439979873/28579716000),(317005312223/2000580120000),(440809750993/2000580120000),(-4000808813279/4001160240000),(-41111869253/457275456000)],[(-609779772967/14004060840000),(-81789057480401/896259893760000),(391054035187579/448129946880000),(-29916626773613/224064973440000),(-3557571720209/1600464096000)],[(-18744078257/1120324867200),(-42669756348167/224064973440000),(5149031931899/8962598937600),(4183644192589/56016243360000),(-3829114888051/4073908608000)],[(-43526767621/1556006760000),(572502295039/29875329792000),(13235621226449/149376648960000),(-2103471536687/49792216320000),(-93134776919/1234517760000)],[(3577870493/2667440160000),(235164978137/74688324480000),(734674819/1556006760000),(-230640736427/74688324480000),(-19035575147/18672081120000)],[(-3999383/622402704000),(-24727481/889146720000),(-514133/11855289600),(-2185681/88914672000),(89801/22228668000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080),(1/31933440)]]
def vac04Rows12 : List (List Jet) := vac04Rows11 ++ [vac04Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Rows12_correct : jetRows 4 false 4 12 = vac04Rows12 := by
  rw [jetRows, vac04Rows11_correct]
  change vac04Rows11 ++ [jetStep 4 false 4 12 vac04Rows11] = vac04Rows11 ++ [vac04Row12]
  congr 1
  decide +kernel
def vac04Coeffs : List Jet := [[(15736526561/17862322500),(-357983596999/35724645000),(-327303430043/250072515000),(2736393628961/45467730000),(-125740221872017/2000580120000)],[(16661497911073/7002030420000),(1049325618107087/448129946880000),(-11372194589288959/224064973440000),(372056224381561/5601624336000),(5950560025942627/112032486720000)],[(453729371/540280125),(32452736906347/3734416224000),(-1529728866526697/37344162240000),(566555018678953/12448054080000),(22330791372797/5334880320000)],[(15774838151/11114334000),(-8040128808073/2667440160000),(-130337108287/106697606400),(4640921436841/889146720000),(-5353761046343/2667440160000)],[(-5966128996/72937816875),(-88147044121/1167005070000),(12722855347/97250422500),(90501141163/1167005070000),(-3734163821/41678752500)],[(990494/1620840375),(13002361/7203735000),(3578621/2701400625),(-35799839/64833615000),(-2013959/2701400625)],[(-64/108056025),(-4/1440747),(-4/800415),(-8/1964655),(-8/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac04Coeffs_correct : widthCoefficients 4 false 4 = vac04Coeffs := by
  rw [widthCoefficients,vac04Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
