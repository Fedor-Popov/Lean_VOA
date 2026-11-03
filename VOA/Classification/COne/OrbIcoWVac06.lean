import VOA.Classification.COne.OrbIcoWVac05

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac06Rows00 := jetRows 4 false 6 0
theorem vac06Rows00_correct : jetRows 4 false 6 0 = vac06Rows00 := rfl
def vac06Row01 : List Jet := [[5,-2,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows01 : List (List Jet) := vac06Rows00 ++ [vac06Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows01_correct : jetRows 4 false 6 1 = vac06Rows01 := by
  rw [jetRows, vac06Rows00_correct]
  change vac06Rows00 ++ [jetStep 4 false 6 1 vac06Rows00] = vac06Rows00 ++ [vac06Row01]
  congr 1
  decide +kernel
def vac06Row02 : List Jet := [[(19/2),(-207/22),(23/11),0,0],[(-1/22),(-1/22),0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows02 : List (List Jet) := vac06Rows01 ++ [vac06Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows02_correct : jetRows 4 false 6 2 = vac06Rows02 := by
  rw [jetRows, vac06Rows01_correct]
  change vac06Rows01 ++ [jetStep 4 false 6 2 vac06Rows01] = vac06Rows01 ++ [vac06Row02]
  congr 1
  decide +kernel
def vac06Row03 : List Jet := [[(118/15),(-5383/330),(613/66),(-23/15),0],[(-17/66),(-17/110),(17/165),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows03 : List (List Jet) := vac06Rows02 ++ [vac06Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows03_correct : jetRows 4 false 6 3 = vac06Rows03 := by
  rw [jetRows, vac06Rows02_correct]
  change vac06Rows02 ++ [jetStep 4 false 6 3 vac06Rows02] = vac06Rows02 ++ [vac06Row03]
  congr 1
  decide +kernel
def vac06Row04 : List Jet := [[(77/45),(-987/88),(29113/1980),(-259/40),(161/180)],[(-172/297),(-49/2970),(1303/2970),(-184/1485),0],[(1/792),(1/396),(1/792),0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows04 : List (List Jet) := vac06Rows03 ++ [vac06Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows04_correct : jetRows 4 false 6 4 = vac06Rows04 := by
  rw [jetRows, vac06Rows03_correct]
  change vac06Rows03 ++ [jetStep 4 false 6 4 vac06Rows03] = vac06Rows03 ++ [vac06Row04]
  congr 1
  decide +kernel
def vac06Row05 : List Jet := [[(-839/900),(-13423/39600),(320273/39600),(-33929/3600),(13081/3600)],[(-73619/118800),(69263/118800),(7177/13200),(-65639/118800),(23/216)],[(1/120),(1/75),(1/600),(-1/300),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows05 : List (List Jet) := vac06Rows04 ++ [vac06Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows05_correct : jetRows 4 false 6 5 = vac06Rows05 := by
  rw [jetRows, vac06Rows04_correct]
  change vac06Rows04 ++ [jetStep 4 false 6 5 vac06Rows04] = vac06Rows04 ++ [vac06Row05]
  congr 1
  decide +kernel
def vac06Row06 : List Jet := [[(53/7560),(389701/184800),(-498173/277200),(-33269/8400),(10403/2100)],[(-180211/712800),(329567/356400),(-7289/39600),(-28541/35640),(346597/712800)],[(11479/498960),(60157/2494800),(-13319/831600),(-6161/498960),(851/178200)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264),0],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows06 : List (List Jet) := vac06Rows05 ++ [vac06Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows06_correct : jetRows 4 false 6 6 = vac06Rows06 := by
  rw [jetRows, vac06Rows05_correct]
  change vac06Rows05 ++ [jetStep 4 false 6 6 vac06Rows05] = vac06Rows05 ++ [vac06Row06]
  congr 1
  decide +kernel
def vac06Row07 : List Jet := [[(7976/33075),(-102733/194040),(-2777149/1293600),(596/245),(27163/17640)],[(2551/38880),(2020133/4989600),(-853717/935550),(-29581/299376),(418181/554400)],[(3503659/104781600),(4031/646800),(-2930717/52390800),(-12191/6548850),(762661/34927200)],[(-281/1164240),(-3653/5821200),(-281/646800),(281/5821200),(281/2910600)],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows07 : List (List Jet) := vac06Rows06 ++ [vac06Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows07_correct : jetRows 4 false 6 7 = vac06Rows07 := by
  rw [jetRows, vac06Rows06_correct]
  change vac06Rows06 ++ [jetStep 4 false 6 7 vac06Rows06] = vac06Rows06 ++ [vac06Row07]
  congr 1
  decide +kernel
def vac06Row08 : List Jet := [[(-276749/2646000),(-542123/1058400),(14732021/14112000),(2517981/1568000),(-7007593/3528000)],[(7302349/119750400),(-5038021/23950080),(-1872989/3742200),(82844827/99792000),(121535621/598752000)],[(2497387/99792000),(-3966491/99792000),(-222931/3564000),(29677/504000),(2575231/99792000)],[(-3803/4365900),(-52457/29106000),(-1241/3492720),(90551/87318000),(2777/9702000)],[(1/1330560),(1/332640),(1/221760),(1/332640),(1/1330560)],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows08 : List (List Jet) := vac06Rows07 ++ [vac06Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows08_correct : jetRows 4 false 6 8 = vac06Rows08 := by
  rw [jetRows, vac06Rows07_correct]
  change vac06Rows07 ++ [jetStep 4 false 6 8 vac06Rows07] = vac06Rows07 ++ [vac06Row08]
  congr 1
  decide +kernel
def vac06Row09 : List Jet := [[(-924473/23814000),(403927/1323000),(265734701/381024000),(-138005501/127008000),(-401803/317520)],[(-431541809/15088550400),(-290915621/1508855040),(4902676511/15088550400),(8068445687/12573792000),(-11095965779/15088550400)],[(41320151/9430344000),(-586043503/9430344000),(115524361/9430344000),(30312493/261954000),(-385199377/9430344000)],[(-7125193/3772137600),(-46731857/18860688000),(10820393/4715172000),(888347/285768000),(-2389403/2694384000)],[(667/83825280),(667/23284800),(667/19051200),(667/52390800),(-667/139708800)],[0,0,0,0,0],[0,0,0,0,0]]
def vac06Rows09 : List (List Jet) := vac06Rows08 ++ [vac06Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows09_correct : jetRows 4 false 6 9 = vac06Rows09 := by
  rw [jetRows, vac06Rows08_correct]
  change vac06Rows08 ++ [jetStep 4 false 6 9 vac06Rows08] = vac06Rows08 ++ [vac06Row09]
  congr 1
  decide +kernel
def vac06Row10 : List Jet := [[(7566449/238140000),(38181529/238140000),(-1257547493/3810240000),(-193609529/190512000),(843622763/1270080000)],[(-64240357507/2263282560000),(143313930043/2263282560000),(344310450683/754427520000),(-25625049809/90531302400),(-419181915353/452656512000)],[(-11655481/1293304320),(-92899039/2829103200),(946556249/8382528000),(34028987227/565820640000),(-191484547589/1131641280000)],[(-1832869/641520000),(-4760771/13471920000),(8301467/962280000),(14062861/6735960000),(-29183879/4490640000)],[(538283/12573792000),(8323099/62868960000),(862273/7858620000),(-100553/3492720000),(-3959201/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680),(-1/7983360)],[0,0,0,0,0]]
def vac06Rows10 : List (List Jet) := vac06Rows09 ++ [vac06Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows10_correct : jetRows 4 false 6 10 = vac06Rows10 := by
  rw [jetRows, vac06Rows09_correct]
  change vac06Rows09 ++ [jetStep 4 false 6 10 vac06Rows09] = vac06Rows09 ++ [vac06Row10]
  congr 1
  decide +kernel
def vac06Row11 : List Jet := [[(33571/1701000),(3356357/124740000),(-706606541/1496880000),(-776473069/1995840000),(468734801/299376000)],[(-7943302223/2263282560000),(3631591147/22861440000),(4237172185207/24896108160000),(-24381733867877/24896108160000),(-537212798401/1659740544000)],[(-18386557901/1659740544000),(29643240569/1659740544000),(13608329117/79035264000),(-1228059048647/8298702720000),(-2242265278417/8298702720000)],[(-7761114587/2074675680000),(302355029/43222410000),(4880691467/296382240000),(-3411622763/259334460000),(-3883417129/230519520000)],[(10428587/59276448000),(891621047/2074675680000),(2090293/23051952000),(-452062757/1037337840000),(-3639371/17146080000)],[(-793/1844156160),(-18239/9220780800),(-793/230519520),(-793/307359360),(-793/1844156160)],[0,0,0,0,0]]
def vac06Rows11 : List (List Jet) := vac06Rows10 ++ [vac06Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows11_correct : jetRows 4 false 6 11 = vac06Rows11 := by
  rw [jetRows, vac06Rows10_correct]
  change vac06Rows10 ++ [jetStep 4 false 6 11 vac06Rows10] = vac06Rows10 ++ [vac06Row11]
  congr 1
  decide +kernel
def vac06Row12 : List Jet := [[(9822761/178605000),(2245102763/31434480000),(-41121674681/31434480000),(-48553531067/100590336000),(2435905671373/502951680000)],[(34984547/70543872000),(1631881325869/4526565120000),(-671732398397/37344162240000),(-29067552265501/10669760640000),(4908760254589/4526565120000)],[(-1432697232667/74688324480000),(93694241099/889146720000),(49511892789179/149376648960000),(-125998340647591/149376648960000),(-16834440059117/49792216320000)],[(-243039141241/29875329792000),(595820389183/16597405440000),(4015798861013/149376648960000),(-1289419323803/13579695360000),(-145472711761/7113173760000)],[(117207089/131725440000),(264869791/177829344000),(-16822987/12933043200),(-218864/77182875),(1326448537/3556586880000)],[(-144007/25933446000),(-6784543/296382240000),(-3179257/98794080000),(-352351/29638224000),(2641/244944000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080),(1/31933440)]]
def vac06Rows12 : List (List Jet) := vac06Rows11 ++ [vac06Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Rows12_correct : jetRows 4 false 6 12 = vac06Rows12 := by
  rw [jetRows, vac06Rows11_correct]
  change vac06Rows11 ++ [jetStep 4 false 6 12 vac06Rows11] = vac06Rows11 ++ [vac06Row12]
  congr 1
  decide +kernel
def vac06Coeffs : List Jet := [[(-172438981/59535000),(-19880003/238140000),(734076659227/10478160000),(-2549700544663/41912640000),(-8403928675127/41912640000)],[(85012577/1410877440),(-229153918877/12933043200),(2493393067171/106697606400),(4697190043747/42679042560),(-145973427151949/711317376000)],[(31923554831941/37344162240000),(-75647726530447/12448054080000),(-249219809129869/37344162240000),(179321949411109/3394923840000),(-32276829615841/592764480000)],[(6934135049/20207880000),(-25745794937/11547360000),(4196275251479/2074675680000),(1841025732853/565820640000),(-29367773095139/6224027040000)],[(-387501704/8104201875),(-393202133/389001690000),(25022734837/194500845000),(-979809203/129667230000),(-20646771323/194500845000)],[(6247499/12966723000),(40754671/32416807500),(243517/480249000),(-30780527/32416807500),(-3465241/5893965000)],[(-4/7203735),(-92/36018675),(-32/7203735),(-8/2401245),(-4/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac06Coeffs_correct : widthCoefficients 4 false 6 = vac06Coeffs := by
  rw [widthCoefficients,vac06Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
