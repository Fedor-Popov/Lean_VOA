import VOA.Classification.COne.OrbIcoWVac30

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac31Rows00 := jetRows 2 false 31 0
theorem vac31Rows00_correct : jetRows 2 false 31 0 = vac31Rows00 := rfl
def vac31Row01 : List Jet := [[(5/6),(-37/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac31Rows01 : List (List Jet) := vac31Rows00 ++ [vac31Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows01_correct : jetRows 2 false 31 1 = vac31Rows01 := by
  rw [jetRows, vac31Rows00_correct]
  change vac31Rows00 ++ [jetStep 2 false 31 1 vac31Rows00] = vac31Rows00 ++ [vac31Row01]
  congr 1
  decide +kernel
def vac31Row02 : List Jet := [[(-221/132),(-73/33),(2701/132)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac31Rows02 : List (List Jet) := vac31Rows01 ++ [vac31Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows02_correct : jetRows 2 false 31 2 = vac31Rows02 := by
  rw [jetRows, vac31Rows01_correct]
  change vac31Rows01 ++ [jetStep 2 false 31 2 vac31Rows01] = vac31Rows01 ++ [vac31Row02]
  congr 1
  decide +kernel
def vac31Row03 : List Jet := [[(1501/1980),(1091/90),(-1087/396)],[(-17/396),(136/495),(629/1980)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac31Rows03 : List (List Jet) := vac31Rows02 ++ [vac31Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows03_correct : jetRows 2 false 31 3 = vac31Rows03 := by
  rw [jetRows, vac31Rows02_correct]
  change vac31Rows02 ++ [jetStep 2 false 31 3 vac31Rows02] = vac31Rows02 ++ [vac31Row03]
  congr 1
  decide +kernel
def vac31Row04 : List Jet := [[(81943/71280),(-54293/4752),(-335923/7920)],[(163/1782),(701/2970),(-1586/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac31Rows04 : List (List Jet) := vac31Rows03 ++ [vac31Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows04_correct : jetRows 2 false 31 4 = vac31Rows04 := by
  rw [jetRows, vac31Rows03_correct]
  change vac31Rows03 ++ [jetStep 2 false 31 4 vac31Rows03] = vac31Rows03 ++ [vac31Row04]
  congr 1
  decide +kernel
def vac31Row05 : List Jet := [[(-3808301/1425600),(-976157/356400),(15547063/237600)],[(-4069/118800),(-32429/39600),(-28219/39600)],[(1/720),(-3/400),(-23/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac31Rows05 : List (List Jet) := vac31Rows04 ++ [vac31Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows05_correct : jetRows 2 false 31 5 = vac31Rows05 := by
  rw [jetRows, vac31Rows04_correct]
  change vac31Rows04 ++ [jetStep 2 false 31 5 vac31Rows04] = vac31Rows04 ++ [vac31Row05]
  congr 1
  decide +kernel
def vac31Row06 : List Jet := [[(2772467/1088640),(1356384749/59875200),(-207412253/9979200)],[(-745753/7484400),(284027/467775),(10170793/2494800)],[(-9571/2993760),(-93829/7484400),(443/14175)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac31Rows06 : List (List Jet) := vac31Rows05 ++ [vac31Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows06_correct : jetRows 2 false 31 6 = vac31Rows06 := by
  rw [jetRows, vac31Rows05_correct]
  change vac31Rows05 ++ [jetStep 2 false 31 6 vac31Rows05] = vac31Rows05 ++ [vac31Row06]
  congr 1
  decide +kernel
def vac31Row07 : List Jet := [[(-306079709/1257379200),(-750206983/22861440),(-29533471307/314344800)],[(680149/3265920),(134167763/179625600),(-37742387/8164800)],[(242/297675),(10586/297675),(138779/1940400)],[(-281/6985440),(281/1587600),(281/363825)],[0,0,0],[0,0,0],[0,0,0]]
def vac31Rows07 : List (List Jet) := vac31Rows06 ++ [vac31Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows07_correct : jetRows 2 false 31 7 = vac31Rows07 := by
  rw [jetRows, vac31Rows06_correct]
  change vac31Rows06 ++ [jetStep 2 false 31 7 vac31Rows06] = vac31Rows06 ++ [vac31Row07]
  congr 1
  decide +kernel
def vac31Row08 : List Jet := [[(-178029021367/50295168000),(27349025593/1676505600),(3511258206623/16765056000)],[(-37998347/239500800),(-10228159/3991680),(-30158431/11404800)],[(6023701/1047816000),(-17627893/1047816000),(-252185639/1047816000)],[(5419/52390800),(146437/261954000),(-1373/2095632)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac31Rows08 : List (List Jet) := vac31Rows07 ++ [vac31Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows08_correct : jetRows 2 false 31 8 = vac31Rows08 := by
  rw [jetRows, vac31Rows07_correct]
  change vac31Rows07 ++ [jetStep 2 false 31 8 vac31Rows07] = vac31Rows07 ++ [vac31Row08]
  congr 1
  decide +kernel
def vac31Row09 : List Jet := [[(5892316907357/905313024000),(211922923183/6158592000),(-53053440005183/301771008000)],[(-3234483491/22632825600),(8606520451/3017710080),(135792922033/7544275200)],[(-365527643/32332608000),(-415170641/5388768000),(262644287/1539648000)],[(-199/48988800),(-2544337/1714608000),(-23202757/4715172000)],[(667/502951680),(-11339/2514758400),(-39353/1257379200)],[0,0,0],[0,0,0]]
def vac31Rows09 : List (List Jet) := vac31Rows08 ++ [vac31Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows09_correct : jetRows 2 false 31 9 = vac31Rows09 := by
  rw [jetRows, vac31Rows08_correct]
  change vac31Rows08 ++ [jetStep 2 false 31 9 vac31Rows08] = vac31Rows08 ++ [vac31Row09]
  congr 1
  decide +kernel
def vac31Row10 : List Jet := [[(-126430497782773/27159390720000),(-1349196115996679/13579695360000),(-114016577136373/565820640000)],[(8536791194083/13579695360000),(1828635637553/1234517760000),(-126383469621727/4526565120000)],[(9789161/2263282560),(9279140351/45265651200),(2775354317/4191264000)],[(-199129033/565820640000),(-2220847/94303440000),(891365569/62868960000)],[(-310367/75442752000),(-464719/15717240000),(478243/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac31Rows10 : List (List Jet) := vac31Rows09 ++ [vac31Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows10_correct : jetRows 2 false 31 10 = vac31Rows10 := by
  rw [jetRows, vac31Rows09_correct]
  change vac31Rows09 ++ [jetStep 2 false 31 10 vac31Rows09] = vac31Rows09 ++ [vac31Row10]
  congr 1
  decide +kernel
def vac31Row11 : List Jet := [[(-431156397138671/59750659584000),(3504068461015457/37344162240000),(147383403597787303/149376648960000)],[(-7295475641317/9053130240000),(-71734339495351/5532468480000),(-308247524329093/24896108160000)],[(159800606197/4979221632000),(-137625191617/1244805408000),(-771034518299/311201352000)],[(277037687/395176320000),(3370791833/395176320000),(2727513293/1185528960000)],[(-247921/118552896000),(2244587/25613280000),(123289801/276623424000)],[(-793/11064936960),(793/4610390400),(793/409812480)],[0,0,0]]
def vac31Rows11 : List (List Jet) := vac31Rows10 ++ [vac31Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows11_correct : jetRows 2 false 31 11 = vac31Rows11 := by
  rw [jetRows, vac31Rows10_correct]
  change vac31Rows10 ++ [jetStep 2 false 31 11 vac31Rows10] = vac31Rows10 ++ [vac31Row11]
  congr 1
  decide +kernel
def vac31Row12 : List Jet := [[(16222402507004329/512148510720000),(19124791739711951/73164072960000),(-289634157167858317/256074255360000)],[(-20167206332683/16295634432000),(20696853128764537/896259893760000),(206254182528014147/896259893760000)],[(-189252674349383/1792519787520000),(-270558903133577/224064973440000),(196616356076507/128037127680000)],[(17437869121/19916886528000),(-3653943714403/149376648960000),(-2475793904267/13579695360000)],[(6766768951/149376648960000),(4951791413/29875329792000),(-3243358051/1991688652800)],[(3839/10287648000),(471703/127020960000),(444527/148191120000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac31Rows12 : List (List Jet) := vac31Rows11 ++ [vac31Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Rows12_correct : jetRows 2 false 31 12 = vac31Rows12 := by
  rw [jetRows, vac31Rows11_correct]
  change vac31Rows11 ++ [jetStep 2 false 31 12 vac31Rows11] = vac31Rows11 ++ [vac31Row12]
  congr 1
  decide +kernel
def vac31Coeffs : List Jet := [[(-365026783274894507/1792519787520000),(937122824563367611/162956344320000),(44856345944415623147/896259893760000)],[(-831659638335497/17925197875200),(-5145820683205997/8962598937600),(144386964436399/70020304200)],[(747549876743/754427520000),(-1839004571540407/74688324480000),(-7900503172384769/37344162240000)],[(103611379573/1556006760000),(8589689988821/18672081120000),(-69196830440239/18672081120000)],[(29343691/83357505000),(2546739443/166715010000),(2141139757/55571670000)],[(-14603/1852389000),(16739/171517500),(465719/617463000)],[(-2/21611205),(8/36018675),(2/800415)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac31Coeffs_correct : widthCoefficients 2 false 31 = vac31Coeffs := by
  rw [widthCoefficients,vac31Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
