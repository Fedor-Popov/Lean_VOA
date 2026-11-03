import VOA.Classification.COne.OrbIcoWSelf00

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self01Rows00 := jetRows 2 true 1 0
theorem self01Rows00_correct : jetRows 2 true 1 0 = self01Rows00 := rfl
def self01Row01 : List Jet := [[(17/6),(-2/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self01Rows01 : List (List Jet) := self01Rows00 ++ [self01Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows01_correct : jetRows 2 true 1 1 = self01Rows01 := by
  rw [jetRows, self01Rows00_correct]
  change self01Rows00 ++ [jetStep 2 true 1 1 self01Rows00] = self01Rows00 ++ [self01Row01]
  congr 1
  decide +kernel
def self01Row02 : List Jet := [[(175/132),(-175/132),(7/33)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self01Rows02 : List (List Jet) := self01Rows01 ++ [self01Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows02_correct : jetRows 2 true 1 2 = self01Rows02 := by
  rw [jetRows, self01Rows01_correct]
  change self01Rows01 ++ [jetStep 2 true 1 2 self01Rows01] = self01Rows01 ++ [self01Row02]
  congr 1
  decide +kernel
def self01Row03 : List Jet := [[(-3131/1980),(28/99),(457/1980)],[(-289/1980),(-221/1980),(17/495)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self01Rows03 : List (List Jet) := self01Rows02 ++ [self01Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows03_correct : jetRows 2 true 1 3 = self01Rows03 := by
  rw [jetRows, self01Rows02_correct]
  change self01Rows02 ++ [jetStep 2 true 1 3 self01Rows02] = self01Rows02 ++ [self01Row03]
  congr 1
  decide +kernel
def self01Row04 : List Jet := [[(14263/71280),(1345/1584),(-7517/23760)],[(-161/1782),(-14/1485),(203/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self01Rows04 : List (List Jet) := self01Rows03 ++ [self01Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows04_correct : jetRows 2 true 1 4 = self01Rows04 := by
  rw [jetRows, self01Rows03_correct]
  change self01Rows03 ++ [jetStep 2 true 1 4 self01Rows03] = self01Rows03 ++ [self01Row04]
  congr 1
  decide +kernel
def self01Row05 : List Jet := [[(1391911/1425600),(-1406129/1425600),(11281/475200)],[(767/7920),(21499/237600),(-967/39600)],[(17/3600),(1/120),(1/400)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self01Rows05 : List (List Jet) := self01Rows04 ++ [self01Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows05_correct : jetRows 2 true 1 5 = self01Rows05 := by
  rw [jetRows, self01Rows04_correct]
  change self01Rows04 ++ [jetStep 2 true 1 5 self01Rows04] = self01Rows04 ++ [self01Row05]
  congr 1
  decide +kernel
def self01Row06 : List Jet := [[(-66767191/59875200),(3222269/14968800),(857771/2494800)],[(323/18711),(-1773361/29937600),(-26129/475200)],[(1703/427680),(10147/2138400),(-281/142560)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self01Rows06 : List (List Jet) := self01Rows05 ++ [self01Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows06_correct : jetRows 2 true 1 6 = self01Rows06 := by
  rw [jetRows, self01Rows05_correct]
  change self01Rows05 ++ [jetStep 2 true 1 6 self01Rows05] = self01Rows05 ++ [self01Row06]
  congr 1
  decide +kernel
def self01Row07 : List Jet := [[(77472671/251475840),(192692029/251475840),(-290337151/628689600)],[(-130714271/1257379200),(-23444621/628689600),(47788997/628689600)],[(-9203/2494800),(-1337/171072),(-107867/29937600)],[(-4777/34927200),(-13207/34927200),(-3653/11642400)],[0,0,0],[0,0,0],[0,0,0]]
def self01Rows07 : List (List Jet) := self01Rows06 ++ [self01Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows07_correct : jetRows 2 true 1 7 = self01Rows07 := by
  rw [jetRows, self01Rows06_correct]
  change self01Rows06 ++ [jetStep 2 true 1 7 self01Rows06] = self01Rows06 ++ [self01Row07]
  congr 1
  decide +kernel
def self01Row08 : List Jet := [[(36623594153/50295168000),(-3206115349/2794176000),(2886729011/16765056000)],[(206061049/2794176000),(178735901/1676505600),(-5904131/598752000)],[(-107089/37422000),(-231683/199584000),(66853/12474000)],[(-1247/7484400),(-7069/18711000),(-1417/9355500)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self01Rows08 : List (List Jet) := self01Rows07 ++ [self01Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows08_correct : jetRows 2 true 1 8 = self01Rows08 := by
  rw [jetRows, self01Rows07_correct]
  change self01Rows07 ++ [jetStep 2 true 1 8 self01Rows07] = self01Rows07 ++ [self01Row08]
  congr 1
  decide +kernel
def self01Row09 : List Jet := [[(-140356738801/129330432000),(1436283257/3079296000),(2459193499/6158592000)],[(644487713/11316412800),(-10621322477/150885504000),(-312501503/3353011200)],[(1534144699/226328256000),(217323221/18860688000),(6453487/5388768000)],[(1487/12700800),(15731641/37721376000),(74765/150885504)],[(11339/2514758400),(667/39293100),(28681/1257379200)],[0,0,0],[0,0,0]]
def self01Rows09 : List (List Jet) := self01Rows08 ++ [self01Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows09_correct : jetRows 2 true 1 9 = self01Rows09 := by
  rw [jetRows, self01Rows08_correct]
  change self01Rows08 ++ [jetStep 2 true 1 9 self01Rows08] = self01Rows08 ++ [self01Row09]
  congr 1
  decide +kernel
def self01Row10 : List Jet := [[(6078778354967/27159390720000),(26045666632319/27159390720000),(-7197999103777/9053130240000)],[(-420933360181/2715939072000),(-508638973783/6789847680000),(535390723781/4526565120000)],[(7400531/113164128000),(-3290501339/452656512000),(-570082253/50295168000)],[(2641757/8981280000),(31263937/51438240000),(522821/6286896000)],[(97651/10777536000),(49373/1632960000),(25453/816480000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self01Rows10 : List (List Jet) := self01Rows09 ++ [self01Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows10_correct : jetRows 2 true 1 10 = self01Rows10 := by
  rw [jetRows, self01Rows09_correct]
  change self01Rows09 ++ [jetStep 2 true 1 10 self01Rows09] = self01Rows09 ++ [self01Row10]
  congr 1
  decide +kernel
def self01Row11 : List Jet := [[(3130215229829/2469035520000),(-889336406291/543187814400),(3903753680591/13579695360000)],[(991799363/63228211200),(301654359817/1580705280000),(256193520067/4742115840000)],[(-982211623/66389621760),(-190423743131/9958443264000),(37943696657/4979221632000)],[(-8979659879/24896108160000),(-3492919489/2766234240000),(-8737745479/6224027040000)],[(-394433/276623424000),(-64691651/4149351360000),(-29946941/691558560000)],[(-13481/55324684800),(-793/683020800),(-793/368831232)],[0,0,0]]
def self01Rows11 : List (List Jet) := self01Rows10 ++ [self01Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows11_correct : jetRows 2 true 1 11 = self01Rows11 := by
  rw [jetRows, self01Rows10_correct]
  change self01Rows10 ++ [jetStep 2 true 1 11 self01Rows10] = self01Rows10 ++ [self01Row11]
  congr 1
  decide +kernel
def self01Row12 : List Jet := [[(-1805468296021/5925685248000),(-18621766272059/13036507545600),(278920160162683/162956344320000)],[(367653810243707/896259893760000),(12450601987093/128037127680000),(-304091622539923/896259893760000)],[(299355547709/358503957504000),(25233181770373/896259893760000),(8382946630001/224064973440000)],[(-428040092597/298753297920000),(-122381998547/42679042560000),(-3707350469/33194810880000)],[(-862404773/16597405440000),(-2759201297/14937664896000),(-31629902363/149376648960000)],[(-234667/177829344000),(-646561/111143340000),(-2784773/296382240000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self01Rows12 : List (List Jet) := self01Rows11 ++ [self01Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Rows12_correct : jetRows 2 true 1 12 = self01Rows12 := by
  rw [jetRows, self01Rows11_correct]
  change self01Rows11 ++ [jetStep 2 true 1 12 self01Rows11] = self01Rows11 ++ [self01Row12]
  congr 1
  decide +kernel
def self01Coeffs : List Jet := [[(343457544207817/14814213120000),(-1893102789980389/81478172160000),(113660302938757/11639738880000)],[(-3288699782675723/448129946880000),(1560123107444213/179251978752000),(-2504065156549681/896259893760000)],[(-1075243814297/2133952128000),(-5555846068513/10669760640000),(106888708411/444573360000)],[(611368133/74688324480),(-676069081703/37344162240000),(-31809531211/711317376000)],[(405407503/389001690000),(731869819/424365480000),(-3570672361/4668020280000)],[(135871/4322241000),(1020449/11787930000),(1918073/43222410000)],[(-34/108056025),(-2/1334025),(-4/1440747)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self01Coeffs_correct : widthCoefficients 2 true 1 = self01Coeffs := by
  rw [widthCoefficients,self01Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
