import VOA.Classification.COne.OrbIcoWSelf07

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self08Rows00 := jetRows 2 true 8 0
theorem self08Rows00_correct : jetRows 2 true 8 0 = self08Rows00 := rfl
def self08Row01 : List Jet := [[(5/3),(-11/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self08Rows01 : List (List Jet) := self08Rows00 ++ [self08Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows01_correct : jetRows 2 true 8 1 = self08Rows01 := by
  rw [jetRows, self08Rows00_correct]
  change self08Rows00 ++ [jetStep 2 true 8 1 self08Rows00] = self08Rows00 ++ [self08Row01]
  congr 1
  decide +kernel
def self08Row02 : List Jet := [[(-21/22),(-91/44),(7/4)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self08Rows02 : List (List Jet) := self08Rows01 ++ [self08Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows02_correct : jetRows 2 true 8 2 = self08Rows02 := by
  rw [jetRows, self08Rows01_correct]
  change self08Rows01 ++ [jetStep 2 true 8 2 self08Rows01] = self08Rows01 ++ [self08Row02]
  congr 1
  decide +kernel
def self08Row03 : List Jet := [[(-4/5),(98/33),(167/165)],[(-17/198),(17/1980),(17/180)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self08Rows03 : List (List Jet) := self08Rows02 ++ [self08Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows03_correct : jetRows 2 true 8 3 = self08Rows03 := by
  rw [jetRows, self08Rows02_correct]
  change self08Rows02 ++ [jetStep 2 true 8 3 self08Rows02] = self08Rows02 ++ [self08Row03]
  congr 1
  decide +kernel
def self08Row04 : List Jet := [[(1759/990),(-283/1485),(-14071/3960)],[(14/297),(259/1485),(7/297)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self08Rows04 : List (List Jet) := self08Rows03 ++ [self08Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows04_correct : jetRows 2 true 8 4 = self08Rows04 := by
  rw [jetRows, self08Rows03_correct]
  change self08Rows03 ++ [jetStep 2 true 8 4 self08Rows03] = self08Rows03 ++ [self08Row04]
  congr 1
  decide +kernel
def self08Row05 : List Jet := [[(-2099/1650),(-13873/3960),(15157/6600)],[(7571/118800),(-28033/237600),(-871/3300)],[(1/360),(1/400),(-1/300)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self08Rows05 : List (List Jet) := self08Rows04 ++ [self08Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows05_correct : jetRows 2 true 8 5 = self08Rows05 := by
  rw [jetRows, self08Rows04_correct]
  change self08Rows04 ++ [jetStep 2 true 8 5 self08Rows04] = self08Rows04 ++ [self08Row05]
  congr 1
  decide +kernel
def self08Row06 : List Jet := [[(-337/924),(1334077/277200),(105031/41580)],[(-619147/4989600),(-1608337/9979200),(331433/1425600)],[(-101/71280),(-5659/712800),(-1813/237600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self08Rows06 : List (List Jet) := self08Rows05 ++ [self08Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows06_correct : jetRows 2 true 8 6 = self08Rows06 := by
  rw [jetRows, self08Rows05_correct]
  change self08Rows05 ++ [jetStep 2 true 8 6 self08Rows05] = self08Rows05 ++ [self08Row06]
  congr 1
  decide +kernel
def self08Row07 : List Jet := [[(248417/121275),(-2794163/1455300),(-62805977/8731800)],[(15931/258720),(5575613/13970880),(954997/4365900)],[(-6979/2138400),(7087/9979200),(470903/29937600)],[(-281/3492720),(-5339/34927200),(281/11642400)],[0,0,0],[0,0,0],[0,0,0]]
def self08Rows07 : List (List Jet) := self08Rows06 ++ [self08Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows07_correct : jetRows 2 true 8 7 = self08Rows07 := by
  rw [jetRows, self08Rows06_correct]
  change self08Rows06 ++ [jetStep 2 true 8 7 self08Rows06] = self08Rows06 ++ [self08Row07]
  congr 1
  decide +kernel
def self08Row08 : List Jet := [[(-494156/202125),(-509048/121275),(94343441/14553000)],[(3259811/31046400),(-69118909/254016000),(-314262049/399168000)],[(1705871/299376000),(9809563/598752000),(449149/299376000)],[(1/28350),(313/1039500),(3401/6237000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self08Rows08 : List (List Jet) := self08Rows07 ++ [self08Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows08_correct : jetRows 2 true 8 8 = self08Rows08 := by
  rw [jetRows, self08Rows07_correct]
  change self08Rows07 ++ [jetStep 2 true 8 8 self08Rows07] = self08Rows07 ++ [self08Row08]
  congr 1
  decide +kernel
def self08Row09 : List Jet := [[(10387/16500),(4260407/462000),(24433721/8316000)],[(-139402261/558835200),(-1659264917/4572288000),(37059801913/50295168000)],[(-547553/1178793000),(-893327947/37721376000),(-44411351/979776000)],[(613993/3772137600),(8108053/37721376000),(-5553211/9430344000)],[(667/251475840),(19343/2514758400),(667/157172400)],[0,0,0],[0,0,0]]
def self08Rows09 : List (List Jet) := self08Rows08 ++ [self08Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows09_correct : jetRows 2 true 8 9 = self08Rows09 := by
  rw [jetRows, self08Rows08_correct]
  change self08Rows08 ++ [jetStep 2 true 8 9 self08Rows08] = self08Rows08 ++ [self08Row09]
  congr 1
  decide +kernel
def self08Row10 : List Jet := [[(72992543/24255000),(-23760607/3880800),(-30492293039/1746360000)],[(1455511601/9313920000),(193160651413/167650560000),(96284366777/125737920000)],[(-571149829/45265651200),(-4048463999/452656512000),(16855804621/251475840000)],[(-10284937/40415760000),(-65149919/51438240000),(-277153237/188606880000)],[(-1297/1796256000),(-226243/17962560000),(-650939/17962560000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self08Rows10 : List (List Jet) := self08Rows09 ++ [self08Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows10_correct : jetRows 2 true 8 10 = self08Rows10 := by
  rw [jetRows, self08Rows09_correct]
  change self08Rows09 ++ [jetStep 2 true 8 10 self08Rows09] = self08Rows09 ++ [self08Row10]
  congr 1
  decide +kernel
def self08Row11 : List Jet := [[(-3953248/741125),(-256064489/22233750),(985707221/53361000)],[(5612504437/14636160000),(-29384431411/37635840000),(-2807333551793/790352640000)],[(97030021727/4979221632000),(63675039793/663896217600),(1564046810027/24896108160000)],[(-203775769/691558560000),(630764191/691558560000),(1656427681/307359360000)],[(-4916897/414935136000),(-142618423/4149351360000),(83057/17075520000)],[(-793/5532468480),(-10309/18441561600),(-793/1229437440)],[0,0,0]]
def self08Rows11 : List (List Jet) := self08Rows10 ++ [self08Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows11_correct : jetRows 2 true 8 11 = self08Rows11 := by
  rw [jetRows, self08Rows10_correct]
  change self08Rows10 ++ [jetStep 2 true 8 11 self08Rows10] = self08Rows10 ++ [self08Row11]
  congr 1
  decide +kernel
def self08Row12 : List Jet := [[(-96331911/29645000),(12176768539/355740000),(29447681057/640332000)],[(-55382044247/49177497600),(-363207999839/90326016000),(61111821760991/33194810880000)],[(2558465223983/74688324480000),(-1874813647397/16597405440000),(-10432621174433/18672081120000)],[(60087532837/29875329792000),(395331509/51732172800),(20981765579/11950131916800)],[(1084724173/74688324480000),(8051709443/49792216320000),(15433172203/37344162240000)],[(-1093/14819112000),(134623/148191120000),(236899/49397040000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self08Rows12 : List (List Jet) := self08Rows11 ++ [self08Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Rows12_correct : jetRows 2 true 8 12 = self08Rows12 := by
  rw [jetRows, self08Rows11_correct]
  change self08Rows11 ++ [jetStep 2 true 8 12 self08Rows11] = self08Rows11 ++ [self08Row12]
  congr 1
  decide +kernel
def self08Coeffs : List Jet := [[(-437356569/3705625),(-11693462591/22233750),(215309986091/228690000)],[(87389055329/4553472000),(-17115100372333/409812480000),(-568221102020647/3688312320000)],[(4874149444523/5334880320000),(385859802649/80831520000),(-30566625925067/21339521280000)],[(-186341446597/9336040560000),(464071865071/4149351360000),(4275214894277/10669760640000)],[(-205313281/194500845000),(-1623672359/778003380000),(27119629/5239080000)],[(-208667/12966723000),(-8935453/129667230000),(-2017/39690000)],[(-4/21611205),(-26/36018675),(-2/2401245)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self08Coeffs_correct : widthCoefficients 2 true 8 = self08Coeffs := by
  rw [widthCoefficients,self08Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
