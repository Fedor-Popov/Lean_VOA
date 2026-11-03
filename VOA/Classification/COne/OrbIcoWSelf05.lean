import VOA.Classification.COne.OrbIcoWSelf04

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self05Rows00 := jetRows 2 true 5 0
theorem self05Rows00_correct : jetRows 2 true 5 0 = self05Rows00 := rfl
def self05Row01 : List Jet := [[(13/6),(-4/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self05Rows01 : List (List Jet) := self05Rows00 ++ [self05Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows01_correct : jetRows 2 true 5 1 = self05Rows01 := by
  rw [jetRows, self05Rows00_correct]
  change self05Rows00 ++ [jetStep 2 true 5 1 self05Rows00] = self05Rows00 ++ [self05Row01]
  congr 1
  decide +kernel
def self05Row02 : List Jet := [[(-7/44),(-93/44),(10/11)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self05Rows02 : List (List Jet) := self05Rows01 ++ [self05Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows02_correct : jetRows 2 true 5 2 = self05Rows02 := by
  rw [jetRows, self05Rows01_correct]
  change self05Rows01 ++ [jetStep 2 true 5 2 self05Rows01] = self05Rows01 ++ [self05Row02]
  congr 1
  decide +kernel
def self05Row03 : List Jet := [[(-63/44),(49/33),(119/132)],[(-221/1980),(-17/396),(34/495)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self05Rows03 : List (List Jet) := self05Rows02 ++ [self05Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows03_correct : jetRows 2 true 5 3 = self05Rows03 := by
  rw [jetRows, self05Rows02_correct]
  change self05Rows02 ++ [jetStep 2 true 5 3 self05Rows02] = self05Rows02 ++ [self05Row03]
  congr 1
  decide +kernel
def self05Row04 : List Jet := [[(721/528),(4919/4752),(-845/528)],[(-1/990),(38/297),(223/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self05Rows04 : List (List Jet) := self05Rows03 ++ [self05Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows04_correct : jetRows 2 true 5 4 = self05Rows04 := by
  rw [jetRows, self05Rows03_correct]
  change self05Rows03 ++ [jetStep 2 true 5 4 self05Rows03] = self05Rows03 ++ [self05Row04]
  congr 1
  decide +kernel
def self05Row05 : List Jet := [[(-7/64),(-16597/6336),(8747/31680)],[(3941/39600),(4291/237600),(-5971/39600)],[(13/3600),(1/200),(-1/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self05Rows05 : List (List Jet) := self05Rows04 ++ [self05Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows05_correct : jetRows 2 true 5 5 = self05Rows05 := by
  rw [jetRows, self05Rows04_correct]
  change self05Rows04 ++ [jetStep 2 true 5 5 self05Rows04] = self05Rows04 ++ [self05Row05]
  congr 1
  decide +kernel
def self05Row06 : List Jet := [[(-1743/1408),(5875/3168),(100703/55440)],[(-6073/75600),(-639173/3326400),(29683/9979200)],[(89/184800),(-20777/4989600),(-4267/554400)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self05Rows06 : List (List Jet) := self05Rows05 ++ [self05Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows06_correct : jetRows 2 true 5 6 = self05Rows06 := by
  rw [jetRows, self05Rows05_correct]
  change self05Rows05 ++ [jetStep 2 true 5 6 self05Rows05] = self05Rows05 ++ [self05Row06]
  congr 1
  decide +kernel
def self05Row07 : List Jet := [[(2323/1408),(217765/266112),(-12454777/4656960)],[(-339173/9313920),(510215/2794176),(5651027/23284800)],[(-1879/415800),(-191003/29937600),(132613/29937600)],[(-3653/34927200),(-8711/34927200),(-281/2328480)],[0,0,0],[0,0,0],[0,0,0]]
def self05Rows07 : List (List Jet) := self05Rows06 ++ [self05Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows07_correct : jetRows 2 true 5 7 = self05Rows07 := by
  rw [jetRows, self05Rows06_correct]
  change self05Rows06 ++ [jetStep 2 true 5 7 self05Rows06] = self05Rows06 ++ [self05Row07]
  congr 1
  decide +kernel
def self05Row08 : List Jet := [[(-7659/11264),(-404897/118272),(23631233/24837120)],[(136845967/931392000),(200379731/2794176000),(-428907929/1397088000)],[(44393/16632000),(7849423/598752000),(1904951/149688000)],[(-1049/29106000),(3763/43659000),(1741/4365900)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self05Rows08 : List (List Jet) := self05Rows07 ++ [self05Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows08_correct : jetRows 2 true 5 8 = self05Rows08 := by
  rw [jetRows, self05Rows07_correct]
  change self05Rows07 ++ [jetStep 2 true 5 8 self05Rows07] = self05Rows07 ++ [self05Row08]
  congr 1
  decide +kernel
def self05Row09 : List Jet := [[(-26887/22528),(341141/101376),(8576063/3041280)],[(-512912227/4191264000),(-2850865757/7185024000),(-671956751/16765056000)],[(960013/186278400),(-32511599/18860688000),(-922318223/37721376000)],[(59483/299376000),(2894431/5388768000),(595873/2694384000)],[(8671/2514758400),(667/57153600),(15341/1257379200)],[0,0,0],[0,0,0]]
def self05Rows09 : List (List Jet) := self05Rows08 ++ [self05Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows09_correct : jetRows 2 true 5 9 = self05Rows09 := by
  rw [jetRows, self05Rows08_correct]
  change self05Rows08 ++ [jetStep 2 true 5 9 self05Rows08] = self05Rows08 ++ [self05Row09]
  congr 1
  decide +kernel
def self05Row10 : List Jet := [[(29785/12288),(1175551/1216512),(-685527811/127733760)],[(-17178085109/167650560000),(95419584163/251475840000),(116621583943/167650560000)],[(-159037/14553000),(-63643382939/2263282560000),(-1728464167/754427520000)],[(-1941497/62868960000),(-373938101/565820640000),(-13258817/8573040000)],[(4271/1552320000),(181793/125737920000),(-1140109/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self05Rows10 : List (List Jet) := self05Rows09 ++ [self05Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows10_correct : jetRows 2 true 5 10 = self05Rows10 := by
  rw [jetRows, self05Rows09_correct]
  change self05Rows09 ++ [jetStep 2 true 5 10 self05Rows09] = self05Rows09 ++ [self05Row10]
  congr 1
  decide +kernel
def self05Row11 : List Jet := [[(-315721/495616),(-16326685/2230272),(162919231/234178560)],[(1398252652579/3688312320000),(1042398606019/2212987392000),(-115960438661/143700480000)],[(-338422501/184415616000),(1985438983217/49792216320000),(2080632016789/24896108160000)],[(-12657737/20490624000),(-973163161/754427520000),(1651404697/2074675680000)],[(-794021/65862720000),(-6052129/118552896000),(-6520937/98794080000)],[(-10309/55324684800),(-15067/18441561600),(-793/614718720)],[0,0,0]]
def self05Rows11 : List (List Jet) := self05Rows10 ++ [self05Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows11_correct : jetRows 2 true 5 11 = self05Rows11 := by
  rw [jetRows, self05Rows10_correct]
  change self05Rows10 ++ [jetStep 2 true 5 11 self05Rows10] = self05Rows10 ++ [self05Row11]
  congr 1
  decide +kernel
def self05Row12 : List Jet := [[(-11276601/1982464),(12607825/5947392),(15045034871/936714240)],[(383834971/9032601600),(-1775150265167/948423168000),(-119777016239/58544640000)],[(99254626379/2011806720000),(27893192914967/298753297920000),(-3279582359261/37344162240000)],[(311485441/526901760000),(144738430289/27159390720000),(2997685264723/298753297920000)],[(-351552409/16597405440000),(8773691/6789847680000),(31583384081/149376648960000)],[(-119663/230519520000),(-25079/18523890000),(2269/3951763200)],[(1/479001600),(1/79833600),(1/31933440)]]
def self05Rows12 : List (List Jet) := self05Rows11 ++ [self05Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Rows12_correct : jetRows 2 true 5 12 = self05Rows12 := by
  rw [jetRows, self05Rows11_correct]
  change self05Rows11 ++ [jetStep 2 true 5 12 self05Rows11] = self05Rows11 ++ [self05Row12]
  congr 1
  decide +kernel
def self05Coeffs : List Jet := [[(65675925/991232),(-404097505/1486848),(1034804183/13381632)],[(20703880383521/1844156160000),(262194426325901/11064936960000),(-16688154032293/442597478400)],[(-1348368939569/2766234240000),(27257732909369/14937664896000),(126471253763681/37344162240000)],[(-1151036357/28814940000),(-2663391147079/37344162240000),(7157587531021/74688324480000)],[(-138181/196465500),(-228969973/62240270400),(-888340553/222286680000)],[(-7003/1029105000),(-228379/3704778000),(-824389/6174630000)],[(-26/108056025),(-38/36018675),(-4/2401245)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self05Coeffs_correct : widthCoefficients 2 true 5 = self05Coeffs := by
  rw [widthCoefficients,self05Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
