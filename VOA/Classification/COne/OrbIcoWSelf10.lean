import VOA.Classification.COne.OrbIcoWSelf09

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self10Rows00 := jetRows 2 true 10 0
theorem self10Rows00_correct : jetRows 2 true 10 0 = self10Rows00 := rfl
def self10Row01 : List Jet := [[(4/3),(-13/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self10Rows01 : List (List Jet) := self10Rows00 ++ [self10Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows01_correct : jetRows 2 true 10 1 = self10Rows01 := by
  rw [jetRows, self10Rows00_correct]
  change self10Rows00 ++ [jetStep 2 true 10 1 self10Rows00] = self10Rows00 ++ [self10Row01]
  congr 1
  decide +kernel
def self10Row02 : List Jet := [[(-4/3),(-229/132),(325/132)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self10Rows02 : List (List Jet) := self10Rows01 ++ [self10Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows02_correct : jetRows 2 true 10 2 = self10Rows02 := by
  rw [jetRows, self10Rows01_correct]
  change self10Rows01 ++ [jetStep 2 true 10 2 self10Rows01] = self10Rows01 ++ [self10Row02]
  congr 1
  decide +kernel
def self10Row03 : List Jet := [[(-2/9),(785/198),(62/99)],[(-34/495),(17/396),(221/1980)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self10Rows03 : List (List Jet) := self10Rows02 ++ [self10Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows03_correct : jetRows 2 true 10 3 = self10Rows03 := by
  rw [jetRows, self10Rows02_correct]
  change self10Rows02 ++ [jetStep 2 true 10 3 self10Rows02] = self10Rows02 ++ [self10Row03]
  congr 1
  decide +kernel
def self10Row04 : List Jet := [[(281/162),(-1409/792),(-1519/297)],[(313/4455),(53/297),(-56/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self10Rows04 : List (List Jet) := self10Rows03 ++ [self10Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows04_correct : jetRows 2 true 10 4 = self10Rows04 := by
  rw [jetRows, self10Rows03_correct]
  change self10Rows03 ++ [jetStep 2 true 10 4 self10Rows03] = self10Rows03 ++ [self10Row04]
  congr 1
  decide +kernel
def self10Row05 : List Jet := [[(-323/162),(-28559/8910),(247411/47520)],[(31/1100),(-52829/237600),(-6143/19800)],[(1/450),(1/1200),(-1/200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self10Rows05 : List (List Jet) := self10Rows04 ++ [self10Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows05_correct : jetRows 2 true 10 5 = self10Rows05 := by
  rw [jetRows, self10Rows04_correct]
  change self10Rows04 ++ [jetStep 2 true 10 5 self10Rows04] = self10Rows04 ++ [self10Row05]
  congr 1
  decide +kernel
def self10Row06 : List Jet := [[(635/972),(376433/53460),(370297/285120)],[(-69623/534600),(-240151/4276800),(523987/1108800)],[(-1093/467775),(-135791/14968800),(-27493/4989600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self10Rows06 : List (List Jet) := self10Rows05 ++ [self10Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows06_correct : jetRows 2 true 10 6 = self10Rows06 := by
  rw [jetRows, self10Rows05_correct]
  change self10Rows05 ++ [jetStep 2 true 10 6 self10Rows05] = self10Rows05 ++ [self10Row06]
  congr 1
  decide +kernel
def self10Row07 : List Jet := [[(16805/10206),(-6507013/1122660),(-14040919/1283040)],[(26611/204120),(1234103/2566080),(-5239471/628689600)],[(-15989/8731800),(1426609/209563200),(4775641/209563200)],[(-281/4365900),(-281/3175200),(281/2328480)],[0,0,0],[0,0,0],[0,0,0]]
def self10Rows07 : List (List Jet) := self10Rows06 ++ [self10Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows07_correct : jetRows 2 true 10 7 = self10Rows07 := by
  rw [jetRows, self10Rows06_correct]
  change self10Rows06 ++ [jetStep 2 true 10 7 self10Rows06] = self10Rows06 ++ [self10Row07]
  congr 1
  decide +kernel
def self10Row08 : List Jet := [[(-279697/81648),(-61379/30240),(363064271/23950080)],[(55841/2376000),(-106696553/171072000),(-1243433197/1197504000)],[(3442477/523908000),(17882107/1397088000),(-86759/5457375)],[(9187/130977000),(6238/16372125),(13523/26195400)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self10Rows08 : List (List Jet) := self10Rows07 ++ [self10Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows08_correct : jetRows 2 true 10 8 = self10Rows08 := by
  rw [jetRows, self10Rows07_correct]
  change self10Rows07 ++ [jetStep 2 true 10 8 self10Rows07] = self10Rows07 ++ [self10Row08]
  congr 1
  decide +kernel
def self10Row09 : List Jet := [[(258401/91854),(32162819/2449440),(-3677983/979776)],[(-2189976221/8083152000),(176574919/21555072000),(29812739249/16765056000)],[(-2068987/404157600),(-1390881743/37721376000),(-3270915751/75442752000)],[(24071/224532000),(-4087043/37721376000),(-22578869/18860688000)],[(667/314344800),(12673/2514758400),(-667/628689600)],[0,0,0],[0,0,0]]
def self10Rows09 : List (List Jet) := self10Rows08 ++ [self10Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows09_correct : jetRows 2 true 10 9 = self10Rows09 := by
  rw [jetRows, self10Rows08_correct]
  change self10Rows08 ++ [jetStep 2 true 10 9 self10Rows08] = self10Rows08 ++ [self10Row09]
  congr 1
  decide +kernel
def self10Row10 : List Jet := [[(1686971/1102248),(-761745007/44089920),(-21843649711/808315200)],[(92840619401/242494560000),(2855382329551/1939956480000),(-7058208221/20207880000)],[(-70293197/8083152000),(7868411213/323326080000),(1585256251/11975040000)],[(-4055851/11787930000),(-716697781/565820640000),(-25927193/62868960000)],[(-57487/23575860000),(-2308577/125737920000),(-4943843/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self10Rows10 : List (List Jet) := self10Rows09 ++ [self10Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows10_correct : jetRows 2 true 10 10 = self10Rows10 := by
  rw [jetRows, self10Rows09_correct]
  change self10Rows09 ++ [jetStep 2 true 10 10 self10Rows09] = self10Rows09 ++ [self10Row10]
  congr 1
  decide +kernel
def self10Row11 : List Jet := [[(-9231599/1102248),(-938608339/242494560),(2975976150247/53348803200)],[(2307765083/26943840000),(-22590498523/8622028800),(-12939240973289/2371057920000)],[(3255583/104544000),(4658455909967/49792216320000),(-1910050967621/24896108160000)],[(1909339/22228668000),(712347527/259334460000),(188397194369/24896108160000)],[(-64643/7203735000),(-1781519/165974054400),(96405647/1383117120000)],[(-793/6915585600),(-793/2049062400),(-793/3688312320)],[0,0,0]]
def self10Rows11 : List (List Jet) := self10Rows10 ++ [self10Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows11_correct : jetRows 2 true 10 11 = self10Rows11 := by
  rw [jetRows, self10Rows10_correct]
  change self10Rows10 ++ [jetStep 2 true 10 11 self10Rows10] = self10Rows10 ++ [self10Row11]
  congr 1
  decide +kernel
def self10Row12 : List Jet := [[(89458343/13226976),(210293183803/2909934720),(19390162786241/640185638400)],[(-94522266437/52907904000),(-11163789287881/4655895552000),(420528588564263/32009281920000)],[(-90571487329/8002320480000),(-22590478722181/64018563840000),(-174870650803801/224064973440000)],[(11654735747/5334880320000),(169876208797/42679042560000),(-31442868991/2032335360000)],[(6497893/194500845000),(2899000997/13579695360000),(25611180473/74688324480000)],[(464657/3112013520000),(844619/444573360000),(89801/14819112000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self10Rows12 : List (List Jet) := self10Rows11 ++ [self10Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Rows12_correct : jetRows 2 true 10 12 = self10Rows12 := by
  rw [jetRows, self10Rows11_correct]
  change self10Rows11 ++ [jetStep 2 true 10 12 self10Rows11] = self10Rows11 ++ [self10Row12]
  congr 1
  decide +kernel
def self10Coeffs : List Jet := [[(-67714075/236196),(-24343241/236196),(25396754267/9447840)],[(73663982233/18895680000),(-234463683611371/1662819840000),(-966584525167/6046617600)],[(159128115203/95265720000),(579914925901/213395212800),(-242054282899259/16597405440000)],[(140096029/8660520000),(1346438645863/5334880320000),(1307094107591/3556586880000)],[(-4612079/6483361500),(56833033/42436548000),(60289447277/4668020280000)],[(-83927/5402801250),(-216143/5186689200),(2379317/43222410000)],[(-16/108056025),(-2/4002075),(-2/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self10Coeffs_correct : widthCoefficients 2 true 10 = self10Coeffs := by
  rw [widthCoefficients,self10Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
