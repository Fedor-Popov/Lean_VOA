import VOA.Classification.COne.OrbIcoWVac31

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac32Rows00 := jetRows 2 false 32 0
theorem vac32Rows00_correct : jetRows 2 false 32 0 = vac32Rows00 := rfl
def vac32Row01 : List Jet := [[(2/3),(-19/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac32Rows01 : List (List Jet) := vac32Rows00 ++ [vac32Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows01_correct : jetRows 2 false 32 1 = vac32Rows01 := by
  rw [jetRows, vac32Rows00_correct]
  change vac32Rows00 ++ [jetStep 2 false 32 1 vac32Rows00] = vac32Rows00 ++ [vac32Row01]
  congr 1
  decide +kernel
def vac32Row02 : List Jet := [[(-19/11),(-25/22),(475/22)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac32Rows02 : List (List Jet) := vac32Rows01 ++ [vac32Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows02_correct : jetRows 2 false 32 2 = vac32Rows02 := by
  rw [jetRows, vac32Rows01_correct]
  change vac32Rows01 ++ [jetStep 2 false 32 2 vac32Rows01] = vac32Rows01 ++ [vac32Row02]
  congr 1
  decide +kernel
def vac32Row03 : List Jet := [[(12/11),(2021/165),(-71/10)],[(-17/495),(289/990),(323/990)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac32Rows03 : List (List Jet) := vac32Rows02 ++ [vac32Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows03_correct : jetRows 2 false 32 3 = vac32Rows03 := by
  rw [jetRows, vac32Rows02_correct]
  change vac32Rows02 ++ [jetStep 2 false 32 3 vac32Rows02] = vac32Rows02 ++ [vac32Row03]
  congr 1
  decide +kernel
def vac32Row04 : List Jet := [[(9/11),(-83789/5940),(-496759/11880)],[(47/495),(523/2970),(-3559/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac32Rows04 : List (List Jet) := vac32Rows03 ++ [vac32Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows04_correct : jetRows 2 false 32 4 = vac32Rows04 := by
  rw [jetRows, vac32Rows03_correct]
  change vac32Rows03 ++ [jetStep 2 false 32 4 vac32Rows03] = vac32Rows03 ++ [vac32Row04]
  congr 1
  decide +kernel
def vac32Row05 : List Jet := [[(-30/11),(1007/990),(382927/4950)],[(-221/3960),(-9223/10800),(-17027/39600)],[(1/900),(-1/120),(-1/50)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac32Rows05 : List (List Jet) := vac32Rows04 ++ [vac32Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows05_correct : jetRows 2 false 32 5 = vac32Rows05 := by
  rw [jetRows, vac32Rows04_correct]
  change vac32Rows04 ++ [jetStep 2 false 32 5 vac32Rows04] = vac32Rows04 ++ [vac32Row05]
  congr 1
  decide +kernel
def vac32Row06 : List Jet := [[(35/11),(302887/13860),(-748852/17325)],[(-13103/166320),(4169507/4989600),(5331127/1247400)],[(-1391/415800),(-5191/498960),(32051/831600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac32Rows06 : List (List Jet) := vac32Rows05 ++ [vac32Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows06_correct : jetRows 2 false 32 6 = vac32Rows06 := by
  rw [jetRows, vac32Rows05_correct]
  change vac32Rows05 ++ [jetStep 2 false 32 6 vac32Rows05] = vac32Rows05 ++ [vac32Row06]
  congr 1
  decide +kernel
def vac32Row07 : List Jet := [[(-40/33),(-405719/10395),(-17046811/207900)],[(257791/1164240),(1820309/3880800),(-4407433/727650)],[(6101/3492720),(4014679/104781600),(793043/13097700)],[(-281/8731800),(3653/17463600),(4777/5821200)],[0,0,0],[0,0,0],[0,0,0]]
def vac32Rows07 : List (List Jet) := vac32Rows06 ++ [vac32Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows07_correct : jetRows 2 false 32 7 = vac32Rows07 := by
  rw [jetRows, vac32Rows06_correct]
  change vac32Rows06 ++ [jetStep 2 false 32 7 vac32Rows06] = vac32Rows06 ++ [vac32Row07]
  congr 1
  decide +kernel
def vac32Row08 : List Jet := [[-3,(271303/9240),(14966437/61600)],[(-2111227/9313920),(-49970981/18627840),(-77359921/155232000)],[(155123/31752000),(-62757923/2095632000),(-557944213/2095632000)],[(59/539000),(42673/87318000),(-87029/87318000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac32Rows08 : List (List Jet) := vac32Rows07 ++ [vac32Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows08_correct : jetRows 2 false 32 8 = vac32Rows08 := by
  rw [jetRows, vac32Rows07_correct]
  change vac32Rows07 ++ [jetStep 2 false 32 8 vac32Rows07] = vac32Rows07 ++ [vac32Row08]
  congr 1
  decide +kernel
def vac32Row09 : List Jet := [[(82/11),(110381/4620),(-76395887/277200)],[(-1234967/23950080),(186171397/47900160),(1590220223/85536000)],[(-39930301/3143448000),(-1201783153/18860688000),(1078192673/3772137600)],[(-28099/628689600),(-31363127/18860688000),(-86055727/18860688000)],[(667/628689600),(-667/114307200),(-667/19646550)],[0,0,0],[0,0,0]]
def vac32Rows09 : List (List Jet) := vac32Rows08 ++ [vac32Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows09_correct : jetRows 2 false 32 9 = vac32Rows09 := by
  rw [jetRows, vac32Rows08_correct]
  change vac32Rows08 ++ [jetStep 2 false 32 9 vac32Rows08] = vac32Rows08 ++ [vac32Row09]
  congr 1
  decide +kernel
def vac32Row10 : List Jet := [[(-23/3),(-3131641/27720),(-157503881/1663200)],[(19544393/30481920),(-901460519/3353011200),(-23475176317/620928000)],[(1882285687/188606880000),(37866514459/161663040000),(50054872247/94303440000)],[(-2996263/9430344000),(4061563/5143824000),(175540483/10478160000)],[(-46447/10478160000),(-1678399/62868960000),(1442149/62868960000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac32Rows10 : List (List Jet) := vac32Rows09 ++ [vac32Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows10_correct : jetRows 2 false 32 10 = vac32Rows10 := by
  rw [jetRows, vac32Rows09_correct]
  change vac32Rows09 ++ [jetStep 2 false 32 10 vac32Rows09] = vac32Rows09 ++ [vac32Row10]
  congr 1
  decide +kernel
def vac32Row11 : List Jet := [[-4,(365623/2310),(435449347/381150)],[(-388875803/335301120),(-44791562377/3353011200),(344182220681/36883123200)],[(2208898787/84680640000),(-7475461519/29393280000),(-10356547264027/3556586880000)],[(109519/125737920),(66347807/8298702720),(-196322261/21611205000)],[(40079/69155856000),(216097627/2074675680000),(301200173/691558560000)],[(-793/13831171200),(793/3073593600),(793/368831232)],[0,0,0]]
def vac32Rows11 : List (List Jet) := vac32Rows10 ++ [vac32Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows11_correct : jetRows 2 false 32 11 = vac32Rows11 := by
  rw [jetRows, vac32Rows10_correct]
  change vac32Rows10 ++ [jetStep 2 false 32 11 vac32Rows10] = vac32Rows10 ++ [vac32Row11]
  congr 1
  decide +kernel
def vac32Row12 : List Jet := [[39,(561021/3080),(-194285071/84700)],[(-1672259069/4023613440),(1487606975479/40236134400),(55118737239143/221298739200)],[(-329209640269/2489610816000),(-77031060078377/74688324480000),(346700353765897/74688324480000)],[(131250353/2263282560000),(-990019155577/29875329792000),(-26836209002807/149376648960000)],[(7096489/161663040000),(4120187867/74688324480000),(-81002761247/37344162240000)],[(144623/345779280000),(92527/26943840000),(1/2661120)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac32Rows12 : List (List Jet) := vac32Rows11 ++ [vac32Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Rows12_correct : jetRows 2 false 32 12 = vac32Rows12 := by
  rw [jetRows, vac32Rows11_correct]
  change vac32Rows11 ++ [jetStep 2 false 32 12 vac32Rows11] = vac32Rows11 ++ [vac32Row12]
  congr 1
  decide +kernel
def vac32Coeffs : List Jet := [[0,(100776/11),(199957012/4235)],[(-755018485/12192768),(-560330425187/1341204480),(167956736609731/36883123200)],[(209757289999/1556006760000),(-683564144438977/18672081120000),(-1458841920588841/7468832448000)],[(4643733443/63510480000),(532706954249/2667440160000),(-14988809732863/2667440160000)],[(48292243/64833615000),(6268436929/389001690000),(138159907/8104201875)],[(-821/196465500),(8402347/64833615000),(8053789/10805602500)],[(-8/108056025),(4/12006225),(4/1440747)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac32Coeffs_correct : widthCoefficients 2 false 32 = vac32Coeffs := by
  rw [widthCoefficients,vac32Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
