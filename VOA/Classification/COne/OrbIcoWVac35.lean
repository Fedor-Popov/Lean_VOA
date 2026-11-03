import VOA.Classification.COne.OrbIcoWVac34

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac35Rows00 := jetRows 1 false 35 0
theorem vac35Rows00_correct : jetRows 1 false 35 0 = vac35Rows00 := rfl
def vac35Row01 : List Jet := [[(1/6),(-41/6)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac35Rows01 : List (List Jet) := vac35Rows00 ++ [vac35Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows01_correct : jetRows 1 false 35 1 = vac35Rows01 := by
  rw [jetRows, vac35Rows00_correct]
  change vac35Rows00 ++ [jetStep 1 false 35 1 vac35Rows00] = vac35Rows00 ++ [vac35Row01]
  congr 1
  decide +kernel
def vac35Row02 : List Jet := [[(-75/44),(27/11)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac35Rows02 : List (List Jet) := vac35Rows01 ++ [vac35Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows02_correct : jetRows 1 false 35 2 = vac35Rows02 := by
  rw [jetRows, vac35Rows01_correct]
  change vac35Rows01 ++ [jetStep 1 false 35 2 vac35Rows01] = vac35Rows01 ++ [vac35Row02]
  congr 1
  decide +kernel
def vac35Row03 : List Jet := [[(89/44),(733/66)],[(-17/1980),(34/99)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac35Rows03 : List (List Jet) := vac35Rows02 ++ [vac35Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows03_correct : jetRows 1 false 35 3 = vac35Rows03 := by
  rw [jetRows, vac35Rows02_correct]
  change vac35Rows02 ++ [jetStep 1 false 35 3 vac35Rows02] = vac35Rows02 ++ [vac35Row03]
  congr 1
  decide +kernel
def vac35Row04 : List Jet := [[(-845/1584),(-102569/4752)],[(281/2970),(-107/2970)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def vac35Rows04 : List (List Jet) := vac35Rows03 ++ [vac35Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows04_correct : jetRows 1 false 35 4 = vac35Rows04 := by
  rw [jetRows, vac35Rows03_correct]
  change vac35Rows03 ++ [jetStep 1 false 35 4 vac35Rows03] = vac35Rows03 ++ [vac35Row04]
  congr 1
  decide +kernel
def vac35Row05 : List Jet := [[(-23279/10560),(7933/495)],[(-13879/118800),(-33733/39600)],[(1/3600),(-13/1200)],[0,0],[0,0],[0,0],[0,0]]
def vac35Rows05 : List (List Jet) := vac35Rows04 ++ [vac35Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows05_correct : jetRows 1 false 35 5 = vac35Rows05 := by
  rw [jetRows, vac35Rows04_correct]
  change vac35Rows04 ++ [jetStep 1 false 35 5 vac35Rows04] = vac35Rows04 ++ [vac35Row05]
  congr 1
  decide +kernel
def vac35Row06 : List Jet := [[(98627/21120),(698173/63360)],[(221/17820),(180113/118800)],[(-1531/453600),(-1949/831600)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def vac35Rows06 : List (List Jet) := vac35Rows05 ++ [vac35Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows06_correct : jetRows 1 false 35 6 = vac35Rows06 := by
  rw [jetRows, vac35Rows05_correct]
  change vac35Rows05 ++ [jetStep 1 false 35 6 vac35Rows05] = vac35Rows05 ++ [vac35Row06]
  congr 1
  decide +kernel
def vac35Row07 : List Jet := [[(-428315/88704),(-67847753/1330560)],[(1358437/6652800),(-82793/105600)],[(9277/2095632),(2175667/52390800)],[(-281/34927200),(5339/17463600)],[0,0],[0,0],[0,0]]
def vac35Rows07 : List (List Jet) := vac35Rows06 ++ [vac35Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows07_correct : jetRows 1 false 35 7 = vac35Rows07 := by
  rw [jetRows, vac35Rows06_correct]
  change vac35Rows06 ++ [jetStep 1 false 35 7 vac35Rows06] = vac35Rows06 ++ [vac35Row07]
  congr 1
  decide +kernel
def vac35Row08 : List Jet := [[(1042429/1182720),(19567507/253440)],[(-7766221/19008000),(-10290437/4752000)],[(4369/6548850),(-1360711/19051200)],[(9809/87318000),(3523/17463600)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def vac35Rows08 : List (List Jet) := vac35Rows07 ++ [vac35Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows08_correct : jetRows 1 false 35 8 = vac35Rows08 := by
  rw [jetRows, vac35Rows07_correct]
  change vac35Rows07 ++ [jetStep 1 false 35 8 vac35Rows07] = vac35Rows07 ++ [vac35Row08]
  congr 1
  decide +kernel
def vac35Row09 : List Jet := [[(324323/43008),(-318968897/7096320)],[(104892659/299376000),(7941994451/1197504000)],[(-29021149/2155507200),(77569817/7544275200)],[(-440707/2694384000),(-7398163/3772137600)],[(667/2514758400),(-24679/2514758400)],[0,0],[0,0]]
def vac35Rows09 : List (List Jet) := vac35Rows08 ++ [vac35Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows09_correct : jetRows 1 false 35 9 = vac35Rows09 := by
  rw [jetRows, vac35Rows08_correct]
  change vac35Rows08 ++ [jetStep 1 false 35 9 vac35Rows08] = vac35Rows08 ++ [vac35Row09]
  congr 1
  decide +kernel
def vac35Row10 : List Jet := [[(-111427663/6451200),(-10517715893/106444800)],[(870698921/2661120000),(-18171913649/2177280000)],[(2199253813/80831520000),(13517285813/53887680000)],[(-2470709/22632825600),(22225303/6286896000)],[(-587197/125737920000),(-27053/1964655000)],[(-1/39916800),(-1/7983360)],[0,0]]
def vac35Rows10 : List (List Jet) := vac35Rows09 ++ [vac35Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows10_correct : jetRows 1 false 35 10 = vac35Rows10 := by
  rw [jetRows, vac35Rows09_correct]
  change vac35Rows09 ++ [jetStep 1 false 35 10 vac35Rows09] = vac35Rows09 ++ [vac35Row10]
  congr 1
  decide +kernel
def vac35Row11 : List Jet := [[(12025113/716800),(2210358853/5913600)],[(-2076069113/1064448000),(-1339456698563/263450880000)],[(-44792930927/3556586880000),(-4548771449447/6224027040000)],[(88219067/79035264000),(4504010449/1659740544000)],[(35864833/4149351360000),(94334113/691558560000)],[(-793/55324684800),(793/1536796800)],[0,0]]
def vac35Rows11 : List (List Jet) := vac35Rows10 ++ [vac35Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows11_correct : jetRows 1 false 35 11 = vac35Rows11 := by
  rw [jetRows, vac35Rows10_correct]
  change vac35Rows10 ++ [jetStep 1 false 35 11 vac35Rows10] = vac35Rows10 ++ [vac35Row11]
  congr 1
  decide +kernel
def vac35Row12 : List Jet := [[(3943833/114688),(-21297321767/40550400)],[(5727274397/1451520000),(10395546335743/143700480000)],[(-2499017689111/17071617024000),(5956093618199/10669760640000)],[(-126959607827/42679042560000),(-210384166217/4267904256000)],[(688136263/29875329792000),(-53450190379/149376648960000)],[(964549/2074675680000),(9293/4704480000)],[(1/479001600),(1/79833600)]]
def vac35Rows12 : List (List Jet) := vac35Rows11 ++ [vac35Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Rows12_correct : jetRows 1 false 35 12 = vac35Rows12 := by
  rw [jetRows, vac35Rows11_correct]
  change vac35Rows11 ++ [jetStep 1 false 35 12 vac35Rows11] = vac35Rows11 ++ [vac35Row12]
  congr 1
  decide +kernel
def vac35Coeffs : List Jet := [[(45006837/40960),(11327030555/811008)],[(-20736455483/380160000),(600971675137/627264000)],[(-1101155839519/304850304000),(-15905713762951/304850304000)],[(50264921411/1333720080000),(-2735060033831/2667440160000)],[(625130851/389001690000),(3954784223/389001690000)],[(523769/64833615000),(1051117/5402801250)],[(-2/108056025),(8/12006225)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac35Coeffs_correct : widthCoefficients 1 false 35 = vac35Coeffs := by
  rw [widthCoefficients,vac35Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
