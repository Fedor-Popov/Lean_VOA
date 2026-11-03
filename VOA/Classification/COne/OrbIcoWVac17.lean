import VOA.Classification.COne.OrbIcoWVac16

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac17Rows00 := jetRows 3 false 17 0
theorem vac17Rows00_correct : jetRows 3 false 17 0 = vac17Rows00 := rfl
def vac17Row01 : List Jet := [[(19/6),(-23/6),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac17Rows01 : List (List Jet) := vac17Rows00 ++ [vac17Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows01_correct : jetRows 3 false 17 1 = vac17Rows01 := by
  rw [jetRows, vac17Rows00_correct]
  change vac17Rows00 ++ [jetStep 3 false 17 1 vac17Rows00] = vac17Rows00 ++ [vac17Row01]
  congr 1
  decide +kernel
def vac17Row02 : List Jet := [[(9/4),(-120/11),(345/44),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac17Rows02 : List (List Jet) := vac17Rows01 ++ [vac17Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows02_correct : jetRows 3 false 17 2 = vac17Rows02 := by
  rw [jetRows, vac17Rows01_correct]
  change vac17Rows01 ++ [jetStep 3 false 17 2 vac17Rows01] = vac17Rows01 ++ [vac17Row02]
  congr 1
  decide +kernel
def vac17Row03 : List Jet := [[(-5/4),(-794/165),(13159/660),(-23/2)],[(-323/1980),(17/495),(391/1980),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac17Rows03 : List (List Jet) := vac17Rows02 ++ [vac17Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows03_correct : jetRows 3 false 17 3 = vac17Rows03 := by
  rw [jetRows, vac17Rows02_correct]
  change vac17Rows02 ++ [jetStep 3 false 17 3 vac17Rows02] = vac17Rows02 ++ [vac17Row03]
  congr 1
  decide +kernel
def vac17Row04 : List Jet := [[(-67/144),(168989/23760),(66997/23760),(-56207/2160)],[(-433/2970),(1513/2970),(283/1485),(-46/99)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac17Rows04 : List (List Jet) := vac17Rows03 ++ [vac17Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows04_correct : jetRows 3 false 17 4 = vac17Rows04 := by
  rw [jetRows, vac17Rows03_correct]
  change vac17Rows03 ++ [jetStep 3 false 17 4 vac17Rows03] = vac17Rows03 ++ [vac17Row04]
  congr 1
  decide +kernel
def vac17Row05 : List Jet := [[(217/192),(-10801/15840),(-1393343/79200),(9541/1800)],[(197/2970),(19399/39600),(-39937/39600),(-75253/118800)],[(19/3600),(1/240),(-3/400),(-23/3600)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac17Rows05 : List (List Jet) := vac17Rows04 ++ [vac17Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows05_correct : jetRows 3 false 17 5 = vac17Rows05 := by
  rw [jetRows, vac17Rows04_correct]
  change vac17Rows04 ++ [jetStep 3 false 17 5 vac17Rows04] = vac17Rows04 ++ [vac17Row05]
  congr 1
  decide +kernel
def vac17Row06 : List Jet := [[(-1783/2688),(-2299217/443520),(6697379/831600),(115615/4032)],[(66379/997920),(-735871/1663200),(-54827/51975),(110161/62370)],[(30673/4989600),(-739/55440),(-3769/138600),(25427/2494800)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac17Rows06 : List (List Jet) := vac17Rows05 ++ [vac17Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows06_correct : jetRows 3 false 17 6 = vac17Rows06 := by
  rw [jetRows, vac17Rows05_correct]
  change vac17Rows05 ++ [jetStep 3 false 17 6 vac17Rows05] = vac17Rows05 ++ [vac17Row06]
  congr 1
  decide +kernel
def vac17Row07 : List Jet := [[(-14467/56448),(48086077/9313920),(203593151/17463600),(-155477717/6350400)],[(-11707/120960),(-606737/2217600),(836147/554400),(36145/19008)],[(-38609/20956320),(-2990431/104781600),(54389/2910600),(1019617/13097700)],[(-5339/34927200),(-4777/17463600),(281/2910600),(281/698544)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac17Rows07 : List (List Jet) := vac17Rows06 ++ [vac17Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows07_correct : jetRows 3 false 17 7 = vac17Rows07 := by
  rw [jetRows, vac17Rows06_correct]
  change vac17Rows06 ++ [jetStep 3 false 17 7 vac17Rows06] = vac17Rows06 ++ [vac17Row07]
  congr 1
  decide +kernel
def vac17Row08 : List Jet := [[(122485/150528),(210407/1128960),(-638074139/33868800),(-528195163/28224000)],[(58771/5322240),(1189/1760),(89920087/133056000),(-4584247/1188000)],[(-10884997/2095632000),(12553811/1047816000),(198988127/2095632000),(-48989/2976750)],[(-21577/87318000),(18563/87318000),(14209/9702000),(11299/17463600)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac17Rows08 : List (List Jet) := vac17Rows07 ++ [vac17Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows08_correct : jetRows 3 false 17 8 = vac17Rows08 := by
  rw [jetRows, vac17Rows07_correct]
  change vac17Rows07 ++ [jetStep 3 false 17 8 vac17Rows07] = vac17Rows07 ++ [vac17Row08]
  congr 1
  decide +kernel
def vac17Row09 : List Jet := [[(-160633/301056),(-3569177/645120),(49154923/22579200),(50109413717/1016064000)],[(32064367/335301120),(-25421717/167650560),(-69049903343/25147584000),(-19488112067/12573792000)],[(48787423/10777536000),(217503397/5388768000),(-87909343/2155507200),(-757795217/2694384000)],[(433/134719200),(28448743/18860688000),(17393633/18860688000),(-3772507/857304000)],[(12673/2514758400),(35351/2514758400),(667/114307200),(-20677/1257379200)],[0,0,0,0],[0,0,0,0]]
def vac17Rows09 : List (List Jet) := vac17Rows08 ++ [vac17Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows09_correct : jetRows 3 false 17 9 = vac17Rows09 := by
  rw [jetRows, vac17Rows08_correct]
  change vac17Rows08 ++ [jetStep 3 false 17 9 vac17Rows08] = vac17Rows08 ++ [vac17Row09]
  congr 1
  decide +kernel
def vac17Row10 : List Jet := [[(-666655/1806336),(11418457/2709504),(100125209/4233600),(-1894704253/381024000)],[(-38345609/447068160),(-5944841321/6706022400),(6555731773/11176704000),(4625696256697/502951680000)],[(6085684967/1131641280000),(-7207199257/188606880000),(-81165518477/377213760000),(353187379/4041576000)],[(43484153/113164128000),(10058401/18860688000),(-1263387011/188606880000),(-1116312163/141455160000)],[(1626341/125737920000),(180853/31434480000),(-9470227/125737920000),(-786763/7858620000)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac17Rows10 : List (List Jet) := vac17Rows09 ++ [vac17Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows10_correct : jetRows 3 false 17 10 = vac17Rows10 := by
  rw [jetRows, vac17Rows09_correct]
  change vac17Rows09 ++ [jetStep 3 false 17 10 vac17Rows09] = vac17Rows09 ++ [vac17Row10]
  congr 1
  decide +kernel
def vac17Row11 : List Jet := [[(162095/200704),(17697671/3311616),(-3594933253/248371200),(-354292955029/3725568000)],[(-90174631/894136320),(436946687/609638400),(1076787943823/184415616000),(1122124073579/1383117120000)],[(-134806715191/12448054080000),(-8308194173/97250422500),(43631427071/259334460000),(48588218839/44457336000)],[(39209/1254528000),(-1085266121/237105792000),(-1136540983/131725440000),(1524727399/56453760000)],[(1179461/118552896000),(-24736337/230519520000),(-320345749/1383117120000),(206885753/1037337840000)],[(-15067/55324684800),(-793/768398400),(-793/737662464),(793/1383117120)],[0,0,0,0]]
def vac17Rows11 : List (List Jet) := vac17Rows10 ++ [vac17Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows11_correct : jetRows 3 false 17 11 = vac17Rows11 := by
  rw [jetRows, vac17Rows10_correct]
  change vac17Rows10 ++ [jetStep 3 false 17 11 vac17Rows10] = vac17Rows10 ++ [vac17Row11]
  congr 1
  decide +kernel
def vac17Row12 : List Jet := [[(102085/114688),(-8965777/1622016),(-14397430721/212889600),(-4353099973/88704000)],[(41361223/243855360),(28201570097/10059033600),(17534626621/40981248000),(-692152818205813/16597405440000)],[(-2446475359189/119501319168000),(4333248968659/37344162240000),(2417879552119/2032335360000),(9537136848479/59750659584000)],[(-460343629619/298753297920000),(-216762273443/29875329792000),(671016843907/16597405440000),(1641607358087/13579695360000)],[(-6344990059/149376648960000),(-57922821961/149376648960000),(228920119/411505920000),(426483337351/149376648960000)],[(-3751997/2074675680000),(-45533/14113440000),(8861/1234926000),(621611/29638224000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac17Rows12 : List (List Jet) := vac17Rows11 ++ [vac17Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Rows12_correct : jetRows 3 false 17 12 = vac17Rows12 := by
  rw [jetRows, vac17Rows11_correct]
  change vac17Rows11 ++ [jetStep 3 false 17 12 vac17Rows11] = vac17Rows11 ++ [vac17Row12]
  congr 1
  decide +kernel
def vac17Coeffs : List Jet := [[(-6372025/401408),(944253797/3612672),(198758745181/149022720),(-56392863743/15523200)],[(-1274405/225792),(-19225146541/447068160),(1079256227347/4098124800),(42513199767523/46103904000)],[(9921823900357/74688324480000),(-471746881394423/74688324480000),(-32418854997811/2489610816000),(65454621140563/678984768000)],[(30332951491/848730960000),(-21120733247/154314720000),(-1159005549613/691558560000),(564257081837/339492384000)],[(193021403/111143340000),(44665097/55571670000),(-119615011/2058210000),(590818703/55571670000)],[(59849/926194500),(-168451/1029105000),(-944563/1543657500),(1550113/9261945000)],[(-38/108056025),(-16/12006225),(-2/1440747),(16/21611205)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac17Coeffs_correct : widthCoefficients 3 false 17 = vac17Coeffs := by
  rw [widthCoefficients,vac17Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
