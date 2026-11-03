import VOA.Classification.COne.OrbIcoWVac22

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac23Rows00 := jetRows 2 false 23 0
theorem vac23Rows00_correct : jetRows 2 false 23 0 = vac23Rows00 := rfl
def vac23Row01 : List Jet := [[(13/6),(-29/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac23Rows01 : List (List Jet) := vac23Rows00 ++ [vac23Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows01_correct : jetRows 2 false 23 1 = vac23Rows01 := by
  rw [jetRows, vac23Rows00_correct]
  change vac23Rows00 ++ [jetStep 2 false 23 1 vac23Rows00] = vac23Rows00 ++ [vac23Row01]
  congr 1
  decide +kernel
def vac23Row02 : List Jet := [[(-7/44),(-95/11),(551/44)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac23Rows02 : List (List Jet) := vac23Rows01 ++ [vac23Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows02_correct : jetRows 2 false 23 2 = vac23Rows02 := by
  rw [jetRows, vac23Rows01_correct]
  change vac23Rows01 ++ [jetStep 2 false 23 2 vac23Rows01] = vac23Rows01 ++ [vac23Row02]
  congr 1
  decide +kernel
def vac23Row03 : List Jet := [[(-63/44),(1519/330),(777/44)],[(-221/1980),(68/495),(493/1980)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac23Rows03 : List (List Jet) := vac23Rows02 ++ [vac23Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows03_correct : jetRows 2 false 23 3 = vac23Rows03 := by
  rw [jetRows, vac23Rows02_correct]
  change vac23Rows02 ++ [jetStep 2 false 23 3 vac23Rows02] = vac23Rows02 ++ [vac23Row03]
  congr 1
  decide +kernel
def vac23Row04 : List Jet := [[(721/528),(134047/23760),(-98269/4752)],[(-1/990),(1549/2970),(-326/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac23Rows04 : List (List Jet) := vac23Rows03 ++ [vac23Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows04_correct : jetRows 2 false 23 4 = vac23Rows04 := by
  rw [jetRows, vac23Rows03_correct]
  change vac23Rows03 ++ [jetStep 2 false 23 4 vac23Rows03] = vac23Rows03 ++ [vac23Row04]
  congr 1
  decide +kernel
def vac23Row05 : List Jet := [[(-7/64),(-81347/7920),(-124759/15840)],[(3941/39600),(-1477/10800),(-60851/39600)],[(13/3600),(-1/1200),(-1/80)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac23Rows05 : List (List Jet) := vac23Rows04 ++ [vac23Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows05_correct : jetRows 2 false 23 5 = vac23Rows05 := by
  rw [jetRows, vac23Rows04_correct]
  change vac23Rows04 ++ [jetStep 2 false 23 5 vac23Rows04] = vac23Rows04 ++ [vac23Row05]
  congr 1
  decide +kernel
def vac23Row06 : List Jet := [[(-1743/1408),(62329/12672),(8068043/221760)],[(-6073/75600),(-70067/113400),(2144309/2494800)],[(89/184800),(-4453/226800),(-1259/103950)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac23Rows06 : List (List Jet) := vac23Rows05 ++ [vac23Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows06_correct : jetRows 2 false 23 6 = vac23Rows06 := by
  rw [jetRows, vac23Rows05_correct]
  change vac23Rows05 ++ [jetStep 2 false 23 6 vac23Rows05] = vac23Rows05 ++ [vac23Row06]
  congr 1
  decide +kernel
def vac23Row07 : List Jet := [[(2323/1408),(1748371/266112),(-72651701/2328480)],[(-339173/9313920),(11993173/15523200),(50913727/23284800)],[(-1879/415800),(-1789/748440),(555227/7484400)],[(-3653/34927200),(-281/3492720),(281/727650)],[0,0,0],[0,0,0],[0,0,0]]
def vac23Rows07 : List (List Jet) := vac23Rows06 ++ [vac23Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows07_correct : jetRows 2 false 23 7 = vac23Rows07 := by
  rw [jetRows, vac23Rows06_correct]
  change vac23Rows06 ++ [jetStep 2 false 23 7 vac23Rows06] = vac23Rows06 ++ [vac23Row07]
  congr 1
  decide +kernel
def vac23Row08 : List Jet := [[(-7659/11264),(-1740161/118272),(-60552503/3763200)],[(136845967/931392000),(26598457/232848000),(-1229455019/310464000)],[(44393/16632000),(5949269/149688000),(47231/4276800)],[(-1049/29106000),(58087/87318000),(101677/87318000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac23Rows08 : List (List Jet) := vac23Rows07 ++ [vac23Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows08_correct : jetRows 2 false 23 8 = vac23Rows08 := by
  rw [jetRows, vac23Rows07_correct]
  change vac23Rows07 ++ [jetStep 2 false 23 8 vac23Rows07] = vac23Rows07 ++ [vac23Row08]
  congr 1
  decide +kernel
def vac23Row09 : List Jet := [[(-26887/22528),(1920001/202752),(33078277/460800)],[(-512912227/4191264000),(-1760485271/1197504000),(40668193/279417600)],[(960013/186278400),(-1147705631/37721376000),(-16734315089/75442752000)],[(59483/299376000),(1444459/2694384000),(-126727/42099750)],[(8671/2514758400),(15341/2514758400),(-12673/1257379200)],[0,0,0],[0,0,0]]
def vac23Rows09 : List (List Jet) := vac23Rows08 ++ [vac23Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows09_correct : jetRows 2 false 23 9 = vac23Rows09 := by
  rw [jetRows, vac23Rows08_correct]
  change vac23Rows08 ++ [jetStep 2 false 23 9 vac23Rows08] = vac23Rows08 ++ [vac23Row09]
  congr 1
  decide +kernel
def vac23Row10 : List Jet := [[(29785/12288),(7217465/608256),(-33205783/554400)],[(-17178085109/167650560000),(87670214633/55883520000),(1548275866883/167650560000)],[(-159037/14553000),(-76097594669/1131641280000),(37577435323/188606880000)],[(-1941497/62868960000),(-693621053/282910320000),(-318189463/62868960000)],[(4271/1552320000),(-83753/3143448000),(-10632037/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac23Rows10 : List (List Jet) := vac23Rows09 ++ [vac23Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows10_correct : jetRows 2 false 23 10 = vac23Rows10 := by
  rw [jetRows, vac23Rows09_correct]
  change vac23Rows09 ++ [jetStep 2 false 23 10 vac23Rows09] = vac23Rows09 ++ [vac23Row10]
  congr 1
  decide +kernel
def vac23Row11 : List Jet := [[(-315721/495616),(-8872763/278784),(-7789283801/78059520)],[(1398252652579/3688312320000),(3475940173043/1844156160000),(-1515376964461/131725440000)],[(-338422501/184415616000),(1072337885903/6224027040000),(512761485937/778003380000)],[(-12657737/20490624000),(-3852903907/8298702720000),(5329763387/251475840000)],[(-794021/65862720000),(-21015971/296382240000),(25590211/197588160000)],[(-10309/55324684800),(-793/1536796800),(793/3688312320)],[0,0,0]]
def vac23Rows11 : List (List Jet) := vac23Rows10 ++ [vac23Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows11_correct : jetRows 2 false 23 11 = vac23Rows11 := by
  rw [jetRows, vac23Rows10_correct]
  change vac23Rows10 ++ [jetStep 2 false 23 11 vac23Rows10] = vac23Rows10 ++ [vac23Row11]
  congr 1
  decide +kernel
def vac23Row12 : List Jet := [[(-11276601/1982464),(-101627219/5947392),(272649638729/936714240)],[(383834971/9032601600),(-55131901003/6842880000),(-5233662710557/143700480000)],[(99254626379/2011806720000),(3043486530089/14937664896000),(-598161786023009/298753297920000)],[(311485441/526901760000),(2674147550413/149376648960000),(4614146024503/149376648960000)],[(-351552409/16597405440000),(37162692913/149376648960000),(42656864507/29875329792000)],[(-119663/230519520000),(5459/2449440000),(211219/16465680000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac23Rows12 : List (List Jet) := vac23Rows11 ++ [vac23Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Rows12_correct : jetRows 2 false 23 12 = vac23Rows12 := by
  rw [jetRows, vac23Rows11_correct]
  change vac23Rows11 ++ [jetStep 2 false 23 12 vac23Rows11] = vac23Rows11 ++ [vac23Row12]
  congr 1
  decide +kernel
def vac23Coeffs : List Jet := [[(65675925/991232),(-2328888989/2973696),(-500356818647/66908160)],[(20703880383521/1844156160000),(46577146998101/307359360000),(-49697961457819/115259760000)],[(-1348368939569/2766234240000),(653192091637553/74688324480000),(2104628145740443/37344162240000)],[(-1151036357/28814940000),(-3742278487/29875329792),(41126679287681/18672081120000)],[(-138181/196465500),(-3848270777/389001690000),(112818493/6174630000)],[(-7003/1029105000),(-117679/661567500),(197423/3087315000)],[(-26/108056025),(-8/12006225),(2/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac23Coeffs_correct : widthCoefficients 2 false 23 = vac23Coeffs := by
  rw [widthCoefficients,vac23Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
