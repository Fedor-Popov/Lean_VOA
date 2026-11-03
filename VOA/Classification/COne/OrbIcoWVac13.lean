import VOA.Classification.COne.OrbIcoWVac12

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac13Rows00 := jetRows 3 false 13 0
theorem vac13Rows00_correct : jetRows 3 false 13 0 = vac13Rows00 := rfl
def vac13Row01 : List Jet := [[(23/6),(-19/6),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac13Rows01 : List (List Jet) := vac13Rows00 ++ [vac13Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows01_correct : jetRows 3 false 13 1 = vac13Rows01 := by
  rw [jetRows, vac13Rows00_correct]
  change vac13Rows00 ++ [jetStep 3 false 13 1 vac13Rows00] = vac13Rows00 ++ [vac13Row01]
  congr 1
  decide +kernel
def vac13Row02 : List Jet := [[(589/132),(-370/33),(703/132),0],[(-1/22),(-1/22),0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac13Rows02 : List (List Jet) := vac13Rows01 ++ [vac13Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows02_correct : jetRows 3 false 13 2 = vac13Rows02 := by
  rw [jetRows, vac13Rows01_correct]
  change vac13Rows01 ++ [jetStep 3 false 13 2 vac13Rows01] = vac13Rows01 ++ [vac13Row02]
  congr 1
  decide +kernel
def vac13Row03 : List Jet := [[(185/396),(-5299/495),(6905/396),(-703/110)],[(-391/1980),(-17/495),(323/1980),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac13Rows03 : List (List Jet) := vac13Rows02 ++ [vac13Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows03_correct : jetRows 3 false 13 3 = vac13Rows03 := by
  rw [jetRows, vac13Rows02_correct]
  change vac13Rows02 ++ [jetStep 3 false 13 3 vac13Rows02] = vac13Rows02 ++ [vac13Row03]
  congr 1
  decide +kernel
def vac13Row04 : List Jet := [[(-19705/14256),(52577/23760),(20503/1584),(-1385531/71280)],[(-2479/8910),(1169/2970),(529/1485),(-1406/4455)],[(1/792),(1/396),(1/792),0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac13Rows04 : List (List Jet) := vac13Rows03 ++ [vac13Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows04_correct : jetRows 3 false 13 4 = vac13Rows04 := by
  rw [jetRows, vac13Rows03_correct]
  change vac13Rows03 ++ [jetStep 3 false 13 4 vac13Rows03] = vac13Rows03 ++ [vac13Row04]
  congr 1
  decide +kernel
def vac13Row05 : List Jet := [[(32029/57024),(594301/142560),(-82205/9504),(-364847/35640)],[(-4151/59400),(10037/13200),(-16381/39600),(-95053/118800)],[(23/3600),(3/400),(-1/240),(-19/3600)],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac13Rows05 : List (List Jet) := vac13Rows04 ++ [vac13Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows05_correct : jetRows 3 false 13 5 = vac13Rows05 := by
  rw [jetRows, vac13Rows04_correct]
  change vac13Rows04 ++ [jetStep 3 false 13 5 vac13Rows04] = vac13Rows04 ++ [vac13Row05]
  congr 1
  decide +kernel
def vac13Row06 : List Jet := [[(805199/2395008),(-42599771/11975040),(-5546939/997920),(92309531/5987520)],[(245893/2138400),(212293/2138400),(-241339/178200),(194053/534600)],[(15389/1360800),(-26869/7484400),(-36103/1247400),(-14071/7484400)],[(-1/33264),(-1/11088),(-1/11088),(-1/33264)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac13Rows06 : List (List Jet) := vac13Rows05 ++ [vac13Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows06_correct : jetRows 3 false 13 6 = vac13Rows06 := by
  rw [jetRows, vac13Rows05_correct]
  change vac13Rows05 ++ [jetStep 3 false 13 6 vac13Rows05] = vac13Rows05 ++ [vac13Row06]
  congr 1
  decide +kernel
def vac13Row07 : List Jet := [[(-29698409/50295168),(-97637849/251475840),(59185001/6286896),(520885873/125737920)],[(-245671/35925120),(-93843601/179625600),(-103603/5613300),(188463533/89812800)],[(577337/104781600),(-689993/20956320),(-8653/396900),(1472693/26195400)],[(-6463/34927200),(-281/698544),(-281/2910600),(4777/17463600)],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
def vac13Rows07 : List (List Jet) := vac13Rows06 ++ [vac13Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows07_correct : jetRows 3 false 13 7 = vac13Rows07 := by
  rw [jetRows, vac13Rows06_correct]
  change vac13Rows06 ++ [jetStep 3 false 13 7 vac13Rows06] = vac13Rows06 ++ [vac13Row07]
  congr 1
  decide +kernel
def vac13Row08 : List Jet := [[(96202405/402361344),(956376947/335301120),(-3586536209/3353011200),(-17014278889/1005903360)],[(-91949041/1197504000),(5484079/49896000),(79707271/57024000),(-6055309/37422000)],[(-244963/42768000),(-334301/13608000),(4046347/59875200),(724651/9355500)],[(-114871/261954000),(-89759/261954000),(303251/261954000),(299597/261954000)],[(1/1330560),(1/332640),(1/221760),(1/332640)],[0,0,0,0],[0,0,0,0]]
def vac13Rows08 : List (List Jet) := vac13Rows07 ++ [vac13Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows08_correct : jetRows 3 false 13 8 = vac13Rows08 := by
  rw [jetRows, vac13Rows07_correct]
  change vac13Rows07 ++ [jetStep 3 false 13 8 vac13Rows07] = vac13Rows07 ++ [vac13Row08]
  congr 1
  decide +kernel
def vac13Row09 : List Jet := [[(156291785/658409472),(-19066530947/12070840320),(-475125269833/60354201600),(26746579679/7242504192)],[(10631113627/226328256000),(8571537283/18860688000),(-6020394991/15088550400),(-174059115313/56582064000)],[(-7102369/1810626048),(1191402319/37721376000),(6494790611/75442752000),(-56620661/452656512)],[(-3863183/9430344000),(22552603/18860688000),(56169419/18860688000),(-2467033/1886068800)],[(15341/2514758400),(48691/2514758400),(20677/1257379200),(-667/114307200)],[0,0,0,0],[0,0,0,0]]
def vac13Rows09 : List (List Jet) := vac13Rows08 ++ [vac13Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows09_correct : jetRows 3 false 13 9 = vac13Rows09 := by
  rw [jetRows, vac13Rows08_correct]
  change vac13Rows08 ++ [jetStep 3 false 13 9 vac13Rows08] = vac13Rows08 ++ [vac13Row09]
  congr 1
  decide +kernel
def vac13Row10 : List Jet := [[(-1224049385/3950456832),(-35140822793/21727512576),(40652482511/9053130240),(127491621799/6789847680)],[(704340427501/13579695360000),(-355753877851/1234517760000),(-735637527029/411505920000),(8768289491459/13579695360000)],[(44568739/6466521600),(2537814341/70727580000),(-12951936793/125737920000),(-160783677449/565820640000)],[(13740311/80831520000),(13021609/4490640000),(-3343993/2993760000),(-19837591/1837080000)],[(8344043/377213760000),(262379/6286896000),(-4174487/125737920000),(-317503/2946982500)],[(-1/39916800),(-1/7983360),(-1/3991680),(-1/3991680)],[0,0,0,0]]
def vac13Rows10 : List (List Jet) := vac13Rows09 ++ [vac13Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows10_correct : jetRows 3 false 13 10 = vac13Rows10 := by
  rw [jetRows, vac13Rows09_correct]
  change vac13Rows09 ++ [jetStep 3 false 13 10 vac13Rows09] = vac13Rows09 ++ [vac13Row10]
  congr 1
  decide +kernel
def vac13Row11 : List Jet := [[(-71724445/564350976),(3682176617/2217093120),(1094591897623/121940121600),(-457596406423/121940121600)],[(-546791577967/9053130240000),(-10183256048753/16597405440000),(14090531549531/24896108160000),(81913933900039/12448054080000)],[(7959455719/1244805408000),(-156078097051/3112013520000),(-111441381881/444573360000),(42394472051/194500845000)],[(265412327/331948108800),(3750706573/8298702720000),(-18298477487/1185528960000),(-73863924083/8298702720000)],[(28392781/592764480000),(-19072939/691558560000),(-466514593/1383117120000),(-203961127/1037337840000)],[(-18239/55324684800),(-793/576298800),(-793/409812480),(-793/1383117120)],[0,0,0,0]]
def vac13Rows11 : List (List Jet) := vac13Rows10 ++ [vac13Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows11_correct : jetRows 3 false 13 11 = vac13Rows11 := by
  rw [jetRows, vac13Rows10_correct]
  change vac13Rows10 ++ [jetStep 3 false 13 11 vac13Rows10] = vac13Rows10 ++ [vac13Row11]
  congr 1
  decide +kernel
def vac13Row12 : List Jet := [[(5713569355/47405481984),(10431850650983/2607301509120),(23351065660931/4481299468800),(-269674555417/5601624336)],[(-4259804027/30233088000),(-4291321049273/40739086080000),(622103713757227/112032486720000),(502562119422263/64018563840000)],[(-16128409331891/1792519787520000),(-113677511173/640185638400),(19802266010063/896259893760000),(1736157789368197/896259893760000)],[(79317527659/99584432640000),(-1769861948887/149376648960000),(-4948264480717/149376648960000),(1343310608573/16597405440000)],[(1652335087/21339521280000),(-12607938851/21339521280000),(-69557083/67744512000),(35621535533/21339521280000)],[(-18444131/6224027040000),(-7940123/889146720000),(-207077/74095560000),(1445657/88914672000)],[(1/479001600),(1/79833600),(1/31933440),(1/23950080)]]
def vac13Rows12 : List (List Jet) := vac13Rows11 ++ [vac13Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Rows12_correct : jetRows 3 false 13 12 = vac13Rows12 := by
  rw [jetRows, vac13Rows11_correct]
  change vac13Rows11 ++ [jetStep 3 false 13 12 vac13Rows11] = vac13Rows11 ++ [vac13Row12]
  congr 1
  decide +kernel
def vac13Coeffs : List Jet := [[(-100143105725/23702740992),(-33812524227833/260730150912),(44991069512701/448129946880),(8320299548454101/4481299468800)],[(11110570757107/2909934720000),(-722460436730311/64018563840000),(-5596458612760993/32009281920000),(255192480203327/1600464096000)],[(9764443353919/24896108160000),(293444657193773/74688324480000),(-618786298501067/37344162240000),(-556060276038457/12448054080000)],[(-49867817/111143340000),(241078372609/533488032000),(-5914377925639/18672081120000),(-8992778530469/2074675680000)],[(-397822627/466802028000),(32867799749/1167005070000),(-470197193/14407470000),(-121044726317/1167005070000)],[(2686289/16208403750),(1945871/21611205000),(-1946053/2701400625),(-41617319/64833615000)],[(-46/108056025),(-64/36018675),(-2/800415),(-16/21611205)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac13Coeffs_correct : widthCoefficients 3 false 13 = vac13Coeffs := by
  rw [widthCoefficients,vac13Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
