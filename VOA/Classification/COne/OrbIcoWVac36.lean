import VOA.Classification.COne.OrbIcoWVac35

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac36Rows00 := jetRows 1 false 36 0
theorem vac36Rows00_correct : jetRows 1 false 36 0 = vac36Rows00 := rfl
def vac36Row01 : List Jet := [[0,-7],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac36Rows01 : List (List Jet) := vac36Rows00 ++ [vac36Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows01_correct : jetRows 1 false 36 1 = vac36Rows01 := by
  rw [jetRows, vac36Rows00_correct]
  change vac36Rows00 ++ [jetStep 1 false 36 1 vac36Rows00] = vac36Rows00 ++ [vac36Row01]
  congr 1
  decide +kernel
def vac36Row02 : List Jet := [[(-18/11),(83/22)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac36Rows02 : List (List Jet) := vac36Rows01 ++ [vac36Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows02_correct : jetRows 1 false 36 2 = vac36Rows02 := by
  rw [jetRows, vac36Rows01_correct]
  change vac36Rows01 ++ [jetStep 1 false 36 2 vac36Rows01] = vac36Rows01 ++ [vac36Row02]
  congr 1
  decide +kernel
def vac36Row03 : List Jet := [[(126/55),(1676/165)],[0,(119/330)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac36Rows03 : List (List Jet) := vac36Rows02 ++ [vac36Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows03_correct : jetRows 1 false 36 3 = vac36Rows03 := by
  rw [jetRows, vac36Rows02_correct]
  change vac36Rows02 ++ [jetStep 1 false 36 3 vac36Rows02] = vac36Rows02 ++ [vac36Row03]
  congr 1
  decide +kernel
def vac36Row04 : List Jet := [[(-119/110),(-1561/66)],[(1/11),(-349/2970)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def vac36Rows04 : List (List Jet) := vac36Rows03 ++ [vac36Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows04_correct : jetRows 1 false 36 4 = vac36Rows04 := by
  rw [jetRows, vac36Rows03_correct]
  change vac36Rows03 ++ [jetStep 1 false 36 4 vac36Rows03] = vac36Rows03 ++ [vac36Row04]
  congr 1
  decide +kernel
def vac36Row05 : List Jet := [[(-973/550),(18214/825)],[(-37/275),(-96197/118800)],[0,(-7/600)],[0,0],[0,0],[0,0],[0,0]]
def vac36Rows05 : List (List Jet) := vac36Rows04 ++ [vac36Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows05_correct : jetRows 1 false 36 5 = vac36Rows05 := by
  rw [jetRows, vac36Rows04_correct]
  change vac36Rows04 ++ [jetStep 1 false 36 5 vac36Rows04] = vac36Rows04 ++ [vac36Row05]
  congr 1
  decide +kernel
def vac36Row06 : List Jet := [[(3241/660),(40613/9900)],[(391/7700),(8585033/4989600)],[(-1/308),(2237/2494800)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def vac36Rows06 : List (List Jet) := vac36Rows05 ++ [vac36Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows06_correct : jetRows 1 false 36 6 = vac36Rows06 := by
  rw [jetRows, vac36Rows05_correct]
  change vac36Rows05 ++ [jetStep 1 false 36 6 vac36Rows05] = vac36Rows05 ++ [vac36Row06]
  congr 1
  decide +kernel
def vac36Row07 : List Jet := [[(-3371/550),(-78517/1540)],[(5699/32340),(-139203887/104781600)],[(281/53900),(4252597/104781600)],[0,(281/831600)],[0,0],[0,0],[0,0]]
def vac36Rows07 : List (List Jet) := vac36Rows06 ++ [vac36Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows07_correct : jetRows 1 false 36 7 = vac36Rows07 := by
  rw [jetRows, vac36Rows06_correct]
  change vac36Rows06 ++ [jetStep 1 false 36 7 vac36Rows06] = vac36Rows06 ++ [vac36Row07]
  congr 1
  decide +kernel
def vac36Row08 : List Jet := [[(65107/22000),(824749/8800)],[(-96857/215600),(-1361037221/838252800)],[(-1297/1078000),(-19718059/232848000)],[(1/9240),(1007/12474000)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def vac36Rows08 : List (List Jet) := vac36Rows07 ++ [vac36Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows08_correct : jetRows 1 false 36 8 = vac36Rows08 := by
  rw [jetRows, vac36Rows07_correct]
  change vac36Rows07 ++ [jetStep 1 false 36 8 vac36Rows07] = vac36Rows07 ++ [vac36Row08]
  congr 1
  decide +kernel
def vac36Row09 : List Jet := [[(27761/4500),(-112333621/1386000)],[(852707/1663200),(108171938053/15088550400)],[(-51143/4158000),(864992209/18860688000)],[(-193/970200),(-36999227/18860688000)],[0,(-667/59875200)],[0,0],[0,0]]
def vac36Rows09 : List (List Jet) := vac36Rows08 ++ [vac36Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows09_correct : jetRows 1 false 36 9 = vac36Rows09 := by
  rw [jetRows, vac36Rows08_correct]
  change vac36Rows08 ++ [jetStep 1 false 36 9 vac36Rows08] = vac36Rows08 ++ [vac36Row09]
  congr 1
  decide +kernel
def vac36Row10 : List Jet := [[(-135184/6875),(-127830697/1980000)],[(1897829/22680000),(-3782215399531/323326080000)],[(556939/17463600),(10096046251/45265651200)],[(-839/97020000),(420939863/94303440000)],[(-1/221760),(-72053/8981280000)],[(-1/39916800),(-1/7983360)],[0,0]]
def vac36Rows10 : List (List Jet) := vac36Rows09 ++ [vac36Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows10_correct : jetRows 1 false 36 10 = vac36Rows10 := by
  rw [jetRows, vac36Rows09_correct]
  change vac36Rows09 ++ [jetStep 1 false 36 10 vac36Rows09] = vac36Rows09 ++ [vac36Row10]
  congr 1
  decide +kernel
def vac36Row11 : List Jet := [[(3269763/121000),(4634944547/10890000)],[(-5443031219/2744280000),(43188850621163/24896108160000)],[(-272633/8712000),(-480074642837/553246848000)],[(3449521/3201660000),(-25881257/86444820000)],[(947/85377600),(289590547/2074675680000)],[0,(793/1317254400)],[0,0]]
def vac36Rows11 : List (List Jet) := vac36Rows10 ++ [vac36Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows11_correct : jetRows 1 false 36 11 = vac36Rows11 := by
  rw [jetRows, vac36Rows10_correct]
  change vac36Rows10 ++ [jetStep 1 false 36 11 vac36Rows10] = vac36Rows10 ++ [vac36Row11]
  congr 1
  decide +kernel
def vac36Row12 : List Jet := [[(11515987/660000),(-120502719277/130680000)],[(37833454399/6586272000),(3193667571643267/42679042560000)],[(-1942160347/16465680000),(15258515726933/10669760640000)],[(-91384739/23051952000),(-7291048550213/149376648960000)],[(281983/25613280000),(-360869791/711317376000)],[(1/2217600),(380077/296382240000)],[(1/479001600),(1/79833600)]]
def vac36Rows12 : List (List Jet) := vac36Rows11 ++ [vac36Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Rows12_correct : jetRows 1 false 36 12 = vac36Rows12 := by
  rw [jetRows, vac36Rows11_correct]
  change vac36Rows11 ++ [jetStep 1 false 36 12 vac36Rows11] = vac36Rows11 ++ [vac36Row12]
  congr 1
  decide +kernel
def vac36Coeffs : List Jet := [[(447535081/302500),(19104345827/1815000)],[(-10773881111/470448000),(1007868590795489/609700608000)],[(-1407400013/294030000),(-116216080578559/2667440160000)],[(7125373/1200622500),(-9252344268613/6224027040000)],[(169231/100051875),(1975820717/389001690000)],[(16/1334025),(13095217/64833615000)],[0,(4/5145525)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac36Coeffs_correct : widthCoefficients 1 false 36 = vac36Coeffs := by
  rw [widthCoefficients,vac36Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
