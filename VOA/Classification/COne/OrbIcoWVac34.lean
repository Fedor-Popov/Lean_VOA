import VOA.Classification.COne.OrbIcoWVac33

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac34Rows00 := jetRows 1 false 34 0
theorem vac34Rows00_correct : jetRows 1 false 34 0 = vac34Rows00 := rfl
def vac34Row01 : List Jet := [[(1/3),(-20/3)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac34Rows01 : List (List Jet) := vac34Rows00 ++ [vac34Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows01_correct : jetRows 1 false 34 1 = vac34Rows01 := by
  rw [jetRows, vac34Rows00_correct]
  change vac34Rows00 ++ [jetStep 1 false 34 1 vac34Rows00] = vac34Rows00 ++ [vac34Row01]
  congr 1
  decide +kernel
def vac34Row02 : List Jet := [[(-115/66),(79/66)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac34Rows02 : List (List Jet) := vac34Rows01 ++ [vac34Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows02_correct : jetRows 1 false 34 2 = vac34Rows02 := by
  rw [jetRows, vac34Rows01_correct]
  change vac34Rows01 ++ [jetStep 1 false 34 2 vac34Rows01] = vac34Rows01 ++ [vac34Row02]
  congr 1
  decide +kernel
def vac34Row03 : List Jet := [[(856/495),(11641/990)],[(-17/990),(323/990)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac34Rows03 : List (List Jet) := vac34Rows02 ++ [vac34Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows03_correct : jetRows 1 false 34 3 = vac34Rows03 := by
  rw [jetRows, vac34Rows02_correct]
  change vac34Rows02 ++ [jetStep 1 false 34 3 vac34Rows02] = vac34Rows02 ++ [vac34Row03]
  congr 1
  decide +kernel
def vac34Row04 : List Jet := [[(-259/8910),(-228739/11880)],[(86/891),(119/2970)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def vac34Rows04 : List (List Jet) := vac34Rows03 ++ [vac34Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows04_correct : jetRows 1 false 34 4 = vac34Rows04 := by
  rw [jetRows, vac34Rows03_correct]
  change vac34Rows03 ++ [jetStep 1 false 34 4 vac34Rows03] = vac34Rows03 ++ [vac34Row04]
  congr 1
  decide +kernel
def vac34Row05 : List Jet := [[(-5071/2025),(3723817/356400)],[(-2317/23760),(-9419/10800)],[(1/1800),(-1/100)],[0,0],[0,0],[0,0],[0,0]]
def vac34Rows05 : List (List Jet) := vac34Rows04 ++ [vac34Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows05_correct : jetRows 1 false 34 5 = vac34Rows05 := by
  rw [jetRows, vac34Rows04_correct]
  change vac34Rows04 ++ [jetStep 1 false 34 5 vac34Rows04] = vac34Rows04 ++ [vac34Row05]
  congr 1
  decide +kernel
def vac34Row06 : List Jet := [[(4001891/935550),(242450273/14968800)],[(-869/38880),(62987/48600)],[(-5141/1496880),(-3611/680400)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def vac34Rows06 : List (List Jet) := vac34Rows05 ++ [vac34Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows06_correct : jetRows 1 false 34 6 = vac34Rows06 := by
  rw [jetRows, vac34Rows05_correct]
  change vac34Rows05 ++ [jetStep 1 false 34 6 vac34Rows05] = vac34Rows05 ++ [vac34Row06]
  congr 1
  decide +kernel
def vac34Row07 : List Jet := [[(-1391722/392931),(-3821490847/78586200)],[(9901183/44906400),(-13434073/44906400)],[(374449/104781600),(12049/291060)],[(-281/17463600),(4777/17463600)],[0,0],[0,0],[0,0]]
def vac34Rows07 : List (List Jet) := vac34Rows06 ++ [vac34Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows07_correct : jetRows 1 false 34 7 = vac34Rows07 := by
  rw [jetRows, vac34Rows06_correct]
  change vac34Rows06 ++ [jetStep 1 false 34 7 vac34Rows06] = vac34Rows06 ++ [vac34Row07]
  congr 1
  decide +kernel
def vac34Row08 : List Jet := [[(-79364381/98232750),(10548579121/174636000)],[(-212735497/598752000),(-500641051/199584000)],[(231961/99792000),(-2463767/42768000)],[(373/3274425),(81223/261954000)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def vac34Rows08 : List (List Jet) := vac34Rows07 ++ [vac34Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows08_correct : jetRows 1 false 34 8 = vac34Rows08 := by
  rw [jetRows, vac34Rows07_correct]
  change vac34Rows07 ++ [jetStep 1 false 34 8 vac34Rows07] = vac34Rows07 ++ [vac34Row08]
  congr 1
  decide +kernel
def vac34Row09 : List Jet := [[(3588515176/442047375),(-1813590467/117879300)],[(8988185783/45265651200),(55163974541/9430344000)],[(-196211291/14145516000),(-4720739/235758600)],[(-473107/3772137600),(-35975069/18860688000)],[(667/1257379200),(-667/78586200)],[0,0],[0,0]]
def vac34Rows09 : List (List Jet) := vac34Rows08 ++ [vac34Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows09_correct : jetRows 1 false 34 9 = vac34Rows09 := by
  rw [jetRows, vac34Rows08_correct]
  change vac34Rows08 ++ [jetStep 1 false 34 9 vac34Rows08] = vac34Rows08 ++ [vac34Row09]
  congr 1
  decide +kernel
def vac34Row10 : List Jet := [[(-8584793348/602791875),(-6155305132469/53045685000)],[(676782064489/1357969536000),(-35609652085639/6789847680000)],[(234405943/10777536000),(147185186441/565820640000)],[(-7892821/40415760000),(104833807/40415760000)],[(-177697/37721376000),(-1181809/62868960000)],[(-1/39916800),(-1/7983360)],[0,0]]
def vac34Rows10 : List (List Jet) := vac34Rows09 ++ [vac34Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows10_correct : jetRows 1 false 34 10 = vac34Rows10 := by
  rw [jetRows, vac34Rows09_correct]
  change vac34Rows09 ++ [jetStep 1 false 34 10 vac34Rows09] = vac34Rows09 ++ [vac34Row10]
  congr 1
  decide +kernel
def vac34Row11 : List Jet := [[(83433535952/10419688125),(6360478065059/20839376250)],[(-8825630010191/4979221632000),(-242204744891353/24896108160000)],[(705595427/199168865280),(-2860631617157/4979221632000)],[(6777378119/6224027040000),(15890676467/3112013520000)],[(51011/8468064000),(267811679/2074675680000)],[(-793/27662342400),(793/1844156160)],[0,0]]
def vac34Rows11 : List (List Jet) := vac34Rows10 ++ [vac34Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows11_correct : jetRows 1 false 34 11 = vac34Rows11 := by
  rw [jetRows, vac34Rows10_correct]
  change vac34Rows10 ++ [jetStep 1 false 34 11 vac34Rows10] = vac34Rows10 ++ [vac34Row11]
  congr 1
  decide +kernel
def vac34Row12 : List Jet := [[(1853925597368/43762690125),(-179301964809859/875253802500)],[(286468105155011/128037127680000),(1295104280482541/20369543040000)],[(-636579102289/4073908608000),(-1221839906159/8002320480000)],[(-287760921131/149376648960000),(-1384137035629/29875329792000)],[(348529327/10669760640000),(-53557987/254041920000)],[(144437/311201352000),(207329/80831520000)],[(1/479001600),(1/79833600)]]
def vac34Rows12 : List (List Jet) := vac34Rows11 ++ [vac34Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Rows12_correct : jetRows 1 false 34 12 = vac34Rows12 := by
  rw [jetRows, vac34Rows11_correct]
  change vac34Rows11 ++ [jetStep 1 false 34 12 vac34Rows11] = vac34Rows11 ++ [vac34Row12]
  congr 1
  decide +kernel
def vac34Coeffs : List Jet := [[(149497506859376/218813450625),(6208743362129321/437626901250)],[(-4465071145955699/64018563840000),(1418664336445151/4001160240000)],[(-17071919961983/7468832448000),(-392166430859429/7468832448000)],[(15886574731/266744016000),(-1511133312833/2667440160000)],[(74410657/53045685000),(197053789/14407470000)],[(51449/12966723000),(1452568/8104201875)],[(-4/108056025),(4/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac34Coeffs_correct : widthCoefficients 1 false 34 = vac34Coeffs := by
  rw [widthCoefficients,vac34Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
