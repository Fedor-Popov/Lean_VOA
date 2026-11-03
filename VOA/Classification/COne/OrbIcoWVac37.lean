import VOA.Classification.COne.OrbIcoWVac36

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac37Rows00 := jetRows 1 false 37 0
theorem vac37Rows00_correct : jetRows 1 false 37 0 = vac37Rows00 := rfl
def vac37Row01 : List Jet := [[(-1/6),(-43/6)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac37Rows01 : List (List Jet) := vac37Rows00 ++ [vac37Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows01_correct : jetRows 1 false 37 1 = vac37Rows01 := by
  rw [jetRows, vac37Rows00_correct]
  change vac37Rows00 ++ [jetStep 1 false 37 1 vac37Rows00] = vac37Rows00 ++ [vac37Row01]
  congr 1
  decide +kernel
def vac37Row02 : List Jet := [[(-203/132),(170/33)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac37Rows02 : List (List Jet) := vac37Rows01 ++ [vac37Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows02_correct : jetRows 1 false 37 2 = vac37Rows02 := by
  rw [jetRows, vac37Rows01_correct]
  change vac37Rows01 ++ [jetStep 1 false 37 2 vac37Rows01] = vac37Rows01 ++ [vac37Row02]
  congr 1
  decide +kernel
def vac37Row03 : List Jet := [[(91/36),(4403/495)],[(17/1980),(17/45)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac37Rows03 : List (List Jet) := vac37Rows02 ++ [vac37Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows03_correct : jetRows 1 false 37 3 = vac37Rows03 := by
  rw [jetRows, vac37Rows02_correct]
  change vac37Rows02 ++ [jetStep 1 false 37 3 vac37Rows02] = vac37Rows02 ++ [vac37Row03]
  congr 1
  decide +kernel
def vac37Row04 : List Jet := [[(-23737/14256),(-200957/7920)],[(761/8910),(-607/2970)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def vac37Rows04 : List (List Jet) := vac37Rows03 ++ [vac37Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows04_correct : jetRows 1 false 37 4 = vac37Rows04 := by
  rw [jetRows, vac37Rows03_correct]
  change vac37Rows03 ++ [jetStep 1 false 37 4 vac37Rows03] = vac37Rows03 ++ [vac37Row04]
  congr 1
  decide +kernel
def vac37Row05 : List Jet := [[(-68075/57024),(4062457/142560)],[(-119/792),(-88403/118800)],[(-1/3600),(-1/80)],[0,0],[0,0],[0,0],[0,0]]
def vac37Rows05 : List (List Jet) := vac37Rows04 ++ [vac37Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows05_correct : jetRows 1 false 37 5 = vac37Rows05 := by
  rw [jetRows, vac37Rows04_correct]
  change vac37Rows04 ++ [jetStep 1 false 37 5 vac37Rows04] = vac37Rows04 ++ [vac37Row05]
  congr 1
  decide +kernel
def vac37Row06 : List Jet := [[(1698305/342144),(-7936589/1710720)],[(275699/2993760),(28472791/14968800)],[(-45641/14968800),(6607/1496880)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def vac37Rows06 : List (List Jet) := vac37Rows05 ++ [vac37Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows06_correct : jetRows 1 false 37 6 = vac37Rows06 := by
  rw [jetRows, vac37Rows05_correct]
  change vac37Rows05 ++ [jetStep 1 false 37 6 vac37Rows05] = vac37Rows05 ++ [vac37Row06]
  congr 1
  decide +kernel
def vac37Row07 : List Jet := [[(-7574825/1026432),(-1724969231/35925120)],[(34210199/251475840),(-2418848119/1257379200)],[(281/47520),(575857/14968800)],[(281/34927200),(6463/17463600)],[0,0],[0,0],[0,0]]
def vac37Rows07 : List (List Jet) := vac37Rows06 ++ [vac37Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows07_correct : jetRows 1 false 37 7 = vac37Rows07 := by
  rw [jetRows, vac37Rows06_correct]
  change vac37Rows06 ++ [jetStep 1 false 37 7 vac37Rows06] = vac37Rows06 ++ [vac37Row07]
  congr 1
  decide +kernel
def vac37Row08 : List Jet := [[(44277493/8211456),(5211819661/47900160)],[(-52891117/111767040),(-2420501/2794176)],[(-972761/299376000),(-14507767/149688000)],[(2419/23814000),(-1261/23814000)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def vac37Rows08 : List (List Jet) := vac37Rows07 ++ [vac37Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows08_correct : jetRows 1 false 37 8 = vac37Rows08 := by
  rw [jetRows, vac37Rows07_correct]
  change vac37Rows07 ++ [jetStep 1 false 37 8 vac37Rows07] = vac37Rows07 ++ [vac37Row08]
  congr 1
  decide +kernel
def vac37Row09 : List Jet := [[(573581659/147806208),(-6060543007/49268736)],[(6138150607/9053130240),(7218083/979776)],[(-2337761357/226328256000),(3250593799/37721376000)],[(-4141/17962560),(-5127131/2694384000)],[(-667/2514758400),(-31349/2514758400)],[0,0],[0,0]]
def vac37Rows09 : List (List Jet) := vac37Rows08 ++ [vac37Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows09_correct : jetRows 1 false 37 9 = vac37Rows09 := by
  rw [jetRows, vac37Rows08_correct]
  change vac37Rows08 ++ [jetStep 1 false 37 9 vac37Rows08] = vac37Rows08 ++ [vac37Row09]
  congr 1
  decide +kernel
def vac37Row10 : List Jet := [[(-18614489803/886837248),(-22748289541/2217093120)],[(-25171307863/108637562880),(-8211166121729/543187814400)],[(40068164057/1131641280000),(16441242229/94303440000)],[(3922727/37721376000),(302484283/56582064000)],[(-1595197/377213760000),(-4447/2857680000)],[(-1/39916800),(-1/7983360)],[0,0]]
def vac37Rows10 : List (List Jet) := vac37Rows09 ++ [vac37Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows10_correct : jetRows 1 false 37 10 = vac37Rows10 := by
  rw [jetRows, vac37Rows09_correct]
  change vac37Rows09 ++ [jetStep 1 false 37 10 vac37Rows09] = vac37Rows09 ++ [vac37Row10]
  congr 1
  decide +kernel
def vac37Row11 : List Jet := [[(372128311373/9755209728),(10917943973671/24388024320)],[(-485251996619/265558487040),(21493025924261/1991688652800)],[(-419094766/8104201875),(-1006480121147/1037337840000)],[(4809658793/4979221632000),(-19379331893/4979221632000)],[(21011/1580705280),(40922521/296382240000)],[(793/55324684800),(793/1152597600)],[0,0]]
def vac37Rows11 : List (List Jet) := vac37Rows10 ++ [vac37Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows11_correct : jetRows 1 false 37 11 = vac37Rows11 := by
  rw [jetRows, vac37Rows10_correct]
  change vac37Rows10 ++ [jetStep 1 false 37 11 vac37Rows10] = vac37Rows10 ++ [vac37Row11]
  congr 1
  decide +kernel
def vac37Row12 : List Jet := [[(-1148446403741/117062516736),(-803111591725979/585312583680)],[(7626573332419/1024297021440),(25010268970979/365820364800)],[(-24782372828359/358503957504000),(271617124698737/112032486720000)],[(-205424763857/42679042560000),(-29321127623/663896217600)],[(-153348133/49792216320000),(-97587091501/149376648960000)],[(2627749/6224027040000),(432181/889146720000)],[(1/479001600),(1/79833600)]]
def vac37Rows12 : List (List Jet) := vac37Rows11 ++ [vac37Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Rows12_correct : jetRows 1 false 37 12 = vac37Rows12 := by
  rw [jetRows, vac37Rows11_correct]
  change vac37Rows11 ++ [jetStep 1 false 37 12 vac37Rows11] = vac37Rows11 ++ [vac37Row12]
  congr 1
  decide +kernel
def vac37Coeffs : List Jet := [[(101366598717475/58531258368),(169795988139869/58531258368)],[(9316333445465/358503957504),(1691121339813443/717007915008)],[(-418087828222483/74688324480000),(-623399199253801/24896108160000)],[(-160421199157/4668020280000),(-3946518162233/2074675680000)],[(1270708231/778003380000),(-1778881163/1167005070000)],[(16/1029105),(1855831/9261945000)],[(2/108056025),(32/36018675)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac37Coeffs_correct : widthCoefficients 1 false 37 = vac37Coeffs := by
  rw [widthCoefficients,vac37Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
