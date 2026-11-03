import VOA.Classification.COne.OrbIcoWVac37

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac38Rows00 := jetRows 1 false 38 0
theorem vac38Rows00_correct : jetRows 1 false 38 0 = vac38Rows00 := rfl
def vac38Row01 : List Jet := [[(-1/3),(-22/3)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac38Rows01 : List (List Jet) := vac38Rows00 ++ [vac38Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows01_correct : jetRows 1 false 38 1 = vac38Rows01 := by
  rw [jetRows, vac38Rows00_correct]
  change vac38Rows00 ++ [jetStep 1 false 38 1 vac38Rows00] = vac38Rows00 ++ [vac38Row01]
  congr 1
  decide +kernel
def vac38Row02 : List Jet := [[(-31/22),(145/22)],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac38Rows02 : List (List Jet) := vac38Rows01 ++ [vac38Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows02_correct : jetRows 1 false 38 2 = vac38Rows02 := by
  rw [jetRows, vac38Rows01_correct]
  change vac38Rows01 ++ [jetStep 1 false 38 2 vac38Rows01] = vac38Rows01 ++ [vac38Row02]
  congr 1
  decide +kernel
def vac38Row03 : List Jet := [[(30/11),(73/10)],[(17/990),(391/990)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac38Rows03 : List (List Jet) := vac38Rows02 ++ [vac38Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows03_correct : jetRows 1 false 38 3 = vac38Rows03 := by
  rw [jetRows, vac38Rows02_correct]
  change vac38Rows02 ++ [jetStep 1 false 38 3 vac38Rows02] = vac38Rows02 ++ [vac38Row03]
  congr 1
  decide +kernel
def vac38Row04 : List Jet := [[(-25/11),(-105583/3960)],[(116/1485),(-881/2970)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def vac38Rows04 : List (List Jet) := vac38Rows03 ++ [vac38Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows04_correct : jetRows 1 false 38 4 = vac38Rows04 := by
  rw [jetRows, vac38Rows03_correct]
  change vac38Rows03 ++ [jetStep 1 false 38 4 vac38Rows03] = vac38Rows03 ++ [vac38Row04]
  congr 1
  decide +kernel
def vac38Row05 : List Jet := [[(-21/44),(30933/880)],[(-19427/118800),(-77617/118800)],[(-1/1800),(-1/75)],[0,0],[0,0],[0,0],[0,0]]
def vac38Rows05 : List (List Jet) := vac38Rows04 ++ [vac38Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows05_correct : jetRows 1 false 38 5 = vac38Rows05 := by
  rw [jetRows, vac38Rows04_correct]
  change vac38Rows04 ++ [jetStep 1 false 38 5 vac38Rows04] = vac38Rows04 ++ [vac38Row05]
  congr 1
  decide +kernel
def vac38Row06 : List Jet := [[(2953/616),(-51229/3360)],[(676267/4989600),(5121521/2494800)],[(-631/226800),(20477/2494800)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def vac38Rows06 : List (List Jet) := vac38Rows05 ++ [vac38Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows06_correct : jetRows 1 false 38 6 = vac38Rows06 := by
  rw [jetRows, vac38Rows05_correct]
  change vac38Rows05 ++ [jetStep 1 false 38 6 vac38Rows05] = vac38Rows05 ++ [vac38Row06]
  congr 1
  decide +kernel
def vac38Row07 : List Jet := [[(-13756/1617),(-8050109/194040)],[(11887/142560),(-1418099/554400)],[(681787/104781600),(122537/3492720)],[(281/17463600),(281/698544)],[0,0],[0,0],[0,0]]
def vac38Rows07 : List (List Jet) := vac38Rows06 ++ [vac38Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows07_correct : jetRows 1 false 38 7 = vac38Rows07 := by
  rw [jetRows, vac38Rows06_correct]
  change vac38Rows06 ++ [jetStep 1 false 38 7 vac38Rows06] = vac38Rows06 ++ [vac38Row07]
  congr 1
  decide +kernel
def vac38Row08 : List Jet := [[(6365/784),(31330547/258720)],[(-95097061/199584000),(23595041/199584000)],[(-11373737/2095632000),(-225562679/2095632000)],[(2017/21829500),(-5801/29106000)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def vac38Rows08 : List (List Jet) := vac38Rows07 ++ [vac38Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows08_correct : jetRows 1 false 38 8 = vac38Rows08 := by
  rw [jetRows, vac38Rows07_correct]
  change vac38Rows07 ++ [jetStep 1 false 38 8 vac38Rows07] = vac38Rows07 ++ [vac38Row08]
  congr 1
  decide +kernel
def vac38Row09 : List Jet := [[(5035/8624),(-4699627/27720)],[(21055116553/25147584000),(2715996809/381024000)],[(-405311/53887680),(175718623/1347192000)],[(-693563/2694384000),(-3050227/1714608000)],[(-667/1257379200),(-8671/628689600)],[0,0],[0,0]]
def vac38Rows09 : List (List Jet) := vac38Rows08 ++ [vac38Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows09_correct : jetRows 1 false 38 9 = vac38Rows09 := by
  rw [jetRows, vac38Rows08_correct]
  change vac38Rows08 ++ [jetStep 1 false 38 9 vac38Rows08] = vac38Rows08 ++ [vac38Row09]
  congr 1
  decide +kernel
def vac38Row10 : List Jet := [[(-1075685/51744),(30940067/465696)],[(-154322811131/251475840000),(-1539515287903/83825280000)],[(1690935781/45265651200),(1818853679/17681895000)],[(63937651/282910320000),(1738522817/282910320000)],[(-240697/62868960000),(70783/12573792000)],[(-1/39916800),(-1/7983360)],[0,0]]
def vac38Rows10 : List (List Jet) := vac38Rows09 ++ [vac38Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows10_correct : jetRows 1 false 38 10 = vac38Rows10 := by
  rw [jetRows, vac38Rows09_correct]
  change vac38Rows09 ++ [jetStep 1 false 38 10 vac38Rows09] = vac38Rows09 ++ [vac38Row10]
  congr 1
  decide +kernel
def vac38Row11 : List Jet := [[(2335955/47432),(3628682861/8537760)],[(-3988357639117/2766234240000),(60788586460787/2766234240000)],[(-362195352119/4979221632000),(-8481789061411/8298702720000)],[(9214987/11855289600),(-18510253/2315486250)],[(4495303/296382240000),(272484983/2074675680000)],[(793/27662342400),(793/1024531200)],[0,0]]
def vac38Rows11 : List (List Jet) := vac38Rows10 ++ [vac38Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows11_correct : jetRows 1 false 38 11 = vac38Rows11 := by
  rw [jetRows, vac38Rows10_correct]
  change vac38Rows10 ++ [jetStep 1 false 38 11 vac38Rows10] = vac38Rows10 ++ [vac38Row11]
  congr 1
  decide +kernel
def vac38Row12 : List Jet := [[(-324615/6776),(-142020059/77440)],[(58522432123381/6638962176000),(25315312621117/502951680000)],[(45085652341/74688324480000),(288940300223/82987027200)],[(-811925261549/149376648960000),(-576701857793/16597405440000)],[(-1405143433/74688324480000),(-446406413/565820640000)],[(49103/129667230000),(-17513/42340320000)],[(1/479001600),(1/79833600)]]
def vac38Rows12 : List (List Jet) := vac38Rows11 ++ [vac38Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Rows12_correct : jetRows 1 false 38 12 = vac38Rows12 := by
  rw [jetRows, vac38Rows11_correct]
  change vac38Rows11 ++ [jetStep 1 false 38 12 vac38Rows11] = vac38Rows11 ++ [vac38Row12]
  congr 1
  decide +kernel
def vac38Coeffs : List Jet := [[(82776825/47432),(-5439467611/569184)],[(500741936104313/5532468480000),(2728526915851493/922078080000)],[(-19760416470769/3394923840000),(18152868778811/4149351360000)],[(-377292455989/4668020280000),(-2759192361719/1244805408000)],[(109231/77182875),(-527607331/55571670000)],[(172033/9261945000),(873217/4630972500)],[(4/108056025),(4/4002075)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac38Coeffs_correct : widthCoefficients 1 false 38 = vac38Coeffs := by
  rw [widthCoefficients,vac38Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
