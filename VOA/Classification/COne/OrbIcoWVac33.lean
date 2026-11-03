import VOA.Classification.COne.OrbIcoWVac32

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac33Rows00 := jetRows 1 false 33 0
theorem vac33Rows00_correct : jetRows 1 false 33 0 = vac33Rows00 := rfl
def vac33Row01 : List Jet := [[(1/2),(-13/2)],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac33Rows01 : List (List Jet) := vac33Rows00 ++ [vac33Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows01_correct : jetRows 1 false 33 1 = vac33Rows01 := by
  rw [jetRows, vac33Rows00_correct]
  change vac33Rows00 ++ [jetStep 1 false 33 1 vac33Rows00] = vac33Rows00 ++ [vac33Row01]
  congr 1
  decide +kernel
def vac33Row02 : List Jet := [[(-7/4),0],[(-1/22),(-1/22)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac33Rows02 : List (List Jet) := vac33Rows01 ++ [vac33Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows02_correct : jetRows 1 false 33 2 = vac33Rows02 := by
  rw [jetRows, vac33Rows01_correct]
  change vac33Rows01 ++ [jetStep 1 false 33 2 vac33Rows01] = vac33Rows01 ++ [vac33Row02]
  congr 1
  decide +kernel
def vac33Row03 : List Jet := [[(17/12),(182/15)],[(-17/660),(17/55)],[0,0],[0,0],[0,0],[0,0],[0,0]]
def vac33Rows03 : List (List Jet) := vac33Rows02 ++ [vac33Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows03_correct : jetRows 1 false 33 3 = vac33Rows03 := by
  rw [jetRows, vac33Rows02_correct]
  change vac33Rows02 ++ [jetStep 1 false 33 3 vac33Rows02] = vac33Rows02 ++ [vac33Row03]
  congr 1
  decide +kernel
def vac33Row04 : List Jet := [[(61/144),(-1339/80)],[(287/2970),(329/2970)],[(1/792),(1/396)],[0,0],[0,0],[0,0],[0,0]]
def vac33Rows04 : List (List Jet) := vac33Rows03 ++ [vac33Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows04_correct : jetRows 1 false 33 4 = vac33Rows04 := by
  rw [jetRows, vac33Rows03_correct]
  change vac33Rows03 ++ [jetStep 1 false 33 4 vac33Rows03] = vac33Rows03 ++ [vac33Row04]
  congr 1
  decide +kernel
def vac33Row05 : List Jet := [[(-1541/576),(7813/1440)],[(-52/675),(-103627/118800)],[(1/1200),(-11/1200)],[0,0],[0,0],[0,0],[0,0]]
def vac33Rows05 : List (List Jet) := vac33Rows04 ++ [vac33Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows05_correct : jetRows 1 false 33 5 = vac33Rows05 := by
  rw [jetRows, vac33Rows04_correct]
  change vac33Rows04 ++ [jetStep 1 false 33 5 vac33Rows04] = vac33Rows04 ++ [vac33Row05]
  congr 1
  decide +kernel
def vac33Row06 : List Jet := [[(91201/24192),(88517/4480)],[(-263953/4989600),(5324587/4989600)],[(-2441/712800),(-259/32400)],[(-1/33264),(-1/11088)],[0,0],[0,0],[0,0]]
def vac33Rows06 : List (List Jet) := vac33Rows05 ++ [vac33Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows06_correct : jetRows 1 false 33 6 = vac33Rows06 := by
  rw [jetRows, vac33Rows05_correct]
  change vac33Rows05 ++ [jetStep 1 false 33 6 vac33Rows05] = vac33Rows05 ++ [vac33Row06]
  congr 1
  decide +kernel
def vac33Row07 : List Jet := [[(-393257/169344),(-12549251/282240)],[(3787141/16765056),(16739537/139708800)],[(40021/14968800),(13403/332640)],[(-281/11642400),(281/1164240)],[0,0],[0,0],[0,0]]
def vac33Rows07 : List (List Jet) := vac33Rows06 ++ [vac33Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows07_correct : jetRows 1 false 33 7 = vac33Rows07 := by
  rw [jetRows, vac33Rows06_correct]
  change vac33Rows06 ++ [jetStep 1 false 33 7 vac33Rows06] = vac33Rows06 ++ [vac33Row07]
  congr 1
  decide +kernel
def vac33Row08 : List Jet := [[(-2842723/1354752),(149776133/3386880)],[(-2459409707/8382528000),(-1400406323/523908000)],[(373063/99792000),(-2178217/49896000)],[(1409/12474000),(241/594000)],[(1/1330560),(1/332640)],[0,0],[0,0]]
def vac33Rows08 : List (List Jet) := vac33Rows07 ++ [vac33Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows08_correct : jetRows 1 false 33 8 = vac33Rows08 := by
  rw [jetRows, vac33Rows07_correct]
  change vac33Rows07 ++ [jetStep 1 false 33 8 vac33Rows07] = vac33Rows07 ++ [vac33Row08]
  congr 1
  decide +kernel
def vac33Row09 : List Jet := [[(28008097/3483648),(14474629/1935360)],[(4765184519/75442752000),(185153864911/37721376000)],[(-205047259/15088550400),(-1687332781/37721376000)],[(-403019/4715172000),(-34062377/18860688000)],[(667/838252800),(-667/93139200)],[0,0],[0,0]]
def vac33Rows09 : List (List Jet) := vac33Rows08 ++ [vac33Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows09_correct : jetRows 1 false 33 9 = vac33Rows09 := by
  rw [jetRows, vac33Rows08_correct]
  change vac33Rows08 ++ [jetStep 1 false 33 9 vac33Rows08] = vac33Rows08 ++ [vac33Row09]
  congr 1
  decide +kernel
def vac33Row10 : List Jet := [[(-533516789/48771072),(-14584806379/121927680)],[(247229074577/411505920000),(-11426431044667/4526565120000)],[(3596645027/226328256000),(143500124953/565820640000)],[(-2382221/8981280000),(157469509/94303440000)],[(-83197/17962560000),(-20753/898128000)],[(-1/39916800),(-1/7983360)],[0,0]]
def vac33Rows10 : List (List Jet) := vac33Rows09 ++ [vac33Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows10_correct : jetRows 1 false 33 10 = vac33Rows10 := by
  rw [jetRows, vac33Rows09_correct]
  change vac33Rows09 ++ [jetStep 1 false 33 10 vac33Rows09] = vac33Rows09 ++ [vac33Row10]
  congr 1
  decide +kernel
def vac33Row11 : List Jet := [[(562138655/536481792),(103115514697/447068160)],[(-21264489987871/14226347520000),(-466383209153/37635840000)],[(2745514927/165974054400),(-106834820683/259334460000)],[(1666235171/1659740544000),(18986521271/2766234240000)],[(13735487/4149351360000),(245137223/2074675680000)],[(-793/18441561600),(793/2305195200)],[0,0]]
def vac33Rows11 : List (List Jet) := vac33Rows10 ++ [vac33Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows11_correct : jetRows 1 false 33 11 = vac33Rows11 := by
  rw [jetRows, vac33Rows10_correct]
  change vac33Rows10 ++ [jetStep 1 false 33 11 vac33Rows10] = vac33Rows10 ++ [vac33Row11]
  congr 1
  decide +kernel
def vac33Row12 : List Jet := [[(278256490265/6437781504),(969549437051/32188907520)],[(45130196089511/59750659584000),(181597249511347/3556586880000)],[(-89857299671177/597506595840000),(-1701463365307/2489610816000)],[(-24276021353/27159390720000),(-96463843249/2371057920000)],[(219460127/5532468480000),(-3566991539/49792216320000)],[(132949/296382240000),(904319/296382240000)],[(1/479001600),(1/79833600)]]
def vac33Rows12 : List (List Jet) := vac33Rows11 ++ [vac33Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Rows12_correct : jetRows 1 false 33 12 = vac33Rows12 := by
  rw [jetRows, vac33Rows11_correct]
  change vac33Rows11 ++ [jetStep 1 false 33 12 vac33Rows11] = vac33Rows11 ++ [vac33Row12]
  congr 1
  decide +kernel
def vac33Coeffs : List Jet := [[(29486532725/97542144),(1195047907495/97542144)],[(-2652236728075181/37344162240000),(-5480439268653323/49792216320000)],[(-10557404715469/10669760640000),(-165725878540427/3556586880000)],[(221552591039/3112013520000),(-185011390001/1244805408000)],[(11467823/10373378400),(6080226463/389001690000)],[(-5617/32416807500),(10191803/64833615000)],[(-2/36018675),(16/36018675)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac33Coeffs_correct : widthCoefficients 1 false 33 = vac33Coeffs := by
  rw [widthCoefficients,vac33Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
