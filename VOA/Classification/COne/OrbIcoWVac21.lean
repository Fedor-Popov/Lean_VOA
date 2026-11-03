import VOA.Classification.COne.OrbIcoWVac20

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac21Rows00 := jetRows 2 false 21 0
theorem vac21Rows00_correct : jetRows 2 false 21 0 = vac21Rows00 := rfl
def vac21Row01 : List Jet := [[(5/2),(-9/2),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac21Rows01 : List (List Jet) := vac21Rows00 ++ [vac21Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows01_correct : jetRows 2 false 21 1 = vac21Rows01 := by
  rw [jetRows, vac21Rows00_correct]
  change vac21Rows00 ++ [jetStep 2 false 21 1 vac21Rows00] = vac21Rows00 ++ [vac21Row01]
  congr 1
  decide +kernel
def vac21Row02 : List Jet := [[(23/44),(-106/11),(477/44)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac21Rows02 : List (List Jet) := vac21Rows01 ++ [vac21Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows02_correct : jetRows 2 false 21 2 = vac21Rows02 := by
  rw [jetRows, vac21Rows01_correct]
  change vac21Rows01 ++ [jetStep 2 false 21 2 vac21Rows01] = vac21Rows01 ++ [vac21Row02]
  congr 1
  decide +kernel
def vac21Row03 : List Jet := [[(-1073/660),(87/55),(233/12)],[(-17/132),(17/165),(51/220)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac21Rows03 : List (List Jet) := vac21Rows02 ++ [vac21Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows03_correct : jetRows 2 false 21 3 = vac21Rows03 := by
  rw [jetRows, vac21Rows02_correct]
  change vac21Rows02 ++ [jetStep 2 false 21 3 vac21Rows02] = vac21Rows02 ++ [vac21Row03]
  congr 1
  decide +kernel
def vac21Row04 : List Jet := [[(6667/7920),(11735/1584),(-97573/7920)],[(-25/594),(1601/2970),(-91/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac21Rows04 : List (List Jet) := vac21Rows03 ++ [vac21Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows04_correct : jetRows 2 false 21 4 = vac21Rows04 := by
  rw [jetRows, vac21Rows03_correct]
  change vac21Rows03 ++ [jetStep 2 false 21 4 vac21Rows03] = vac21Rows03 ++ [vac21Row04]
  congr 1
  decide +kernel
def vac21Row05 : List Jet := [[(85781/158400),(-599251/79200),(-405373/26400)],[(6343/59400),(301/3600),(-56869/39600)],[(1/240),(1/1200),(-13/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac21Rows05 : List (List Jet) := vac21Rows04 ++ [vac21Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows05_correct : jetRows 2 false 21 5 = vac21Rows05 := by
  rw [jetRows, vac21Rows04_correct]
  change vac21Rows04 ++ [jetStep 2 false 21 5 vac21Rows04] = vac21Rows04 ++ [vac21Row05]
  congr 1
  decide +kernel
def vac21Row06 : List Jet := [[(-255059/190080),(-104377/950400),(6810671/237600)],[(-24581/712800),(-158687/237600),(25703/415800)],[(2089/997920),(-5167/277200),(-7817/415800)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac21Rows06 : List (List Jet) := vac21Rows05 ++ [vac21Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows06_correct : jetRows 2 false 21 6 = vac21Rows06 := by
  rw [jetRows, vac21Rows05_correct]
  change vac21Rows05 ++ [jetStep 2 false 21 6 vac21Rows05] = vac21Rows05 ++ [vac21Row06]
  congr 1
  decide +kernel
def vac21Row07 : List Jet := [[(6685339/6652800),(11955/1408),(-43551/4400)],[(-988469/11975040),(24642341/59875200),(13865227/5821200)],[(-474451/104781600),(-1325953/104781600),(127717/2182950)],[(-281/2328480),(-281/1940400),(281/970200)],[0,0,0],[0,0,0],[0,0,0]]
def vac21Rows07 : List (List Jet) := vac21Rows06 ++ [vac21Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows07_correct : jetRows 2 false 21 7 = vac21Rows07 := by
  rw [jetRows, vac21Rows06_correct]
  change vac21Rows06 ++ [jetStep 2 false 21 7 vac21Rows06] = vac21Rows06 ++ [vac21Row07]
  congr 1
  decide +kernel
def vac21Row08 : List Jet := [[(5520527/24192000),(-256349399/26611200),(-358983839/12672000)],[(4258813/34214400),(2355757/4276800),(-526968689/239500800)],[(-3751/63504000),(12766309/349272000),(38716879/698544000)],[(-1681/17463600),(49339/87318000),(7951/5821200)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac21Rows08 : List (List Jet) := vac21Rows07 ++ [vac21Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows08_correct : jetRows 2 false 21 8 = vac21Rows08 := by
  rw [jetRows, vac21Rows07_correct]
  change vac21Rows07 ++ [jetStep 2 false 21 8 vac21Rows07] = vac21Rows07 ++ [vac21Row08]
  congr 1
  decide +kernel
def vac21Row09 : List Jet := [[(-6757219717/4790016000),(211684993/1596672000),(224948859109/4790016000)],[(-9462773/431101440),(-23482979/19245600),(-34588238611/15088550400)],[(10743617/1539648000),(-20836297/37721376000),(-13976360557/75442752000)],[(48401/269438400),(18670483/18860688000),(-32861113/18860688000)],[(667/167650560),(667/76204800),(-667/139708800)],[0,0,0],[0,0,0]]
def vac21Rows09 : List (List Jet) := vac21Rows08 ++ [vac21Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows09_correct : jetRows 2 false 21 9 = vac21Rows09 := by
  rw [jetRows, vac21Rows08_correct]
  change vac21Rows08 ++ [jetStep 2 false 21 9 vac21Rows08] = vac21Rows08 ++ [vac21Row09]
  congr 1
  decide +kernel
def vac21Row10 : List Jet := [[(5498539561/4354560000),(36904173857/2661120000),(-18738762019/5987520000)],[(-10007120957/58786560000),(59939162681/215550720000),(1542472786693/215550720000)],[(-38929537/6466521600),(-44637071/538876800),(-3960071/307929600)],[(26726899/188606880000),(-15369497/8573040000),(-1350846463/188606880000)],[(142493/25147584000),(-588493/31434480000),(-11149007/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac21Rows10 : List (List Jet) := vac21Rows09 ++ [vac21Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows10_correct : jetRows 2 false 21 10 = vac21Rows10 := by
  rw [jetRows, vac21Rows09_correct]
  change vac21Rows09 ++ [jetStep 2 false 21 10 vac21Rows09] = vac21Rows09 ++ [vac21Row10]
  congr 1
  decide +kernel
def vac21Row11 : List Jet := [[(843143639/870912000),(-307296549761/23950080000),(-3596810668553/37635840000)],[(262345562879/1293304320000),(1643414553073/646652160000),(-34237457/77440000)],[(-347784511/29638224000),(1337283863/18860688000),(5302289551/7683984000)],[(-9113347/15396480000),(-26175259427/8298702720000),(32096595037/2766234240000)],[(-7099801/829870272000),(-67833851/691558560000),(-171893/276623424000)],[(-793/3688312320),(-793/1152597600),(-793/3688312320)],[0,0,0]]
def vac21Rows11 : List (List Jet) := vac21Rows10 ++ [vac21Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows11_correct : jetRows 2 false 21 11 = vac21Rows11 := by
  rw [jetRows, vac21Rows10_correct]
  change vac21Rows10 ++ [jetStep 2 false 21 11 vac21Rows10] = vac21Rows10 ++ [vac21Row11]
  congr 1
  decide +kernel
def vac21Row12 : List Jet := [[(-155609183171/52254720000),(-2191088701027/63866880000),(25871983444067/790352640000)],[(328668185963/775982592000),(-600040734217/277136640000),(-12863274796861/395176320000)],[(2506678621577/85358085120000),(1997978824949/5334880320000),(-25373086664249/99584432640000)],[(-91619323/155196518400),(263249384831/21339521280000),(20705466523/338722560000)],[(-189839423/4526565120000),(609403181/9958443264000),(2202631/1517824000)],[(-369221/414935136000),(1057/1283040000),(829/68040000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac21Rows12 : List (List Jet) := vac21Rows11 ++ [vac21Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Rows12_correct : jetRows 2 false 21 12 = vac21Rows12 := by
  rw [jetRows, vac21Rows11_correct]
  change vac21Rows11 ++ [jetStep 2 false 21 12 vac21Rows11] = vac21Rows11 ++ [vac21Row12]
  congr 1
  decide +kernel
def vac21Coeffs : List Jet := [[(87165995449/1244160000),(365097387317/1520640000),(-82227236127181/18817920000)],[(-2115911269/2519424000),(7063492821647/55427328000),(11821250185783/33872256000)],[(-1245482305187/1524251520000),(-3729079949981/10669760640000),(647260753727747/12448054080000)],[(-1728391157/74095560000),(-322898161829/889146720000),(218358956887/296382240000)],[(59630911/778003380000),(-4474050233/389001690000),(-1892328617/129667230000)],[(1189/147349125),(-4530461/21611205000),(-208171/1080560250)],[(-2/7203735),(-32/36018675),(-2/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac21Coeffs_correct : widthCoefficients 2 false 21 = vac21Coeffs := by
  rw [widthCoefficients,vac21Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
