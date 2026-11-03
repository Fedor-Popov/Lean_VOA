import VOA.Classification.COne.OrbIcoWVac28

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac29Rows00 := jetRows 2 false 29 0
theorem vac29Rows00_correct : jetRows 2 false 29 0 = vac29Rows00 := rfl
def vac29Row01 : List Jet := [[(7/6),(-35/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac29Rows01 : List (List Jet) := vac29Rows00 ++ [vac29Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows01_correct : jetRows 2 false 29 1 = vac29Rows01 := by
  rw [jetRows, vac29Rows00_correct]
  change vac29Rows00 ++ [jetStep 2 false 29 1 vac29Rows00] = vac29Rows00 ++ [vac29Row01]
  congr 1
  decide +kernel
def vac29Row02 : List Jet := [[(-65/44),(-46/11),(805/44)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac29Rows02 : List (List Jet) := vac29Rows01 ++ [vac29Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows02_correct : jetRows 2 false 29 2 = vac29Rows02 := by
  rw [jetRows, vac29Rows01_correct]
  change vac29Rows01 ++ [jetStep 2 false 29 2 vac29Rows01] = vac29Rows01 ++ [vac29Row02]
  congr 1
  decide +kernel
def vac29Row03 : List Jet := [[(21/220),(617/55),(3071/660)],[(-119/1980),(119/495),(119/396)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac29Rows03 : List (List Jet) := vac29Rows02 ++ [vac29Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows03_correct : jetRows 2 false 29 3 = vac29Rows03 := by
  rw [jetRows, vac29Rows02_correct]
  change vac29Rows02 ++ [jetStep 2 false 29 3 vac29Rows02] = vac29Rows02 ++ [vac29Row03]
  congr 1
  decide +kernel
def vac29Row04 : List Jet := [[(4249/2640),(-1477/240),(-964151/23760)],[(47/594),(1009/2970),(-1223/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac29Rows04 : List (List Jet) := vac29Rows03 ++ [vac29Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows04_correct : jetRows 2 false 29 4 = vac29Rows04 := by
  rw [jetRows, vac29Rows03_correct]
  change vac29Rows03 ++ [jetStep 2 false 29 4 vac29Rows03] = vac29Rows03 ++ [vac29Row04]
  congr 1
  decide +kernel
def vac29Row05 : List Jet := [[(-40299/17600),(-72471/8800),(1112179/26400)],[(97/11880),(-83779/118800),(-5029/4400)],[(7/3600),(-7/1200),(-7/400)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac29Rows05 : List (List Jet) := vac29Rows04 ++ [vac29Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows05_correct : jetRows 2 false 29 5 = vac29Rows05 := by
  rw [jetRows, vac29Rows04_correct]
  change vac29Rows04 ++ [jetStep 2 false 29 5 vac29Rows04] = vac29Rows04 ++ [vac29Row05]
  congr 1
  decide +kernel
def vac29Row06 : List Jet := [[(44219/35200),(2230031/105600),(6943093/554400)],[(-125179/997920),(894217/4989600),(4312103/1247400)],[(-2687/997920),(-39847/2494800),(7451/415800)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac29Rows06 : List (List Jet) := vac29Rows05 ++ [vac29Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows06_correct : jetRows 2 false 29 6 = vac29Rows06 := by
  rw [jetRows, vac29Rows05_correct]
  change vac29Rows05 ++ [jetStep 2 false 29 6 vac29Rows05] = vac29Rows05 ++ [vac29Row06]
  congr 1
  decide +kernel
def vac29Row07 : List Jet := [[(2291/1920),(-43688011/2217600),(-563887981/5821200)],[(2048041/12700800),(5650067/5174400),(-1982621/970200)],[(-104351/104781600),(196517/6985440),(1115641/13097700)],[(-281/4989600),(281/2494800),(281/415800)],[0,0,0],[0,0,0],[0,0,0]]
def vac29Rows07 : List (List Jet) := vac29Rows06 ++ [vac29Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows07_correct : jetRows 2 false 29 7 = vac29Rows07 := by
  rw [jetRows, vac29Rows06_correct]
  change vac29Rows06 ++ [jetStep 2 false 29 7 vac29Rows06] = vac29Rows06 ++ [vac29Row07]
  congr 1
  decide +kernel
def vac29Row08 : List Jet := [[(-5210807/1408000),(-6955093/2112000),(11958680903/88704000)],[(-86710541/2794176000),(-711313363/349272000),(-4913224403/931392000)],[(13812901/2095632000),(6824471/1047816000),(-375563239/2095632000)],[(19/226800),(131/198000),(-601/12474000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac29Rows08 : List (List Jet) := vac29Rows07 ++ [vac29Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows08_correct : jetRows 2 false 29 8 = vac29Rows08 := by
  rw [jetRows, vac29Rows07_correct]
  change vac29Rows07 ++ [jetStep 2 false 29 8 vac29Rows07] = vac29Rows07 ++ [vac29Row08]
  congr 1
  decide +kernel
def vac29Row09 : List Jet := [[(11470167/2816000),(1454128493/35481600),(-9132536839/338688000)],[(-180981223/718502400),(2009862413/2095632000),(362115033359/25147584000)],[(-79768201/10777536000),(-661768237/7544275200),(-1473377069/75442752000)],[(5497/75442752),(-19649909/18860688000),(-19431833/3772137600)],[(667/359251200),(-667/359251200),(-667/25660800)],[0,0,0],[0,0,0]]
def vac29Rows09 : List (List Jet) := vac29Rows08 ++ [vac29Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows09_correct : jetRows 2 false 29 9 = vac29Rows09 := by
  rw [jetRows, vac29Rows08_correct]
  change vac29Rows08 ++ [jetStep 2 false 29 9 vac29Rows08] = vac29Rows08 ++ [vac29Row09]
  congr 1
  decide +kernel
def vac29Row10 : List Jet := [[(242991/28160000),(-23716112609/380160000),(-550473071831/1995840000)],[(1402729961/2874009600),(83376761921/23950080000),(-30014158337/2874009600)],[(-1177334479/226328256000),(18221125099/141455160000),(18709024931/25147584000)],[(-206351599/565820640000),(-388379401/282910320000),(1629136073/188606880000)],[(-11197/3592512000),(-148871/4490640000),(-522241/17962560000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac29Rows10 : List (List Jet) := vac29Rows09 ++ [vac29Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows10_correct : jetRows 2 false 29 10 = vac29Rows10 := by
  rw [jetRows, vac29Rows09_correct]
  change vac29Rows09 ++ [jetStep 2 false 29 10 vac29Rows09] = vac29Rows09 ++ [vac29Row10]
  congr 1
  decide +kernel
def vac29Row11 : List Jet := [[(-255869523/28160000),(75754279/126720000),(16950610696529/29272320000)],[(-51233875247/316141056000),(-52725580540379/5532468480000),(-96633901097813/2766234240000)],[(1217396351/35565868800),(1534624577/13831171200),(-4466584261291/3112013520000)],[(2461076047/8298702720000),(6047710247/754427520000),(156179992951/8298702720000)],[(-5763281/829870272000),(101974559/2074675680000),(65034839/153679680000)],[(-793/7903526400),0,(793/526901760)],[0,0,0]]
def vac29Rows11 : List (List Jet) := vac29Rows10 ++ [vac29Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows11_correct : jetRows 2 false 29 11 = vac29Rows11 := by
  rw [jetRows, vac29Rows10_correct]
  change vac29Rows10 ++ [jetStep 2 false 29 11 vac29Rows10] = vac29Rows10 ++ [vac29Row11]
  congr 1
  decide +kernel
def vac29Row12 : List Jet := [[(29401911/2048000),(88546790393/337920000),(1591790974633/4878720000)],[(-8901820266667/4742115840000),(577627507111/790352640000),(303963120134519/2074675680000)],[(-5704835383/136572936192),(-2022536240717/1778293440000),(-4568953445269/1707161702400)],[(585172490993/298753297920000),(-65048214617/9958443264000),(-22523306246701/149376648960000)],[(5956907833/149376648960000),(258120791/790352640000),(-11918020393/21339521280000)],[(14149/59276448000),(1174423/296382240000),(7229/987940800)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac29Rows12 : List (List Jet) := vac29Rows11 ++ [vac29Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Rows12_correct : jetRows 2 false 29 12 = vac29Rows12 := by
  rw [jetRows, vac29Rows11_correct]
  change vac29Rows11 ++ [jetStep 2 false 29 12 vac29Rows11] = vac29Rows11 ++ [vac29Row12]
  congr 1
  decide +kernel
def vac29Coeffs : List Jet := [[(-1682226693/5120000),(9873838191/56320000),(11677921489999/348480000)],[(-602243701181/56453760000),(-140318734579813/263450880000),(-3466279568758439/2766234240000)],[(3724054895359/2133952128000),(-1137878998027/711317376000),(-557032837211177/3394923840000)],[(8361587911/233401014000),(53082632873/76839840000),(-142703037887/746883244800)],[(-105141983/259334460000),(369814213/35363790000),(24611377213/389001690000)],[(-44497/3241680750),(1621349/64833615000),(619282/900466875)],[(-2/15436575),0,(2/1029105)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac29Coeffs_correct : widthCoefficients 2 false 29 = vac29Coeffs := by
  rw [widthCoefficients,vac29Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
