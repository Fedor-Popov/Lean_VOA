import VOA.Classification.COne.OrbIcoWSelf10

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self11Rows00 := jetRows 2 true 11 0
theorem self11Rows00_correct : jetRows 2 true 11 0 = self11Rows00 := rfl
def self11Row01 : List Jet := [[(7/6),(-7/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self11Rows01 : List (List Jet) := self11Rows00 ++ [self11Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows01_correct : jetRows 2 true 11 1 = self11Rows01 := by
  rw [jetRows, self11Rows00_correct]
  change self11Rows00 ++ [jetStep 2 true 11 1 self11Rows00] = self11Rows00 ++ [self11Row01]
  congr 1
  decide +kernel
def self11Row02 : List Jet := [[(-65/44),(-65/44),(63/22)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self11Rows02 : List (List Jet) := self11Rows01 ++ [self11Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows02_correct : jetRows 2 true 11 2 = self11Rows02 := by
  rw [jetRows, self11Rows01_correct]
  change self11Rows01 ++ [jetStep 2 true 11 2 self11Rows01] = self11Rows01 ++ [self11Row02]
  congr 1
  decide +kernel
def self11Row03 : List Jet := [[(21/220),(97/22),(53/220)],[(-119/1980),(119/1980),(119/990)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self11Rows03 : List (List Jet) := self11Rows02 ++ [self11Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows03_correct : jetRows 2 true 11 3 = self11Rows03 := by
  rw [jetRows, self11Rows02_correct]
  change self11Rows02 ++ [jetStep 2 true 11 3 self11Rows02] = self11Rows02 ++ [self11Row03]
  congr 1
  decide +kernel
def self11Row04 : List Jet := [[(4249/2640),(-4417/1584),(-46489/7920)],[(47/594),(256/1485),(-227/2970)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self11Rows04 : List (List Jet) := self11Rows03 ++ [self11Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows04_correct : jetRows 2 true 11 4 = self11Rows04 := by
  rw [jetRows, self11Rows03_correct]
  change self11Rows03 ++ [jetStep 2 true 11 4 self11Rows03] = self11Rows03 ++ [self11Row04]
  congr 1
  decide +kernel
def self11Row05 : List Jet := [[(-40299/17600),(-46599/17600),(380579/52800)],[(97/11880),(-21667/79200),(-12557/39600)],[(7/3600),0,(-7/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self11Rows05 : List (List Jet) := self11Rows04 ++ [self11Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows05_correct : jetRows 2 true 11 5 = self11Rows05 := by
  rw [jetRows, self11Rows04_correct]
  change self11Rows04 ++ [jetStep 2 true 11 5 self11Rows04] = self11Rows04 ++ [self11Row05]
  congr 1
  decide +kernel
def self11Row06 : List Jet := [[(44219/35200),(35177/4400),(-153437/554400)],[(-125179/997920),(19853/907200),(2029157/3326400)],[(-2687/997920),(-5113/554400),(-1273/332640)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self11Rows06 : List (List Jet) := self11Rows05 ++ [self11Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows06_correct : jetRows 2 true 11 6 = self11Rows06 := by
  rw [jetRows, self11Rows05_correct]
  change self11Rows05 ++ [jetStep 2 true 11 6 self11Rows05] = self11Rows05 ++ [self11Row06]
  congr 1
  decide +kernel
def self11Row07 : List Jet := [[(2291/1920),(-410033/49280),(-26410313/2116800)],[(2048041/12700800),(11278067/23284800),(-14591767/69854400)],[(-104351/104781600),(417817/41912640),(1786777/69854400)],[(-281/4989600),(-281/4989600),(281/1663200)],[0,0,0],[0,0,0],[0,0,0]]
def self11Rows07 : List (List Jet) := self11Rows06 ++ [self11Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows07_correct : jetRows 2 true 11 7 = self11Rows07 := by
  rw [jetRows, self11Rows06_correct]
  change self11Rows06 ++ [jetStep 2 true 11 7 self11Rows06] = self11Rows06 ++ [self11Row07]
  congr 1
  decide +kernel
def self11Row08 : List Jet := [[(-5210807/1408000),(269909/704000),(1882491899/88704000)],[(-86710541/2794176000),(-41206559/50803200),(-93293729/87318000)],[(13812901/2095632000),(3481607/381024000),(-56989781/2095632000)],[(19/226800),(2507/6237000),(241/519750)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self11Rows08 : List (List Jet) := self11Rows07 ++ [self11Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows08_correct : jetRows 2 true 11 8 = self11Rows08 := by
  rw [jetRows, self11Rows07_correct]
  change self11Rows07 ++ [jetStep 2 true 11 8 self11Rows07] = self11Rows07 ++ [self11Row08]
  congr 1
  decide +kernel
def self11Row09 : List Jet := [[(11470167/2816000),(626039509/44352000),(-13887568633/1241856000)],[(-180981223/718502400),(5398963597/16765056000),(24265055113/10059033600)],[(-79768201/10777536000),(-70821589/1714608000),(-1290420101/37721376000)],[(5497/75442752),(-10750199/37721376000),(-2787341/1886068800)],[(667/359251200),(667/179625600),(-667/179625600)],[0,0,0],[0,0,0]]
def self11Rows09 : List (List Jet) := self11Rows08 ++ [self11Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows09_correct : jetRows 2 true 11 9 = self11Rows09 := by
  rw [jetRows, self11Rows08_correct]
  change self11Rows08 ++ [jetStep 2 true 11 9 self11Rows08] = self11Rows08 ++ [self11Row09]
  congr 1
  decide +kernel
def self11Row10 : List Jet := [[(242991/28160000),(-18702084541/760320000),(-51542462099/1774080000)],[(1402729961/2874009600),(4692574363/3265920000),(-107075537533/71850240000)],[(-1177334479/226328256000),(457768763/10059033600),(2227901833/13716864000)],[(-206351599/565820640000),(-211864231/188606880000),(164489/392931000)],[(-11197/3592512000),(-32927/1632960000),(-171371/4490640000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self11Rows10 : List (List Jet) := self11Rows09 ++ [self11Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows10_correct : jetRows 2 true 11 10 = self11Rows10 := by
  rw [jetRows, self11Rows09_correct]
  change self11Rows09 ++ [jetStep 2 true 11 10 self11Rows09] = self11Rows09 ++ [self11Row10]
  congr 1
  decide +kernel
def self11Row11 : List Jet := [[(-255869523/28160000),(81078391/12672000),(24906101863/295680000)],[(-51233875247/316141056000),(-13652273520467/3688312320000),(-21008170230059/3688312320000)],[(1217396351/35565868800),(714112558793/9958443264000),(-319381204189/1659740544000)],[(2461076047/8298702720000),(29610336433/8298702720000),(163988173/20956320000)],[(-5763281/829870272000),(4457743/1383117120000),(35457997/345779280000)],[(-793/7903526400),(-793/2634508800),0],[0,0,0]]
def self11Rows11 : List (List Jet) := self11Rows10 ++ [self11Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows11_correct : jetRows 2 true 11 11 = self11Rows11 := by
  rw [jetRows, self11Rows10_correct]
  change self11Rows10 ++ [jetStep 2 true 11 11 self11Rows10] = self11Rows10 ++ [self11Row11]
  congr 1
  decide +kernel
def self11Row12 : List Jet := [[(29401911/2048000),(6003137533/67584000),(-1302350029/80640000)],[(-8901820266667/4742115840000),(451791008807/2371057920000),(241195439862647/11064936960000)],[(-5704835383/136572936192),(-19921680586007/42679042560000),(-870885492061/1185528960000)],[(585172490993/298753297920000),(13213129681/27159390720000),(-2625828428527/99584432640000)],[(5956907833/149376648960000),(229725539/1066976064000),(1675639327/7113173760000)],[(14149/59276448000),(55337/24698520000),(68351/10977120000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self11Rows12 : List (List Jet) := self11Rows11 ++ [self11Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Rows12_correct : jetRows 2 true 11 12 = self11Rows12 := by
  rw [jetRows, self11Rows11_correct]
  change self11Rows11 ++ [jetStep 2 true 11 12 self11Rows11] = self11Rows11 ++ [self11Row12]
  congr 1
  decide +kernel
def self11Coeffs : List Jet := [[(-1682226693/5120000),(13849236541/28160000),(107339494509/28160000)],[(-602243701181/56453760000),(-59579359811443/316141056000),(-767073774631531/11064936960000)],[(3724054895359/2133952128000),(-3105360207643/10669760640000),(-7170039334949/307359360000)],[(8361587911/233401014000),(10876638785647/37344162240000),(1641443519/8230118400)],[(-105141983/259334460000),(5183099983/1556006760000),(8161968721/518668920000)],[(-44497/3241680750),(-946877/43222410000),(4874143/43222410000)],[(-2/15436575),(-2/5145525),0]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self11Coeffs_correct : widthCoefficients 2 true 11 = self11Coeffs := by
  rw [widthCoefficients,self11Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
