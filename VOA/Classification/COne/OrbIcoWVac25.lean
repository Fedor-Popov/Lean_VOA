import VOA.Classification.COne.OrbIcoWVac24

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def vac25Rows00 := jetRows 2 false 25 0
theorem vac25Rows00_correct : jetRows 2 false 25 0 = vac25Rows00 := rfl
def vac25Row01 : List Jet := [[(11/6),(-31/6),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac25Rows01 : List (List Jet) := vac25Rows00 ++ [vac25Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows01_correct : jetRows 2 false 25 1 = vac25Rows01 := by
  rw [jetRows, vac25Rows00_correct]
  change vac25Rows00 ++ [jetStep 2 false 25 1 vac25Rows00] = vac25Rows00 ++ [vac25Row01]
  congr 1
  decide +kernel
def vac25Row02 : List Jet := [[(-95/132),(-244/33),(1891/132)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac25Rows02 : List (List Jet) := vac25Rows01 ++ [vac25Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows02_correct : jetRows 2 false 25 2 = vac25Rows02 := by
  rw [jetRows, vac25Rows01_correct]
  change vac25Rows01 ++ [jetStep 2 false 25 2 vac25Rows01] = vac25Rows01 ++ [vac25Row02]
  congr 1
  decide +kernel
def vac25Row03 : List Jet := [[(-415/396),(724/99),(5825/396)],[(-17/180),(17/99),(527/1980)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac25Rows03 : List (List Jet) := vac25Rows02 ++ [vac25Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows03_correct : jetRows 2 false 25 3 = vac25Rows03 := by
  rw [jetRows, vac25Rows02_correct]
  change vac25Rows02 ++ [jetStep 2 false 25 3 vac25Rows02] = vac25Rows02 ++ [vac25Row03]
  congr 1
  decide +kernel
def vac25Row04 : List Jet := [[(24215/14256),(12689/4752),(-15167/528)],[(293/8910),(1433/2970),(-593/1485)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac25Rows04 : List (List Jet) := vac25Rows03 ++ [vac25Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows04_correct : jetRows 2 false 25 4 = vac25Rows04 := by
  rw [jetRows, vac25Rows03_correct]
  change vac25Rows03 ++ [jetStep 2 false 25 4 vac25Rows03] = vac25Rows03 ++ [vac25Row04]
  congr 1
  decide +kernel
def vac25Row05 : List Jet := [[(-50135/57024),(-1659557/142560),(41771/9504)],[(2329/29700),(-41659/118800),(-6753/4400)],[(11/3600),(-1/400),(-17/1200)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def vac25Rows05 : List (List Jet) := vac25Rows04 ++ [vac25Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows05_correct : jetRows 2 false 25 5 = vac25Rows05 := by
  rw [jetRows, vac25Rows04_correct]
  change vac25Rows04 ++ [jetStep 2 false 25 5 vac25Rows04] = vac25Rows04 ++ [vac25Row05]
  congr 1
  decide +kernel
def vac25Row06 : List Jet := [[(-256915/342144),(129996277/11975040),(9581921/249480)],[(-68063/598752),(-6793307/14968800),(13437/7700)],[(-12773/14968800),(-146101/7484400),(-4693/1247400)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def vac25Rows06 : List (List Jet) := vac25Rows05 ++ [vac25Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows06_correct : jetRows 2 false 25 6 = vac25Rows06 := by
  rw [jetRows, vac25Rows05_correct]
  change vac25Rows05 ++ [jetStep 2 false 25 6 vac25Rows05] = vac25Rows05 ++ [vac25Row06]
  congr 1
  decide +kernel
def vac25Row07 : List Jet := [[(2080495/1026432),(8449205/7185024),(-254512451/4490640)],[(33645343/1257379200),(1322063129/1257379200),(17753191/12573792)],[(-80077/20956320),(291983/34927200),(2224451/26195400)],[(-281/3175200),(-281/17463600),(281/582120)],[0,0,0],[0,0,0],[0,0,0]]
def vac25Rows07 : List (List Jet) := vac25Rows06 ++ [vac25Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows07_correct : jetRows 2 false 25 7 = vac25Rows07 := by
  rw [jetRows, vac25Rows06_correct]
  change vac25Rows06 ++ [jetStep 2 false 25 7 vac25Rows06] = vac25Rows06 ++ [vac25Row07]
  congr 1
  decide +kernel
def vac25Row08 : List Jet := [[(-15177995/8211456),(-18132683/1064448),(1411511621/95800320)],[(1089008029/8382528000),(-46671733/87318000),(-15107543557/2794176000)],[(227587/46569600),(7486879/209563200),(-19380497/419126400)],[(3677/261954000),(7489/10478160),(225707/261954000)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def vac25Rows08 : List (List Jet) := vac25Rows07 ++ [vac25Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows08_correct : jetRows 2 false 25 8 = vac25Rows08 := by
  rw [jetRows, vac25Rows07_correct]
  change vac25Rows07 ++ [jetStep 2 false 25 8 vac25Rows07] = vac25Rows07 ++ [vac25Row08]
  congr 1
  decide +kernel
def vac25Row09 : List Jet := [[(-2575195/13436928),(7612426595/344881152),(139039729921/1724405760)],[(-996426479/4618944000),(-6790041253/5388768000),(8961761621/2155507200)],[(76441727/45265651200),(-445143121/7544275200),(-3218571161/15088550400)],[(214591/1178793000),(56531/3772137600),(-76932739/18860688000)],[(667/228614400),(8671/2514758400),(-19343/1257379200)],[0,0,0],[0,0,0]]
def vac25Rows09 : List (List Jet) := vac25Rows08 ++ [vac25Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows09_correct : jetRows 2 false 25 9 = vac25Rows09 := by
  rw [jetRows, vac25Rows08_correct]
  change vac25Rows08 ++ [jetStep 2 false 25 9 vac25Rows08] = vac25Rows08 ++ [vac25Row09]
  congr 1
  decide +kernel
def vac25Row10 : List Jet := [[(2745758561/886837248),(-11637032167/15519651840),(-467291010409/3233260800)],[(65256481883/1234517760000),(39643519989727/13579695360000),(36335399879729/4526565120000)],[(-1635013997/125737920000),(-1793957743/80831520000),(165218023391/377213760000)],[(-4283171/22632825600),(-29681033/11316412800),(-56995391/37721376000)],[(119159/377213760000),(-996143/31434480000),(-9210827/125737920000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def vac25Rows10 : List (List Jet) := vac25Rows09 ++ [vac25Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows10_correct : jetRows 2 false 25 10 = vac25Rows10 := by
  rw [jetRows, vac25Rows09_correct]
  change vac25Rows09 ++ [jetStep 2 false 25 10 vac25Rows09] = vac25Rows09 ++ [vac25Row10]
  congr 1
  decide +kernel
def vac25Row11 : List Jet := [[(-34956381019/9755209728),(-8038967998517/170716170240),(-9992262794051/853580851200)],[(8647494834211/19916886528000),(-29421323835707/49792216320000),(-210520879210273/8298702720000)],[(21764185649/1778293440000),(52683818441/222286680000),(64229790853/222286680000)],[(-2209713719/4979221632000),(13885308659/4979221632000),(26909637389/995844326400)],[(-52046377/4149351360000),(-71436361/2074675680000),(38750699/153679680000)],[(-793/5029516800),(-793/2305195200),(793/1229437440)],[0,0,0]]
def vac25Rows11 : List (List Jet) := vac25Rows10 ++ [vac25Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows11_correct : jetRows 2 false 25 11 = vac25Rows11 := by
  rw [jetRows, vac25Rows10_correct]
  change vac25Rows10 ++ [jetStep 2 false 25 11 vac25Rows10] = vac25Rows10 ++ [vac25Row11]
  congr 1
  decide +kernel
def vac25Row12 : List Jet := [[(-58399410055/10642046976),(39866310406379/819437617152),(638369753117009/1024297021440)],[(-628256872830679/896259893760000),(-350540160315187/28008121680000),(-4699174693947047/448129946880000)],[(3341396209597/71700791500800),(-21947160380203/112032486720000),(-3264192492899761/896259893760000)],[(494264051621/298753297920000),(100509333577/5975065958400),(-1170763532167/49792216320000)],[(12866863/4267904256000),(8343151/22767360000),(158264484181/149376648960000)],[(-117373/565820640000),(2863117/889146720000),(453143/37047780000)],[(1/479001600),(1/79833600),(1/31933440)]]
def vac25Rows12 : List (List Jet) := vac25Rows11 ++ [vac25Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Rows12_correct : jetRows 2 false 25 12 = vac25Rows12 := by
  rw [jetRows, vac25Rows11_correct]
  change vac25Rows11 ++ [jetStep 2 false 25 12 vac25Rows11] = vac25Rows11 ++ [vac25Row12]
  congr 1
  decide +kernel
def vac25Coeffs : List Jet := [[(-2031489599825/58531258368),(-120847947032275/58531258368),(-424750330112771/102429702144)],[(1106202466626167/56016243360000),(2176098504373693/89625989376000),(-347425079629757359/224064973440000)],[(5967395116241/14937664896000),(225219141964349/14937664896000),(37396210583273/2489610816000)],[(-43284873439/1333720080000),(648637881979/2667440160000),(121010007929/42340320000)],[(-2474501149/2334010140000),(-1704286417/389001690000),(55422833699/1167005070000)],[(-470443/32416807500),(-7909921/64833615000),(1133723/3601867500)],[(-2/9823275),(-16/36018675),(2/2401245)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem vac25Coeffs_correct : widthCoefficients 2 false 25 = vac25Coeffs := by
  rw [widthCoefficients,vac25Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
