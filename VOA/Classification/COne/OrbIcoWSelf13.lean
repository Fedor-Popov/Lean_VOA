import VOA.Classification.COne.OrbIcoWSelf12

/-! Exact finite BSA coefficient jets, with cached kernel-checked stages. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbIcoW
def self13Rows00 := jetRows 2 true 13 0
theorem self13Rows00_correct : jetRows 2 true 13 0 = self13Rows00 := rfl
def self13Row01 : List Jet := [[(5/6),(-8/3),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self13Rows01 : List (List Jet) := self13Rows00 ++ [self13Row01]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows01_correct : jetRows 2 true 13 1 = self13Rows01 := by
  rw [jetRows, self13Rows00_correct]
  change self13Rows00 ++ [jetStep 2 true 13 1 self13Rows00] = self13Rows00 ++ [self13Row01]
  congr 1
  decide +kernel
def self13Row02 : List Jet := [[(-221/132),(-103/132),(124/33)],[(-1/22),(-1/22),0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self13Rows02 : List (List Jet) := self13Rows01 ++ [self13Row02]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows02_correct : jetRows 2 true 13 2 = self13Rows02 := by
  rw [jetRows, self13Rows01_correct]
  change self13Rows01 ++ [jetStep 2 true 13 2 self13Rows01] = self13Rows01 ++ [self13Row02]
  congr 1
  decide +kernel
def self13Row03 : List Jet := [[(1501/1980),(505/99),(-181/180)],[(-17/396),(17/180),(68/495)],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self13Rows03 : List (List Jet) := self13Rows02 ++ [self13Row03]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows03_correct : jetRows 2 true 13 3 = self13Rows03 := by
  rw [jetRows, self13Rows02_correct]
  change self13Rows02 ++ [jetStep 2 true 13 3 self13Rows02] = self13Rows02 ++ [self13Row03]
  congr 1
  decide +kernel
def self13Row04 : List Jet := [[(81943/71280),(-122533/23760),(-168161/23760)],[(163/1782),(214/1485),(-101/594)],[(1/792),(1/396),(1/792)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self13Rows04 : List (List Jet) := self13Rows03 ++ [self13Row04]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows04_correct : jetRows 2 true 13 4 = self13Rows04 := by
  rw [jetRows, self13Rows03_correct]
  change self13Rows03 ++ [jetStep 2 true 13 4 self13Rows03] = self13Rows03 ++ [self13Row04]
  congr 1
  decide +kernel
def self13Row05 : List Jet := [[(-3808301/1425600),(-148729/285120),(647941/52800)],[(-4069/118800),(-86893/237600),(-3769/13200)],[(1/720),(-1/600),(-3/400)],[0,0,0],[0,0,0],[0,0,0],[0,0,0]]
def self13Rows05 : List (List Jet) := self13Rows04 ++ [self13Row05]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows05_correct : jetRows 2 true 13 5 = self13Rows05 := by
  rw [jetRows, self13Rows04_correct]
  change self13Rows04 ++ [jetStep 2 true 13 5 self13Rows04] = self13Rows04 ++ [self13Row05]
  congr 1
  decide +kernel
def self13Row06 : List Jet := [[(2772467/1088640),(135380243/14968800),(-205619/33264)],[(-745753/7484400),(6698939/29937600),(8920931/9979200)],[(-9571/2993760),(-130139/14968800),(3917/4989600)],[(-1/33264),(-1/11088),(-1/11088)],[0,0,0],[0,0,0],[0,0,0]]
def self13Rows06 : List (List Jet) := self13Rows05 ++ [self13Row06]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows06_correct : jetRows 2 true 13 6 = self13Rows06 := by
  rw [jetRows, self13Rows05_correct]
  change self13Rows05 ++ [jetStep 2 true 13 6 self13Rows05] = self13Rows05 ++ [self13Row06]
  congr 1
  decide +kernel
def self13Row07 : List Jet := [[(-306079709/1257379200),(-17761956967/1257379200),(-8269138879/628689600)],[(680149/3265920),(1394497/3592512),(-72317521/89812800)],[(242/297675),(1118969/69854400),(6011171/209563200)],[(-281/6985440),(281/34927200),(281/1058400)],[0,0,0],[0,0,0],[0,0,0]]
def self13Rows07 : List (List Jet) := self13Rows06 ++ [self13Row07]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows07_correct : jetRows 2 true 13 7 = self13Rows07 := by
  rw [jetRows, self13Rows06_correct]
  change self13Rows06 ++ [jetStep 2 true 13 7 self13Rows06] = self13Rows06 ++ [self13Row07]
  congr 1
  decide +kernel
def self13Row08 : List Jet := [[(-178029021367/50295168000),(14286627209/1676505600),(602187804707/16765056000)],[(-37998347/239500800),(-195589223/171072000),(-466807601/598752000)],[(6023701/1047816000),(-272197/155232000),(-18630047/349272000)],[(5419/52390800),(53153/130977000),(18503/65488500)],[(1/1330560),(1/332640),(1/221760)],[0,0,0],[0,0,0]]
def self13Rows08 : List (List Jet) := self13Rows07 ++ [self13Row08]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows08_correct : jetRows 2 true 13 8 = self13Rows08 := by
  rw [jetRows, self13Rows07_correct]
  change self13Rows07 ++ [jetStep 2 true 13 8 self13Rows07] = self13Rows07 ++ [self13Row08]
  congr 1
  decide +kernel
def self13Row09 : List Jet := [[(5892316907357/905313024000),(253230541457/21555072000),(-11406803040257/301771008000)],[(-3234483491/22632825600),(179596182679/150885504000),(61473155881/16765056000)],[(-365527643/32332608000),(-16570999/384912000),(25365127/5388768000)],[(-199/48988800),(-24103847/37721376000),(-36199277/18860688000)],[(667/502951680),(667/628689600),(-11339/1257379200)],[0,0,0],[0,0,0]]
def self13Rows09 : List (List Jet) := self13Rows08 ++ [self13Row09]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows09_correct : jetRows 2 true 13 9 = self13Rows09 := by
  rw [jetRows, self13Rows08_correct]
  change self13Rows08 ++ [jetStep 2 true 13 9 self13Rows08] = self13Rows08 ++ [self13Row09]
  congr 1
  decide +kernel
def self13Row10 : List Jet := [[(-126430497782773/27159390720000),(-217798047083093/5431878144000),(-151952413486801/9053130240000)],[(8536791194083/13579695360000),(4989561044609/6789847680000),(-23316167329843/4526565120000)],[(9789161/2263282560),(13712544851/150885504000),(147843292273/754427520000)],[(-199129033/565820640000),(-309384629/565820640000),(243754729/94303440000)],[(-310367/75442752000),(-2717711/125737920000),(-174059/5715360000)],[(-1/39916800),(-1/7983360),(-1/3991680)],[0,0,0]]
def self13Rows10 : List (List Jet) := self13Rows09 ++ [self13Row10]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows10_correct : jetRows 2 true 13 10 = self13Rows10 := by
  rw [jetRows, self13Rows09_correct]
  change self13Rows09 ++ [jetStep 2 true 13 10 self13Rows09] = self13Rows09 ++ [self13Row10]
  congr 1
  decide +kernel
def self13Row11 : List Jet := [[(-431156397138671/59750659584000),(6606315796647269/149376648960000),(911783271015733/5975065958400)],[(-7295475641317/9053130240000),(-50431121113451/9053130240000),(-276724862382713/99584432640000)],[(159800606197/4979221632000),(-208089457363/9958443264000),(-1376047517587/2766234240000)],[(277037687/395176320000),(16543786753/3556586880000),(740029591/127020960000)],[(-247921/118552896000),(135751037/4149351360000),(12370709/76839840000)],[(-793/11064936960),(-793/6147187200),(793/1844156160)],[0,0,0]]
def self13Rows11 : List (List Jet) := self13Rows10 ++ [self13Row11]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows11_correct : jetRows 2 true 13 11 = self13Rows11 := by
  rw [jetRows, self13Rows10_correct]
  change self13Rows10 ++ [jetStep 2 true 13 11 self13Rows10] = self13Rows10 ++ [self13Row11]
  congr 1
  decide +kernel
def self13Row12 : List Jet := [[(16222402507004329/512148510720000),(44951674540539917/512148510720000),(-12909856857445607/51214851072000)],[(-20167206332683/16295634432000),(155441738212267/16295634432000),(37056962338514477/896259893760000)],[(-189252674349383/1792519787520000),(-524681513018363/896259893760000),(-86490679109/1000290060000)],[(17437869121/19916886528000),(-538436546561/59750659584000),(-2848085534729/59750659584000)],[(6766768951/149376648960000),(152751637/922078080000),(-17253621463/149376648960000)],[(3839/10287648000),(10367/3969405000),(1668679/296382240000)],[(1/479001600),(1/79833600),(1/31933440)]]
def self13Rows12 : List (List Jet) := self13Rows11 ++ [self13Row12]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Rows12_correct : jetRows 2 true 13 12 = self13Rows12 := by
  rw [jetRows, self13Rows11_correct]
  change self13Rows11 ++ [jetStep 2 true 13 12 self13Rows11] = self13Rows11 ++ [self13Row12]
  congr 1
  decide +kernel
def self13Coeffs : List Jet := [[(-365026783274894507/1792519787520000),(2277220257773981221/896259893760000),(4499208936969891989/896259893760000)],[(-831659638335497/17925197875200),(-186299499378658331/896259893760000),(391702421347944059/896259893760000)],[(747549876743/754427520000),(-738388266233819/74688324480000),(-128325476758511/3394923840000)],[(103611379573/1556006760000),(75946773809/308629440000),(-37081882853651/74688324480000)],[(29343691/83357505000),(1535835221/222286680000),(11047677037/666860040000)],[(-14603/1852389000),(446801/18523890000),(453617/2058210000)],[(-2/21611205),(-2/12006225),(4/7203735)]]
set_option maxHeartbeats 4000000 in
-- Finite exact rational jet arithmetic, checked by kernel reduction.
theorem self13Coeffs_correct : widthCoefficients 2 true 13 = self13Coeffs := by
  rw [widthCoefficients,self13Rows12_correct]
  decide +kernel
end VOA.Classification.COne.OrbIcoW
