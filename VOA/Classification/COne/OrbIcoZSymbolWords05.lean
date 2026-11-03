import VOA.Classification.COne.OrbIcoZSymbolWords04

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache40 : RawSym := [(0, [[(-5254:ℚ), (-361:ℚ), (-6:ℚ)], [(145:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(5180:ℚ), (210:ℚ)], [(4:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(-7875:ℚ), (-210:ℚ)], [(30:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(6930:ℚ)], [(171:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache40_check : equalRawCheck
    (rawScale (rawFactor 4 74) wordCache6 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache6)) wordCache40 = true := by
  decide +kernel

theorem wordCache40_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 3]) = evalSym W k a (symMap wordCache40) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache6_sound W k a, wordCache6_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache40_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache41 : RawSym := [(0, [[(-373176:ℚ), (-20448:ℚ)], [(15551:ℚ), (572:ℚ)], [(-216:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(10512:ℚ), (576:ℚ)], [(-290:ℚ), (-8:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(73:ℚ), (4:ℚ)], [(-74:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(819280:ℚ)], [(-15568:ℚ)], [(-13:ℚ)], [(1:ℚ)]]),
 (6, [[(107800:ℚ)], [(-22190:ℚ)], [(116:ℚ)], [(2:ℚ)]]),
 (7, [[(4200:ℚ)], [(-1510:ℚ)], [(129:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache41_check : equalRawCheck
    (rawScale (rawFactor 5 73) wordCache2 ++
      rawScale (rawSecond 5) (rawShift 5 wordCache2)) wordCache41 = true := by
  decide +kernel

theorem wordCache41_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [5, 1, 1]) = evalSym W k a (symMap wordCache41) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache2_sound W k a, wordCache2_sound W (k - (5 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache41_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache42 : RawSym := [(0, [[(-5183:ℚ), (-357:ℚ), (-4:ℚ)], [(144:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-2555:ℚ), (-140:ℚ)], [(-38:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(10640:ℚ), (140:ℚ)], [(-64:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (7, [[(4200:ℚ)], [(170:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache42_check : equalRawCheck
    (rawScale (rawFactor 5 73) wordCache3 ++
      rawScale (rawSecond 5) (rawShift 5 wordCache3)) wordCache42 = true := by
  decide +kernel

theorem wordCache42_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [5, 2]) = evalSym W k a (symMap wordCache42) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache3_sound W k a, wordCache3_sound W (k - (5 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache42_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache43 : RawSym := [(0, [[(-5112:ℚ), (-355:ℚ)], [(143:ℚ), (5:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(72:ℚ), (5:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(-13475:ℚ)], [(98:ℚ)], [(1:ℚ)]]),
 (7, [[(-1050:ℚ)], [(169:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache43_check : equalRawCheck
    (rawScale (rawFactor 6 72) wordCache1 ++
      rawScale (rawSecond 6) (rawShift 6 wordCache1)) wordCache43 = true := by
  decide +kernel

theorem wordCache43_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [6, 1]) = evalSym W k a (symMap wordCache43) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache1_sound W k a, wordCache1_sound W (k - (6 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache43_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache44 : RawSym := [(0, [[(945378254620800:ℚ)], [(-101613313749744:ℚ)], [(4777655828364:ℚ)], [(-128345977004:ℚ)], [(2154621049:ℚ)], [(-23146256:ℚ)], [(155386:ℚ)], [(-596:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(-106521493478400:ℚ)], [(9949084739712:ℚ)], [(-398199463200:ℚ)], [(8853075392:ℚ)], [(-118083000:ℚ)], [(944888:ℚ)], [(-4200:ℚ)], [(8:ℚ)]]),
 (2, [[(0:ℚ)], [(-5178128155200:ℚ)], [(5589845772336:ℚ)], [(-425356235248:ℚ)], [(13879550692:ℚ)], [(-243326440:ℚ)], [(2406544:ℚ)], [(-12712:ℚ)], [(28:ℚ)]]),
 (3, [[(0:ℚ)], [(-283733049600:ℚ)], [(444272689728:ℚ)], [(-170367723232:ℚ)], [(10080314384:ℚ)], [(-255508120:ℚ)], [(3298232:ℚ)], [(-21448:ℚ)], [(56:ℚ)]]),
 (4, [[(0:ℚ)], [(-14378364000:ℚ)], [(27112304520:ℚ)], [(-15771723240:ℚ)], [(3175528510:ℚ)], [(-140311080:ℚ)], [(2587060:ℚ)], [(-21840:ℚ)], [(70:ℚ)]]),
 (5, [[(0:ℚ)], [(-613476864:ℚ)], [(1301981184:ℚ)], [(-944765024:ℚ)], [(291124064:ℚ)], [(-35977256:ℚ)], [(1127336:ℚ)], [(-13496:ℚ)], [(56:ℚ)]]),
 (6, [[(0:ℚ)], [(-20180160:ℚ)], [(46598832:ℚ)], [(-39030320:ℚ)], [(15278452:ℚ)], [(-2897720:ℚ)], [(235648:ℚ)], [(-4760:ℚ)], [(28:ℚ)]]),
 (7, [[(0:ℚ)], [(-449280:ℚ)], [(1106496:ℚ)], [(-1027488:ℚ)], [(471632:ℚ)], [(-115080:ℚ)], [(14504:ℚ)], [(-792:ℚ)], [(8:ℚ)]]),
 (8, [[(0:ℚ)], [(-5040:ℚ)], [(13068:ℚ)], [(-13132:ℚ)], [(6769:ℚ)], [(-1960:ℚ)], [(322:ℚ)], [(-28:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache44_check : equalRawCheck
    (rawScale (rawFactor 1 78) wordCache30 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache30)) wordCache44 = true := by
  decide +kernel

theorem wordCache44_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1, 1, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache44) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache30_sound W k a, wordCache30_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache44_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache45 : RawSym := [(0, [[(12120234033600:ℚ), (157405636800:ℚ)], [(-1147347175848:ℚ), (-12856383624:ℚ)], [(46542418622:ℚ), (437480974:ℚ)], [(-1048763569:ℚ), (-7938735:ℚ)], [(14177660:ℚ), (81025:ℚ)], [(-114982:ℚ), (-441:ℚ)], [(518:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-1024245129600:ℚ), (-13301884800:ℚ)], [(82532928528:ℚ), (899104464:ℚ)], [(-2770726524:ℚ), (-24306780:ℚ)], [(49603590:ℚ), (328530:ℚ)], [(-499470:ℚ), (-2220:ℚ)], [(2682:ℚ), (6:ℚ)], [(-6:ℚ), (0:ℚ)]]),
 (2, [[(6472660194000:ℚ), (0:ℚ)], [(-365277940020:ℚ), (-461871000:ℚ)], [(40279920338:ℚ), (486675030:ℚ)], [(-2249117906:ℚ), (-25303515:ℚ)], [(58495640:ℚ), (503955:ℚ)], [(-779660:ℚ), (-4485:ℚ)], [(5222:ℚ), (15:ℚ)], [(-14:ℚ), (0:ℚ)]]),
 (3, [[(1063998936000:ℚ), (0:ℚ)], [(-572922824880:ℚ), (-16872000:ℚ)], [(21672195832:ℚ), (25982960:ℚ)], [(-647064236:ℚ), (-9457440:ℚ)], [(21749350:ℚ), (351020:ℚ)], [(-431270:ℚ), (-4560:ℚ)], [(4018:ℚ), (20:ℚ)], [(-14:ℚ), (0:ℚ)]]),
 (4, [[(107837730000:ℚ), (0:ℚ)], [(-92462976900:ℚ), (-513000:ℚ)], [(20128646790:ℚ), (954090:ℚ)], [(-424520460:ℚ), (-538005:ℚ)], [(-2096640:ℚ), (99255:ℚ)], [(105840:ℚ), (-2355:ℚ)], [(-630:ℚ), (15:ℚ)]]),
 (5, [[(7668460800:ℚ), (0:ℚ)], [(-8388047808:ℚ), (-10944:ℚ)], [(2959142032:ℚ), (22944:ℚ)], [(-345545284:ℚ), (-16260:ℚ)], [(1856050:ℚ), (4770:ℚ)], [(185318:ℚ), (-516:ℚ)], [(-3122:ℚ), (6:ℚ)], [(14:ℚ), (0:ℚ)]]),
 (6, [[(378378000:ℚ), (0:ℚ)], [(-484548540:ℚ), (-120:ℚ)], [(222336758:ℚ), (274:ℚ)], [(-43263934:ℚ), (-225:ℚ)], [(2907800:ℚ), (85:ℚ)], [(33740:ℚ), (-15:ℚ)], [(-1918:ℚ), (1:ℚ)], [(14:ℚ), (0:ℚ)]]),
 (7, [[(11793600:ℚ)], [(-16914960:ℚ)], [(9226728:ℚ)], [(-2382996:ℚ)], [(284130:ℚ)], [(-10290:ℚ)], [(-378:ℚ)], [(6:ℚ)]]),
 (8, [[(176400:ℚ)], [(-275940:ℚ)], [(170612:ℚ)], [(-53171:ℚ)], [(8660:ℚ)], [(-650:ℚ)], [(8:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache45_check : equalRawCheck
    (rawScale (rawFactor 2 77) wordCache19 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache19)) wordCache45 = true := by
  decide +kernel

theorem wordCache45_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 1, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache45) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache19_sound W k a, wordCache19_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache45_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache46 : RawSym := [(0, [[(159476763600:ℚ), (4197483648:ℚ), (27615024:ℚ)], [(-12998294898:ℚ), (-286870448:ℚ), (-1523950:ℚ)], [(441370049:ℚ), (7841220:ℚ), (31535:ℚ)], [(-7992020:ℚ), (-107150:ℚ), (-290:ℚ)], [(81390:ℚ), (732:ℚ), (1:ℚ)], [(-442:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-8984606400:ℚ), (-236477952:ℚ), (-1555776:ℚ)], [(605754552:ℚ), (12831040:ℚ), (63944:ℚ)], [(-16334164:ℚ), (-261040:ℚ), (-876:ℚ)], [(220196:ℚ), (2360:ℚ), (4:ℚ)], [(-1484:ℚ), (-8:ℚ), (0:ℚ)], [(4:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(165965646000:ℚ), (2155398000:ℚ), (0:ℚ)], [(-6513616480:ℚ), (-59095964:ℚ), (-32412:ℚ)], [(176195716:ℚ), (4149238:ℚ), (33294:ℚ)], [(-5723200:ℚ), (-155826:ℚ), (-888:ℚ)], [(116680:ℚ), (2162:ℚ), (6:ℚ)], [(-1120:ℚ), (-10:ℚ), (0:ℚ)], [(4:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(18188016000:ℚ), (236208000:ℚ), (0:ℚ)], [(-9541584080:ℚ), (-120894624:ℚ), (-592:ℚ)], [(218956896:ℚ), (1343712:ℚ), (896:ℚ)], [(2655644:ℚ), (26424:ℚ), (-308:ℚ)], [(-122492:ℚ), (-312:ℚ), (4:ℚ)], [(1236:ℚ), (0:ℚ), (0:ℚ)], [(-4:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(40646529000:ℚ), (14364000:ℚ), (0:ℚ)], [(-673781220:ℚ), (-11941032:ℚ), (-6:ℚ)], [(146821950:ℚ), (2362432:ℚ), (11:ℚ)], [(-1228440:ℚ), (11078:ℚ), (-6:ℚ)], [(-101660:ℚ), (-1288:ℚ), (1:ℚ)], [(1980:ℚ), (10:ℚ), (0:ℚ)], [(-10:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(8474632320:ℚ), (510720:ℚ)], [(-1983395008:ℚ), (-545408:ℚ)], [(-35142696:ℚ), (182800:ℚ)], [(314980:ℚ), (-18120:ℚ)], [(2860:ℚ), (-400:ℚ)], [(348:ℚ), (8:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (6, [[(833078400:ℚ), (8400:ℚ)], [(-347888240:ℚ), (-10540:ℚ)], [(29198932:ℚ), (4662:ℚ)], [(1479136:ℚ), (-838:ℚ)], [(-11384:ℚ), (42:ℚ)], [(-464:ℚ), (2:ℚ)], [(4:ℚ), (0:ℚ)]]),
 (7, [[(43243200:ℚ)], [(-24675120:ℚ)], [(4182096:ℚ)], [(-114860:ℚ)], [(-15700:ℚ)], [(-100:ℚ)], [(4:ℚ)]]),
 (8, [[(970200:ℚ)], [(-679770:ℚ)], [(164201:ℚ)], [(-13876:ℚ)], [(-162:ℚ)], [(46:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache46_check : equalRawCheck
    (rawScale (rawFactor 2 77) wordCache20 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache20)) wordCache46 = true := by
  decide +kernel

theorem wordCache46_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache46) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache20_sound W k a, wordCache20_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache46_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache47 : RawSym := [(0, [[(2155091400:ℚ), (86244552:ℚ), (1150200:ℚ), (5112:ℚ)], [(-146529777:ℚ), (-4712953:ℚ), (-47511:ℚ), (-143:ℚ)], [(3984328:ℚ), (96557:ℚ), (654:ℚ), (1:ℚ)], [(-54158:ℚ), (-879:ℚ), (-3:ℚ), (0:ℚ)], [(368:ℚ), (3:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(-60706800:ℚ), (-2429424:ℚ), (-32400:ℚ), (-144:ℚ)], [(3272574:ℚ), (98542:ℚ), (882:ℚ), (2:ℚ)], [(-66142:ℚ), (-1332:ℚ), (-6:ℚ), (0:ℚ)], [(594:ℚ), (6:ℚ), (0:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(3275637750:ℚ), (86215920:ℚ), (567210:ℚ), (0:ℚ)], [(-82184970:ℚ), (-1034099:ℚ), (546:ℚ), (-1:ℚ)], [(-1051936:ℚ), (-35293:ℚ), (-108:ℚ), (1:ℚ)], [(52072:ℚ), (675:ℚ), (0:ℚ), (0:ℚ)], [(-566:ℚ), (-3:ℚ), (0:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(179487000:ℚ), (4724160:ℚ), (31080:ℚ)], [(-91764960:ℚ), (-2353104:ℚ), (-15072:ℚ)], [(901374:ℚ), (-7248:ℚ), (-246:ℚ)], [(56970:ℚ), (1404:ℚ), (6:ℚ)], [(-1158:ℚ), (-12:ℚ), (0:ℚ)], [(6:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(1524426750:ℚ), (19846260:ℚ), (630:ℚ)], [(26473860:ℚ), (561261:ℚ), (-507:ℚ)], [(-830544:ℚ), (4455:ℚ), (90:ℚ)], [(-5796:ℚ), (27:ℚ), (3:ℚ)], [(114:ℚ), (-3:ℚ), (0:ℚ)]]),
 (5, [[(162217440:ℚ), (2106720:ℚ)], [(-35245056:ℚ), (-430368:ℚ)], [(-1408854:ℚ), (-23886:ℚ)], [(18342:ℚ), (-72:ℚ)], [(534:ℚ), (6:ℚ)], [(-6:ℚ), (0:ℚ)]]),
 (6, [[(220380930:ℚ), (69300:ℚ)], [(11891418:ℚ), (-27105:ℚ)], [(281792:ℚ), (1689:ℚ)], [(5864:ℚ), (177:ℚ)], [(-2:ℚ), (3:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (7, [[(33513480:ℚ)], [(-2961072:ℚ)], [(-383910:ℚ)], [(-9170:ℚ)], [(30:ℚ)], [(2:ℚ)]]),
 (8, [[(1503810:ℚ)], [(-328419:ℚ)], [(-2456:ℚ)], [(2018:ℚ)], [(86:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache47_check : equalRawCheck
    (rawScale (rawFactor 2 77) wordCache21 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache21)) wordCache47 = true := by
  decide +kernel

theorem wordCache47_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 2, 1, 1]) = evalSym W k a (symMap wordCache47) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache21_sound W k a, wordCache21_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache47_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
