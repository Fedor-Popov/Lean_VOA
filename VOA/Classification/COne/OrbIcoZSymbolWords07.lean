import VOA.Classification.COne.OrbIcoZSymbolWords06

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache56 : RawSym := [(0, [[(388725:ℚ), (26349:ℚ), (507:ℚ), (3:ℚ)], [(-15983:ℚ), (-726:ℚ), (-7:ℚ), (0:ℚ)], [(219:ℚ), (5:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(383250:ℚ), (20580:ℚ), (210:ℚ)], [(590:ℚ), (308:ℚ), (6:ℚ)], [(-226:ℚ), (-8:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(693000:ℚ), (19425:ℚ), (105:ℚ)], [(-6240:ℚ), (146:ℚ), (1:ℚ)], [(-40:ℚ), (1:ℚ), (0:ℚ)]]),
 (6, [[(501270:ℚ), (6510:ℚ)], [(14434:ℚ), (272:ℚ)], [(-118:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (8, [[(94395:ℚ)], [(7199:ℚ)], [(165:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache56_check : equalRawCheck
    (rawScale (rawFactor 4 75) wordCache9 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache9)) wordCache56 = true := by
  decide +kernel

theorem wordCache56_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 2, 2]) = evalSym W k a (symMap wordCache56) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache9_sound W k a, wordCache9_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache56_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache57 : RawSym := [(0, [[(383400:ℚ), (25986:ℚ), (426:ℚ)], [(-15837:ℚ), (-721:ℚ), (-6:ℚ)], [(218:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-5400:ℚ), (-366:ℚ), (-6:ℚ)], [(147:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-388500:ℚ), (-15540:ℚ)], [(4880:ℚ), (-12:ℚ)], [(79:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(582750:ℚ), (15120:ℚ)], [(-4920:ℚ), (141:ℚ)], [(-38:ℚ), (1:ℚ)]]),
 (5, [[(31920:ℚ), (840:ℚ)], [(-8096:ℚ), (-202:ℚ)], [(25:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(-540540:ℚ)], [(-6408:ℚ)], [(93:ℚ)], [(1:ℚ)]]),
 (8, [[(-48510:ℚ)], [(5733:ℚ)], [(164:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache57_check : equalRawCheck
    (rawScale (rawFactor 4 75) wordCache10 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache10)) wordCache57 = true := by
  decide +kernel

theorem wordCache57_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 3, 1]) = evalSym W k a (symMap wordCache57) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache10_sound W k a, wordCache10_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache57_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache58 : RawSym := [(0, [[(5325:ℚ), (438:ℚ), (9:ℚ)], [(-146:ℚ), (-6:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(15750:ℚ), (630:ℚ)], [(-60:ℚ), (6:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (8, [[(10605:ℚ)], [(206:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache58_check : equalRawCheck
    (rawScale (rawFactor 4 75) wordCache11 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache11)) wordCache58 = true := by
  decide +kernel

theorem wordCache58_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 4]) = evalSym W k a (symMap wordCache58) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache11_sound W k a, wordCache11_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache58_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache59 : RawSym := [(0, [[(27615024:ℚ), (1492704:ℚ)], [(-1523950:ℚ), (-62204:ℚ)], [(31535:ℚ), (864:ℚ)], [(-290:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-1166832:ℚ), (-63072:ℚ)], [(47958:ℚ), (1740:ℚ)], [(-657:ℚ), (-12:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(-16206:ℚ), (-876:ℚ)], [(16647:ℚ), (888:ℚ)], [(-444:ℚ), (-12:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(-148:ℚ), (-8:ℚ)], [(224:ℚ), (12:ℚ)], [(-77:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(-63903840:ℚ)], [(2033584:ℚ)], [(-14554:ℚ)], [(-91:ℚ)], [(1:ℚ)]]),
 (6, [[(-12612600:ℚ)], [(2757930:ℚ)], [(-46857:ℚ)], [(-60:ℚ)], [(3:ℚ)]]),
 (7, [[(-982800:ℚ)], [(365940:ℚ)], [(-34716:ℚ)], [(153:ℚ)], [(3:ℚ)]]),
 (8, [[(-29400:ℚ)], [(14770:ℚ)], [(-2413:ℚ)], [(122:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache59_check : equalRawCheck
    (rawScale (rawFactor 5 74) wordCache4 ++
      rawScale (rawSecond 5) (rawShift 5 wordCache4)) wordCache59 = true := by
  decide +kernel

theorem wordCache59_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [5, 1, 1, 1]) = evalSym W k a (symMap wordCache59) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache4_sound W k a, wordCache4_sound W (k - (5 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache59_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache60 : RawSym := [(0, [[(378288:ℚ), (25702:ℚ), (284:ℚ)], [(-15694:ℚ), (-717:ℚ), (-4:ℚ)], [(217:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-5328:ℚ), (-362:ℚ), (-4:ℚ)], [(146:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(189070:ℚ), (10220:ℚ)], [(257:ℚ), (152:ℚ)], [(-112:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (3, [[(5180:ℚ), (280:ℚ)], [(-2512:ℚ), (-132:ℚ)], [(-41:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(-819280:ℚ), (-10640:ℚ)], [(15568:ℚ), (64:ℚ)], [(13:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(-53900:ℚ), (-700:ℚ)], [(11095:ℚ), (135:ℚ)], [(-58:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (7, [[(-327600:ℚ)], [(-9060:ℚ)], [(92:ℚ)], [(1:ℚ)]]),
 (8, [[(-29400:ℚ)], [(3010:ℚ)], [(163:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache60_check : equalRawCheck
    (rawScale (rawFactor 5 74) wordCache5 ++
      rawScale (rawSecond 5) (rawShift 5 wordCache5)) wordCache60 = true := by
  decide +kernel

theorem wordCache60_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [5, 2, 1]) = evalSym W k a (symMap wordCache60) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache5_sound W k a, wordCache5_sound W (k - (5 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache60_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache61 : RawSym := [(0, [[(5254:ℚ), (432:ℚ), (8:ℚ)], [(-145:ℚ), (-6:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-5180:ℚ), (-280:ℚ)], [(-4:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(-10640:ℚ), (-280:ℚ)], [(64:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (8, [[(9100:ℚ)], [(205:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache61_check : equalRawCheck
    (rawScale (rawFactor 5 74) wordCache6 ++
      rawScale (rawSecond 5) (rawShift 5 wordCache6)) wordCache61 = true := by
  decide +kernel

theorem wordCache61_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [5, 3]) = evalSym W k a (symMap wordCache61) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache6_sound W k a, wordCache6_sound W (k - (5 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache61_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache62 : RawSym := [(0, [[(-74684882115043200:ℚ)], [(8972830040850576:ℚ)], [(-479048124190500:ℚ)], [(14916988011680:ℚ)], [(-298561039875:ℚ)], [(3983175273:ℚ)], [(-35421750:ℚ)], [(202470:ℚ)], [(-675:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(9467097732892800:ℚ)], [(-1004061586405104:ℚ)], [(46582697624076:ℚ)], [(-1234791471564:ℚ)], [(20454336441:ℚ)], [(-216820296:ℚ)], [(1436274:ℚ)], [(-5436:ℚ)], [(9:ℚ)]]),
 (2, [[(0:ℚ)], [(525949874049600:ℚ)], [(-574426213932528:ℚ)], [(50390985030336:ℚ)], [(-1956652379892:ℚ)], [(42560150724:ℚ)], [(-557284392:ℚ)], [(4385304:ℚ)], [(-19188:ℚ)], [(36:ℚ)]]),
 (3, [[(0:ℚ)], [(33622366377600:ℚ)], [(-53071913307168:ℚ)], [(20854984237584:ℚ)], [(-1450068839352:ℚ)], [(45398183796:ℚ)], [(-774102672:ℚ)], [(7488936:ℚ)], [(-38808:ℚ)], [(84:ℚ)]]),
 (4, [[(0:ℚ)], [(2044603360800:ℚ)], [(-3881250757944:ℚ)], [(2291541192864:ℚ)], [(-479949255954:ℚ)], [(25668186894:ℚ)], [(-620439876:ℚ)], [(7762356:ℚ)], [(-49266:ℚ)], [(126:ℚ)]]),
 (5, [[(0:ℚ)], [(109045512576:ℚ)], [(-232807478400:ℚ)], [(170861440680:ℚ)], [(-53873023680:ℚ)], [(7049986398:ℚ)], [(-281332800:ℚ)], [(4935420:ℚ)], [(-40320:ℚ)], [(126:ℚ)]]),
 (6, [[(0:ℚ)], [(4782697920:ℚ)], [(-11104463664:ℚ)], [(9389982336:ℚ)], [(-3738084084:ℚ)], [(732594996:ℚ)], [(-64541736:ℚ)], [(1835064:ℚ)], [(-20916:ℚ)], [(84:ℚ)]]),
 (7, [[(0:ℚ)], [(159719040:ℚ)], [(-395381088:ℚ)], [(370251216:ℚ)], [(-172288872:ℚ)], [(43033284:ℚ)], [(-5674032:ℚ)], [(346824:ℚ)], [(-6408:ℚ)], [(36:ℚ)]]),
 (8, [[(0:ℚ)], [(3583440:ℚ)], [(-9336708:ℚ)], [(9454464:ℚ)], [(-4930947:ℚ)], [(1454481:ℚ)], [(-246582:ℚ)], [(22806:ℚ)], [(-963:ℚ)], [(9:ℚ)]]),
 (9, [[(0:ℚ)], [(40320:ℚ)], [(-109584:ℚ)], [(118124:ℚ)], [(-67284:ℚ)], [(22449:ℚ)], [(-4536:ℚ)], [(546:ℚ)], [(-36:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache62_check : equalRawCheck
    (rawScale (rawFactor 1 79) wordCache44 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache44)) wordCache62 = true := by
  decide +kernel

theorem wordCache62_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1, 1, 1, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache62) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache44_sound W k a, wordCache44_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache62_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache63 : RawSym := [(0, [[(-945378254620800:ℚ), (-12120234033600:ℚ)], [(101613313749744:ℚ), (1147347175848:ℚ)], [(-4777655828364:ℚ), (-46542418622:ℚ)], [(128345977004:ℚ), (1048763569:ℚ)], [(-2154621049:ℚ), (-14177660:ℚ)], [(23146256:ℚ), (114982:ℚ)], [(-155386:ℚ), (-518:ℚ)], [(596:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(93206306793600:ℚ), (1194952651200:ℚ)], [(-8705449147248:ℚ), (-96288416616:ℚ)], [(348424530300:ℚ), (3232514278:ℚ)], [(-7746440968:ℚ), (-57870855:ℚ)], [(103322625:ℚ), (582715:ℚ)], [(-826777:ℚ), (-3129:ℚ)], [(3675:ℚ), (7:ℚ)], [(-7:ℚ), (0:ℚ)]]),
 (2, [[(-511340155326000:ℚ), (0:ℚ)], [(36403652278980:ℚ), (49789693800:ℚ)], [(-4707279892484:ℚ), (-53110187634:ℚ)], [(306672953923:ℚ), (3409063959:ℚ)], [(-9780354850:ℚ), (-89751270:ℚ)], [(171380860:ℚ), (1189020:ℚ)], [(-1702246:ℚ), (-7896:ℚ)], [(9037:ℚ), (21:ℚ)], [(-20:ℚ), (0:ℚ)]]),
 (3, [[(-98065235268000:ℚ), (0:ℚ)], [(54103314502440:ℚ), (2273502000:ℚ)], [(-2756067001996:ℚ), (-3530729860:ℚ)], [(119535351082:ℚ), (1319860220:ℚ)], [(-4816971887:ℚ), (-63850465:ℚ)], [(117534655:ℚ), (1228745:ℚ)], [(-1553489:ℚ), (-10675:ℚ)], [(10423:ℚ), (35:ℚ)], [(-28:ℚ), (0:ℚ)]]),
 (4, [[(-11926852938000:ℚ), (0:ℚ)], [(10380198438540:ℚ), (92169000:ℚ)], [(-2360995394436:ℚ), (-172615170:ℚ)], [(78227080365:ℚ), (98887775:ℚ)], [(-986093066:ℚ), (-19088160:ℚ)], [(13028190:ℚ), (654710:ℚ)], [(-294644:ℚ), (-8190:ℚ)], [(3465:ℚ), (35:ℚ)], [(-14:ℚ), (0:ℚ)]]),
 (5, [[(-1060164705600:ℚ), (0:ℚ)], [(1173180968064:ℚ), (2949408:ℚ)], [(-424021480204:ℚ), (-6221712:ℚ)], [(53125046324:ℚ), (4462374:ℚ)], [(-915217709:ℚ), (-1342425:ℚ)], [(-15704269:ℚ), (155757:ℚ)], [(546259:ℚ), (-3423:ℚ)], [(-4879:ℚ), (21:ℚ)], [(14:ℚ), (0:ℚ)]]),
 (6, [[(-69747678000:ℚ), (0:ℚ)], [(90204671340:ℚ), (64680:ℚ)], [(-42122405948:ℚ), (-148526:ℚ)], [(8500234925:ℚ), (123193:ℚ)], [(-639484258:ℚ), (-47390:ℚ)], [(1045520:ℚ), (8680:ℚ)], [(393218:ℚ), (-644:ℚ)], [(-6265:ℚ), (7:ℚ)], [(28:ℚ), (0:ℚ)]]),
 (7, [[(-3260930400:ℚ), (0:ℚ)], [(4718320200:ℚ), (720:ℚ)], [(-2610530964:ℚ), (-1764:ℚ)], [(691320378:ℚ), (1624:ℚ)], [(-86961385:ℚ), (-735:ℚ)], [(3854025:ℚ), (175:ℚ)], [(66689:ℚ), (-21:ℚ)], [(-2883:ℚ), (1:ℚ)], [(20:ℚ), (0:ℚ)]]),
 (8, [[(-97549200:ℚ)], [(153829620:ℚ)], [(-96280016:ℚ)], [(30597847:ℚ)], [(-5161177:ℚ)], [(420070:ℚ)], [(-8974:ℚ)], [(-497:ℚ)], [(7:ℚ)]]),
 (9, [[(-1411200:ℚ)], [(2383920:ℚ)], [(-1640836:ℚ)], [(595980:ℚ)], [(-122451:ℚ)], [(13860:ℚ)], [(-714:ℚ)], [(0:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache63_check : equalRawCheck
    (rawScale (rawFactor 2 78) wordCache30 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache30)) wordCache63 = true := by
  decide +kernel

theorem wordCache63_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 1, 1, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache63) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache30_sound W k a, wordCache30_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache63_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
