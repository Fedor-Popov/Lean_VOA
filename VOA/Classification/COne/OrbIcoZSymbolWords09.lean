import VOA.Classification.COne.OrbIcoZSymbolWords08

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache72 : RawSym := [(0, [[(-29128176:ℚ), (-1948382:ℚ), (-41890:ℚ), (-284:ℚ)], [(1586726:ℚ), (80053:ℚ), (1158:ℚ), (4:ℚ)], [(-32403:ℚ), (-1096:ℚ), (-8:ℚ), (0:ℚ)], [(294:ℚ), (5:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(410256:ℚ), (27442:ℚ), (590:ℚ), (4:ℚ)], [(-16570:ℚ), (-741:ℚ), (-8:ℚ), (0:ℚ)], [(223:ℚ), (5:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-14558390:ℚ), (-771610:ℚ), (-10220:ℚ)], [(169281:ℚ), (-1256:ℚ), (-152:ℚ)], [(8881:ℚ), (454:ℚ), (4:ℚ)], [(-189:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(59430140:ℚ), (2330580:ℚ), (20440:ℚ)], [(-1329916:ℚ), (-19018:ℚ), (148:ℚ)], [(-1761:ℚ), (-308:ℚ), (0:ℚ)], [(194:ℚ), (2:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(2425500:ℚ), (95340:ℚ), (840:ℚ)], [(-837690:ℚ), (-31678:ℚ), (-268:ℚ)], [(9238:ℚ), (-52:ℚ), (-4:ℚ)], [(170:ℚ), (6:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(26216960:ℚ), (680960:ℚ)], [(508368:ℚ), (22048:ℚ)], [(-15028:ℚ), (-104:ℚ)], [(-102:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (6, [[(-26443340:ℚ), (-316330:ℚ)], [(-384692:ℚ), (-12779:ℚ)], [(-939:ℚ), (-328:ℚ)], [(58:ℚ), (-3:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(-2194920:ℚ), (-28140:ℚ)], [(329844:ℚ), (3868:ℚ)], [(6350:ℚ), (131:ℚ)], [(-53:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-10744790:ℚ)], [(-548367:ℚ)], [(-4451:ℚ)], [(87:ℚ)], [(1:ℚ)]]),
 (9, [[(-1088080:ℚ)], [(66706:ℚ)], [(7335:ℚ)], [(158:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache72_check : equalRawCheck
    (rawScale (rawFactor 3 77) wordCache24 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache24)) wordCache72 = true := by
  decide +kernel

theorem wordCache72_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 3, 2, 1]) = evalSym W k a (symMap wordCache72) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache24_sound W k a, wordCache24_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache72_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache73 : RawSym := [(0, [[(-404558:ℚ), (-32838:ℚ), (-888:ℚ), (-8:ℚ)], [(16419:ℚ), (888:ℚ), (12:ℚ), (0:ℚ)], [(-222:ℚ), (-6:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(1196580:ℚ), (63420:ℚ), (840:ℚ)], [(-14616:ℚ), (66:ℚ), (12:ℚ)], [(-243:ℚ), (-12:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-1083390:ℚ), (-28140:ℚ)], [(-17577:ℚ), (-822:ℚ)], [(180:ℚ), (-6:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (9, [[(300160:ℚ)], [(13458:ℚ)], [(201:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache73_check : equalRawCheck
    (rawScale (rawFactor 3 77) wordCache25 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache25)) wordCache73 = true := by
  decide +kernel

theorem wordCache73_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 3, 3]) = evalSym W k a (symMap wordCache73) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache25_sound W k a, wordCache25_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache73_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache74 : RawSym := [(0, [[(-157405636800:ℚ), (-6213380400:ℚ)], [(12856383624:ℚ), (425733822:ℚ)], [(-437480974:ℚ), (-11667225:ℚ)], [(7938735:ℚ), (159855:ℚ)], [(-81025:ℚ), (-1095:ℚ)], [(441:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(11084904000:ℚ), (437562000:ℚ)], [(-749253720:ℚ), (-23818410:ℚ)], [(20255650:ℚ), (486165:ℚ)], [(-273775:ℚ), (-4410:ℚ)], [(1850:ℚ), (15:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(307914000:ℚ), (12154500:ℚ)], [(-324450020:ℚ), (-12647310:ℚ)], [(16869010:ℚ), (499470:ℚ)], [(-335970:ℚ), (-6690:ℚ)], [(2990:ℚ), (30:ℚ)], [(-10:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(8436000:ℚ), (333000:ℚ)], [(-12991480:ℚ), (-508440:ℚ)], [(4728720:ℚ), (179970:ℚ)], [(-175510:ℚ), (-4560:ℚ)], [(2280:ℚ), (30:ℚ)], [(-10:ℚ), (0:ℚ)]]),
 (4, [[(-283972689000:ℚ), (0:ℚ)], [(15741677970:ℚ), (6750:ℚ)], [(-303880131:ℚ), (-12465:ℚ)], [(1840085:ℚ), (6915:ℚ)], [(-14225:ℚ), (-1215:ℚ)], [(505:ℚ), (15:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (5, [[(-75726050400:ℚ), (0:ℚ)], [(22119568944:ℚ), (72:ℚ)], [(-835459954:ℚ), (-150:ℚ)], [(9543635:ℚ), (105:ℚ)], [(20730:ℚ), (-30:ℚ)], [(-959:ℚ), (3:ℚ)], [(4:ℚ), (0:ℚ)]]),
 (6, [[(-9963954000:ℚ)], [(4772155500:ℚ)], [(-629230790:ℚ)], [(14961720:ℚ)], [(-51380:ℚ)], [(-1380:ℚ)], [(10:ℚ)]]),
 (7, [[(-776412000:ℚ)], [(491175000:ℚ)], [(-104628120:ℚ)], [(7978870:ℚ)], [(-94690:ℚ)], [(-670:ℚ)], [(10:ℚ)]]),
 (8, [[(-34839000:ℚ)], [(26570250:ℚ)], [(-7502765:ℚ)], [(932530:ℚ)], [(-43440:ℚ)], [(20:ℚ)], [(5:ℚ)]]),
 (9, [[(-705600:ℚ)], [(617400:ℚ)], [(-211406:ℚ)], [(35205:ℚ)], [(-2795:ℚ)], [(75:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache74_check : equalRawCheck
    (rawScale (rawFactor 4 76) wordCache12 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache12)) wordCache74 = true := by
  decide +kernel

theorem wordCache74_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache74) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache12_sound W k a, wordCache12_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache74_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache75 : RawSym := [(0, [[(-2098741824:ℚ), (-111206448:ℚ), (-1119528:ℚ)], [(143435224:ℚ), (6126902:ℚ), (46653:ℚ)], [(-3920610:ℚ), (-126572:ℚ), (-648:ℚ)], [(53575:ℚ), (1162:ℚ), (3:ℚ)], [(-366:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(88679232:ℚ), (4698864:ℚ), (47304:ℚ)], [(-4811640:ℚ), (-192702:ℚ), (-1305:ℚ)], [(97890:ℚ), (2634:ℚ), (9:ℚ)], [(-885:ℚ), (-12:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-1077699000:ℚ), (-42540750:ℚ), (0:ℚ)], [(28316326:ℚ), (574647:ℚ), (657:ℚ)], [(-793241:ℚ), (-41061:ℚ), (-666:ℚ)], [(27522:ℚ), (1221:ℚ), (9:ℚ)], [(-409:ℚ), (-9:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-88578000:ℚ), (-3496500:ℚ), (0:ℚ)], [(45312988:ℚ), (1742816:ℚ), (6:ℚ)], [(-469548:ℚ), (4165:ℚ), (-9:ℚ)], [(-22061:ℚ), (-734:ℚ), (3:ℚ)], [(423:ℚ), (5:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-3598182000:ℚ), (-46226250:ℚ)], [(156743460:ℚ), (1496400:ℚ)], [(-2486436:ℚ), (-28384:ℚ)], [(-5984:ℚ), (-528:ℚ)], [(564:ℚ), (10:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (5, [[(-575198400:ℚ), (-7376040:ℚ)], [(160784704:ℚ), (1968594:ℚ)], [(-4333700:ℚ), (-30930:ℚ)], [(20160:ℚ), (-78:ℚ)], [(440:ℚ), (6:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (6, [[(-1582250670:ℚ), (-485100:ℚ)], [(12521691:ℚ), (219975:ℚ)], [(-920161:ℚ), (-24951:ℚ)], [(19079:ℚ), (57:ℚ)], [(79:ℚ), (3:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (7, [[(-362014380:ℚ), (-12600:ℚ)], [(54895284:ℚ), (7650:ℚ)], [(1071093:ℚ), (-1501:ℚ)], [(-26906:ℚ), (90:ℚ)], [(-93:ℚ), (1:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (8, [[(-32400270:ℚ)], [(9085041:ℚ)], [(-472182:ℚ)], [(-24564:ℚ)], [(132:ℚ)], [(3:ℚ)]]),
 (9, [[(-1093680:ℚ)], [(429534:ℚ)], [(-48835:ℚ)], [(545:ℚ)], [(115:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache75_check : equalRawCheck
    (rawScale (rawFactor 4 76) wordCache13 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache13)) wordCache75 = true := by
  decide +kernel

theorem wordCache75_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 2, 1, 1, 1]) = evalSym W k a (symMap wordCache75) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache13_sound W k a, wordCache13_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache75_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache76 : RawSym := [(0, [[(-28749888:ℚ), (-1922680:ℚ), (-36494:ℚ), (-213:ℚ)], [(1571032:ℚ), (79336:ℚ), (1011:ℚ), (3:ℚ)], [(-32186:ℚ), (-1091:ℚ), (-7:ℚ), (0:ℚ)], [(293:ℚ), (5:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(404928:ℚ), (27080:ℚ), (514:ℚ), (3:ℚ)], [(-16424:ℚ), (-736:ℚ), (-7:ℚ), (0:ℚ)], [(222:ℚ), (5:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-28738640:ℚ), (-1522780:ℚ), (-15330:ℚ)], [(339076:ℚ), (-2208:ℚ), (-228:ℚ)], [(17538:ℚ), (900:ℚ), (6:ℚ)], [(-376:ℚ), (-8:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-787360:ℚ), (-41720:ℚ), (-420:ℚ)], [(392184:ℚ), (20228:ℚ), (198:ℚ)], [(1208:ℚ), (332:ℚ), (6:ℚ)], [(-234:ℚ), (-8:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-53266500:ℚ), (-1472625:ℚ), (-7875:ℚ)], [(1177395:ℚ), (8535:ℚ), (30:ℚ)], [(-3154:ℚ), (73:ℚ), (1:ℚ)], [(-41:ℚ), (1:ℚ), (0:ℚ)]]),
 (5, [[(-2840880:ℚ), (-78540:ℚ), (-420:ℚ)], [(735136:ℚ), (19043:ℚ), (101:ℚ)], [(-6065:ℚ), (144:ℚ), (1:ℚ)], [(-41:ℚ), (1:ℚ), (0:ℚ)]]),
 (6, [[(-39099060:ℚ), (-501270:ℚ)], [(-624582:ℚ), (-14434:ℚ)], [(23638:ℚ), (118:ℚ)], [(38:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (7, [[(-3046680:ℚ), (-39060:ℚ)], [(419544:ℚ), (4878:ℚ)], [(15402:ℚ), (260:ℚ)], [(-104:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (8, [[(-7457205:ℚ)], [(-474326:ℚ)], [(-5836:ℚ)], [(86:ℚ)], [(1:ℚ)]]),
 (9, [[(-755160:ℚ)], [(36803:ℚ)], [(5879:ℚ)], [(157:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache76_check : equalRawCheck
    (rawScale (rawFactor 4 76) wordCache14 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache14)) wordCache76 = true := by
  decide +kernel

theorem wordCache76_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 2, 2, 1]) = evalSym W k a (symMap wordCache76) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache14_sound W k a, wordCache14_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache76_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache77 : RawSym := [(0, [[(-28361376:ℚ), (-1896552:ℚ), (-30672:ℚ)], [(1555052:ℚ), (78613:ℚ), (858:ℚ)], [(-31967:ℚ), (-1086:ℚ), (-6:ℚ)], [(292:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(798912:ℚ), (53424:ℚ), (864:ℚ)], [(-32552:ℚ), (-1462:ℚ), (-12:ℚ)], [(442:ℚ), (10:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5548:ℚ), (371:ℚ), (6:ℚ)], [(-5697:ℚ), (-376:ℚ), (-6:ℚ)], [(150:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(29526000:ℚ), (1165500:ℚ)], [(-759380:ℚ), (-14640:ℚ)], [(-1124:ℚ), (-237:ℚ)], [(155:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(-43690500:ℚ), (-1102500:ℚ)], [(553215:ℚ), (-11100:ℚ)], [(2641:ℚ), (44:ℚ)], [(45:ℚ), (4:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(-4851840:ℚ), (-125160:ℚ)], [(1273456:ℚ), (30950:ℚ)], [(-14776:ℚ), (89:ℚ)], [(-91:ℚ), (-1:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (6, [[(-161700:ℚ), (-4200:ℚ)], [(73325:ℚ), (1850:ℚ)], [(-8317:ℚ), (-192:ℚ)], [(19:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(42702660:ℚ)], [(-34308:ℚ)], [(-13755:ℚ)], [(14:ℚ)], [(1:ℚ)]]),
 (8, [[(7664580:ℚ)], [(-1002834:ℚ)], [(-14446:ℚ)], [(170:ℚ)], [(2:ℚ)]]),
 (9, [[(388080:ℚ)], [(-94374:ℚ)], [(4421:ℚ)], [(156:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache77_check : equalRawCheck
    (rawScale (rawFactor 4 76) wordCache15 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache15)) wordCache77 = true := by
  decide +kernel

theorem wordCache77_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 3, 1, 1]) = evalSym W k a (symMap wordCache77) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache15_sound W k a, wordCache15_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache77_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache78 : RawSym := [(0, [[(-393908:ℚ), (-31889:ℚ), (-797:ℚ), (-6:ℚ)], [(16127:ℚ), (875:ℚ), (11:ℚ), (0:ℚ)], [(-220:ℚ), (-6:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-194180:ℚ), (-12985:ℚ), (-210:ℚ)], [(-333:ℚ), (-196:ℚ), (-6:ℚ)], [(114:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(393680:ℚ), (20860:ℚ), (210:ℚ)], [(-4876:ℚ), (18:ℚ), (3:ℚ)], [(-80:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-606375:ℚ), (-23835:ℚ), (-210:ℚ)], [(10185:ℚ), (88:ℚ), (-2:ℚ)], [(47:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(170240:ℚ), (6720:ℚ)], [(5512:ℚ), (306:ℚ)], [(-26:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(-250635:ℚ), (-6510:ℚ)], [(-7217:ℚ), (-272:ℚ)], [(59:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(540540:ℚ), (6930:ℚ)], [(6408:ℚ), (171:ℚ)], [(-93:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (9, [[(194040:ℚ)], [(11718:ℚ)], [(199:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache78_check : equalRawCheck
    (rawScale (rawFactor 4 76) wordCache16 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache16)) wordCache78 = true := by
  decide +kernel

theorem wordCache78_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 3, 2]) = evalSym W k a (symMap wordCache78) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache16_sound W k a, wordCache16_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache78_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache79 : RawSym := [(0, [[(-388512:ℚ), (-31524:ℚ), (-639:ℚ)], [(15980:ℚ), (870:ℚ), (9:ℚ)], [(-219:ℚ), (-6:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5472:ℚ), (444:ℚ), (9:ℚ)], [(-148:ℚ), (-6:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-1197000:ℚ), (-47250:ℚ)], [(20310:ℚ), (180:ℚ)], [(92:ℚ), (6:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (5, [[(-63840:ℚ), (-2520:ℚ)], [(16192:ℚ), (606:ℚ)], [(-50:ℚ), (6:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (8, [[(-837795:ℚ)], [(-5669:ℚ)], [(127:ℚ)], [(1:ℚ)]]),
 (9, [[(-84840:ℚ)], [(8957:ℚ)], [(198:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache79_check : equalRawCheck
    (rawScale (rawFactor 4 76) wordCache17 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache17)) wordCache79 = true := by
  decide +kernel

theorem wordCache79_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 4, 1]) = evalSym W k a (symMap wordCache79) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache17_sound W k a, wordCache17_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache79_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
