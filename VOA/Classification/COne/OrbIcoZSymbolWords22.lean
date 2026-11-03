import VOA.Classification.COne.OrbIcoZSymbolWords21

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache176 : RawSym := [(0, [[(-2126356848:ℚ), (-223159248:ℚ), (-4478112:ℚ)], [(144959174:ℚ), (12284906:ℚ), (186612:ℚ)], [(-3952145:ℚ), (-253576:ℚ), (-2592:ℚ)], [(53865:ℚ), (2326:ℚ), (12:ℚ)], [(-367:ℚ), (-8:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(89846064:ℚ), (9429264:ℚ), (189216:ℚ)], [(-4859598:ℚ), (-386274:ℚ), (-5220:ℚ)], [(98547:ℚ), (5274:ℚ), (36:ℚ)], [(-888:ℚ), (-24:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(1247862:ℚ), (130962:ℚ), (2628:ℚ)], [(-1298025:ℚ), (-134508:ℚ), (-2664:ℚ)], [(50835:ℚ), (3570:ℚ), (36:ℚ)], [(-675:ℚ), (-24:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(2273502000:ℚ), (177156000:ℚ), (0:ℚ)], [(-87986864:ℚ), (-4555084:ℚ), (24:ℚ)], [(655436:ℚ), (-8554:ℚ), (-36:ℚ)], [(19212:ℚ), (1552:ℚ), (12:ℚ)], [(-386:ℚ), (-14:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(276507000:ℚ), (21546000:ℚ)], [(-99134910:ℚ), (-7444980:ℚ)], [(2309667:ℚ), (83286:ℚ)], [(5523:ℚ), (1512:ℚ)], [(-483:ℚ), (-18:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (5, [[(14747040:ℚ), (1149120:ℚ)], [(-8777328:ℚ), (-669024:ℚ)], [(1327950:ℚ), (94788:ℚ)], [(-12795:ℚ), (234:ℚ)], [(-270:ℚ), (-18:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (6, [[(323400:ℚ), (25200:ℚ)], [(-252910:ℚ), (-19380:ℚ)], [(64291:ℚ), (4758:ℚ)], [(-5259:ℚ), (-348:ℚ)], [(-19:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(8385249600:ℚ), (207043200:ℚ)], [(-382053060:ℚ), (-6877320:ℚ)], [(5953548:ℚ), (62096:ℚ)], [(-28861:ℚ), (54:ℚ)], [(-108:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (8, [[(2257567200:ℚ), (55742400:ℚ)], [(-396426870:ℚ), (-9100140:ℚ)], [(11214831:ℚ), (164562:ℚ)], [(-92973:ℚ), (-264:ℚ)], [(-111:ℚ), (-6:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (9, [[(228614400:ℚ), (5644800:ℚ)], [(-65827440:ℚ), (-1555680:ℚ)], [(5320482:ℚ), (112164:ℚ)], [(-84027:ℚ), (-690:ℚ)], [(102:ℚ), (-6:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (10, [[(-7284940740:ℚ), (211680:ℚ)], [(113047326:ℚ), (-79212:ℚ)], [(2133192:ℚ), (9698:ℚ)], [(-53672:ℚ), (-372:ℚ)], [(132:ℚ), (-2:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (11, [[(-2701301400:ℚ)], [(279877500:ℚ)], [(-224466:ℚ)], [(-78267:ℚ)], [(294:ℚ)], [(3:ℚ)]]),
 (12, [[(-362369700:ℚ)], [(66068100:ℚ)], [(-2637543:ℚ)], [(-39927:ℚ)], [(507:ℚ)], [(3:ℚ)]]),
 (13, [[(-17463600:ℚ)], [(4428900:ℚ)], [(-339084:ℚ)], [(4583:ℚ)], [(240:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache176_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache23 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache23)) wordCache176 = true := by
  decide +kernel

theorem wordCache176_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 3, 1, 1, 1]) = evalSym W k a (symMap wordCache176) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache23_sound W k a, wordCache23_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache176_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache177 : RawSym := [(0, [[(-29128176:ℚ), (-3461534:ℚ), (-103802:ℚ), (-852:ℚ)], [(1586726:ℚ), (142829:ℚ), (2882:ℚ), (12:ℚ)], [(-32403:ℚ), (-1964:ℚ), (-20:ℚ), (0:ℚ)], [(294:ℚ), (9:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(410256:ℚ), (48754:ℚ), (1462:ℚ), (12:ℚ)], [(-16570:ℚ), (-1325:ℚ), (-20:ℚ), (0:ℚ)], [(223:ℚ), (9:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-14558390:ℚ), (-1527890:ℚ), (-30660:ℚ)], [(169281:ℚ), (-2284:ℚ), (-456:ℚ)], [(8881:ℚ), (902:ℚ), (12:ℚ)], [(-189:ℚ), (-8:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(29515640:ℚ), (2688000:ℚ), (30240:ℚ)], [(-565656:ℚ), (-13858:ℚ), (420:ℚ)], [(-558:ℚ), (-221:ℚ), (6:ℚ)], [(38:ℚ), (-1:ℚ), (0:ℚ)]]),
 (4, [[(1212750:ℚ), (110670:ℚ), (1260:ℚ)], [(-418845:ℚ), (-36779:ℚ), (-402:ℚ)], [(4619:ℚ), (-58:ℚ), (-6:ℚ)], [(85:ℚ), (7:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(13108480:ℚ), (1021440:ℚ)], [(254184:ℚ), (33072:ℚ)], [(-7514:ℚ), (-156:ℚ)], [(-51:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (6, [[(862400:ℚ), (67200:ℚ)], [(-144410:ℚ), (-10380:ℚ)], [(-5739:ℚ), (-582:ℚ)], [(20:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(104815620:ℚ), (3914820:ℚ), (32760:ℚ)], [(-3465468:ℚ), (-80688:ℚ), (-264:ℚ)], [(31101:ℚ), (157:ℚ), (-2:ℚ)], [(28:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (8, [[(9406530:ℚ), (351330:ℚ), (2940:ℚ)], [(-1534197:ℚ), (-52927:ℚ), (-406:ℚ)], [(27551:ℚ), (370:ℚ), (-2:ℚ)], [(-43:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (9, [[(38102400:ℚ), (940800:ℚ)], [(595560:ℚ), (26320:ℚ)], [(-25958:ℚ), (-316:ℚ)], [(77:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (10, [[(-83587140:ℚ), (-965790:ℚ)], [(-12474:ℚ), (-16359:ℚ)], [(9816:ℚ), (-266:ℚ)], [(38:ℚ), (-1:ℚ)]]),
 (11, [[(-10848600:ℚ), (-132300:ℚ)], [(993300:ℚ), (10500:ℚ)], [(11066:ℚ), (263:ℚ)], [(-181:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (12, [[(-27452250:ℚ)], [(-1333815:ℚ)], [(-4679:ℚ)], [(215:ℚ)], [(1:ℚ)]]),
 (13, [[(-3969000:ℚ)], [(90090:ℚ)], [(16479:ℚ)], [(286:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache177_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache24 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache24)) wordCache177 = true := by
  decide +kernel

theorem wordCache177_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 3, 2, 1]) = evalSym W k a (symMap wordCache177) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache24_sound W k a, wordCache24_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache177_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache178 : RawSym := [(0, [[(-404558:ℚ), (-53854:ℚ), (-2048:ℚ), (-24:ℚ)], [(16419:ℚ), (1468:ℚ), (28:ℚ), (0:ℚ)], [(-222:ℚ), (-10:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(797720:ℚ), (83720:ℚ), (1680:ℚ)], [(-9744:ℚ), (76:ℚ), (24:ℚ)], [(-162:ℚ), (-16:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-361130:ℚ), (-28140:ℚ)], [(-5859:ℚ), (-822:ℚ)], [(60:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(1326780:ℚ), (66780:ℚ), (840:ℚ)], [(-27072:ℚ), (-522:ℚ), (4:ℚ)], [(51:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (10, [[(-2143260:ℚ), (-52920:ℚ)], [(-17766:ℚ), (-1092:ℚ)], [(384:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (13, [[(793800:ℚ)], [(29610:ℚ)], [(333:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache178_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache25 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache25)) wordCache178 = true := by
  decide +kernel

theorem wordCache178_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 3, 3]) = evalSym W k a (symMap wordCache178) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache25_sound W k a, wordCache25_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache178_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache179 : RawSym := [(0, [[(-28734552:ℚ), (-3419928:ℚ), (-92016:ℚ)], [(1570603:ℚ), (141675:ℚ), (2574:ℚ)], [(-32183:ℚ), (-1956:ℚ), (-18:ℚ)], [(293:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(809424:ℚ), (96336:ℚ), (2592:ℚ)], [(-32842:ℚ), (-2634:ℚ), (-36:ℚ)], [(444:ℚ), (18:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5621:ℚ), (669:ℚ), (18:ℚ)], [(-5771:ℚ), (-678:ℚ), (-18:ℚ)], [(151:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-46084500:ℚ), (-3591000:ℚ)], [(1380435:ℚ), (60930:ℚ)], [(-6613:ℚ), (276:ℚ)], [(-123:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(-4915680:ℚ), (-383040:ℚ)], [(1310624:ℚ), (97152:ℚ)], [(-20042:ℚ), (-300:ℚ)], [(-104:ℚ), (-12:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (6, [[(-161700:ℚ), (-12600:ℚ)], [(73325:ℚ), (5550:ℚ)], [(-8317:ℚ), (-576:ℚ)], [(19:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(103521600:ℚ), (3882060:ℚ)], [(-3438660:ℚ), (-80424:ℚ)], [(31048:ℚ), (159:ℚ)], [(27:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(18580800:ℚ), (696780:ℚ)], [(-3033380:ℚ), (-105042:ℚ)], [(54854:ℚ), (744:ℚ)], [(-88:ℚ), (6:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (9, [[(940800:ℚ), (35280:ℚ)], [(-259280:ℚ), (-9282:ℚ)], [(18694:ℚ), (585:ℚ)], [(-115:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (11, [[(140067480:ℚ)], [(-1299452:ℚ)], [(-23434:ℚ)], [(143:ℚ)], [(1:ℚ)]]),
 (12, [[(37579080:ℚ)], [(-3306632:ℚ)], [(-14918:ℚ)], [(428:ℚ)], [(2:ℚ)]]),
 (13, [[(2716560:ℚ)], [(-432684:ℚ)], [(13628:ℚ)], [(285:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache179_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache26 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache26)) wordCache179 = true := by
  decide +kernel

theorem wordCache179_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 4, 1, 1]) = evalSym W k a (symMap wordCache179) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache26_sound W k a, wordCache26_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache179_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache180 : RawSym := [(0, [[(-399091:ℚ), (-53120:ℚ), (-1947:ℚ), (-18:ℚ)], [(16271:ℚ), (1458:ℚ), (27:ℚ), (0:ℚ)], [(-221:ℚ), (-10:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-196735:ℚ), (-23415:ℚ), (-630:ℚ)], [(-371:ℚ), (-354:ℚ), (-18:ℚ)], [(115:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-606375:ℚ), (-55335:ℚ), (-630:ℚ)], [(10185:ℚ), (208:ℚ), (-6:ℚ)], [(47:ℚ), (7:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-250635:ℚ), (-19530:ℚ)], [(-7217:ℚ), (-816:ℚ)], [(59:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(1310400:ℚ), (65940:ℚ), (630:ℚ)], [(-26940:ℚ), (-526:ℚ), (3:ℚ)], [(52:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (9, [[(470400:ℚ), (17640:ℚ)], [(13160:ℚ), (714:ℚ)], [(-158:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (11, [[(1687560:ℚ), (20580:ℚ)], [(4676:ℚ), (308:ℚ)], [(-226:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (13, [[(493920:ℚ)], [(27972:ℚ)], [(332:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache180_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache27 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache27)) wordCache180 = true := by
  decide +kernel

theorem wordCache180_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 4, 2]) = evalSym W k a (symMap wordCache180) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache27_sound W k a, wordCache27_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache180_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache181 : RawSym := [(0, [[(-393624:ℚ), (-52540:ℚ), (-1704:ℚ)], [(16123:ℚ), (1450:ℚ), (24:ℚ)], [(-220:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5544:ℚ), (740:ℚ), (24:ℚ)], [(-149:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(819280:ℚ), (63840:ℚ)], [(-15568:ℚ), (-384:ℚ)], [(-13:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (6, [[(53900:ℚ), (4200:ℚ)], [(-11095:ℚ), (-810:ℚ)], [(58:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(1294020:ℚ), (65520:ℚ)], [(-26808:ℚ), (-528:ℚ)], [(53:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (8, [[(116130:ℚ), (5880:ℚ)], [(-17507:ℚ), (-812:ℚ)], [(124:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (12, [[(-2318190:ℚ)], [(-539:ℚ)], [(260:ℚ)], [(1:ℚ)]]),
 (13, [[(-335160:ℚ)], [(23814:ℚ)], [(331:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache181_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache28 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache28)) wordCache181 = true := by
  decide +kernel

theorem wordCache181_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 5, 1]) = evalSym W k a (symMap wordCache181) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache28_sound W k a, wordCache28_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache181_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache182 : RawSym := [(0, [[(-5467:ℚ), (-811:ℚ), (-30:ℚ)], [(148:ℚ), (11:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-13475:ℚ), (-1050:ℚ)], [(98:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(16380:ℚ), (1050:ℚ)], [(-132:ℚ), (5:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (13, [[(35280:ℚ)], [(378:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache182_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache29 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache29)) wordCache182 = true := by
  decide +kernel

theorem wordCache182_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 6]) = evalSym W k a (symMap wordCache182) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache29_sound W k a, wordCache29_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache182_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache183 : RawSym := [(0, [[(-157405636800:ℚ), (-14497887600:ℚ)], [(12856383624:ℚ), (993378918:ℚ)], [(-437480974:ℚ), (-27223525:ℚ)], [(7938735:ℚ), (372995:ℚ)], [(-81025:ℚ), (-2555:ℚ)], [(441:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(11084904000:ℚ), (1020978000:ℚ)], [(-749253720:ℚ), (-55576290:ℚ)], [(20255650:ℚ), (1134385:ℚ)], [(-273775:ℚ), (-10290:ℚ)], [(1850:ℚ), (35:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(307914000:ℚ), (28360500:ℚ)], [(-324450020:ℚ), (-29510390:ℚ)], [(16869010:ℚ), (1165430:ℚ)], [(-335970:ℚ), (-15610:ℚ)], [(2990:ℚ), (70:ℚ)], [(-10:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(8436000:ℚ), (777000:ℚ)], [(-12991480:ℚ), (-1186360:ℚ)], [(4728720:ℚ), (419930:ℚ)], [(-175510:ℚ), (-10640:ℚ)], [(2280:ℚ), (70:ℚ)], [(-10:ℚ), (0:ℚ)]]),
 (4, [[(0:ℚ), (0:ℚ)], [(171000:ℚ), (15750:ℚ)], [(-318030:ℚ), (-29085:ℚ)], [(179335:ℚ), (16135:ℚ)], [(-33085:ℚ), (-2835:ℚ)], [(785:ℚ), (35:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (5, [[(0:ℚ), (0:ℚ)], [(1824:ℚ), (168:ℚ)], [(-3824:ℚ), (-350:ℚ)], [(2710:ℚ), (245:ℚ)], [(-795:ℚ), (-70:ℚ)], [(86:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-853611242400:ℚ)], [(49223995010:ℚ)], [(-1086597581:ℚ)], [(10760030:ℚ)], [(-33620:ℚ)], [(-160:ℚ)], [(1:ℚ)]]),
 (9, [[(-432208224000:ℚ)], [(73478579600:ℚ)], [(-2735510110:ℚ)], [(39593405:ℚ)], [(-196855:ℚ)], [(-445:ℚ)], [(5:ℚ)]]),
 (10, [[(-97246850400:ℚ)], [(26122300380:ℚ)], [(-2125925510:ℚ)], [(50722200:ℚ)], [(-400100:ℚ)], [(-180:ℚ)], [(10:ℚ)]]),
 (11, [[(-12005784000:ℚ)], [(4277334200:ℚ)], [(-532150880:ℚ)], [(25938230:ℚ)], [(-355370:ℚ)], [(530:ℚ)], [(10:ℚ)]]),
 (12, [[(-805266000:ℚ)], [(350280050:ℚ)], [(-57502645:ℚ)], [(4283330:ℚ)], [(-129760:ℚ)], [(620:ℚ)], [(5:ℚ)]]),
 (13, [[(-23284800:ℚ)], [(11788440:ℚ)], [(-2364746:ℚ)], [(233925:ℚ)], [(-11255:ℚ)], [(195:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache183_check : equalRawCheck
    (rawScale (rawFactor 8 76) wordCache12 ++
      rawScale (rawSecond 8) (rawShift 8 wordCache12)) wordCache183 = true := by
  decide +kernel

theorem wordCache183_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [8, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache183) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache12_sound W k a, wordCache12_sound W (k - (8 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache183_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
