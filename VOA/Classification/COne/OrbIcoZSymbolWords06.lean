import VOA.Classification.COne.OrbIcoZSymbolWords05

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache48 : RawSym := [(0, [[(29931825:ℚ), (1619416:ℚ), (32846:ℚ), (296:ℚ), (1:ℚ)], [(-1619416:ℚ), (-65692:ℚ), (-888:ℚ), (-4:ℚ), (0:ℚ)], [(32846:ℚ), (888:ℚ), (6:ℚ), (0:ℚ), (0:ℚ)], [(-296:ℚ), (-4:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(59020500:ℚ), (2361940:ℚ), (31500:ℚ), (140:ℚ)], [(-675640:ℚ), (4484:ℚ), (480:ℚ), (4:ℚ)], [(-35984:ℚ), (-1380:ℚ), (-12:ℚ), (0:ℚ)], [(760:ℚ), (12:ℚ), (0:ℚ), (0:ℚ)], [(-4:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(40020750:ℚ), (1053360:ℚ), (6930:ℚ)], [(1302840:ℚ), (48156:ℚ), (408:ℚ)], [(-20436:ℚ), (96:ℚ), (6:ℚ)], [(-504:ℚ), (-12:ℚ), (0:ℚ)], [(6:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(11027940:ℚ), (143220:ℚ)], [(861784:ℚ), (13052:ℚ)], [(17440:ℚ), (396:ℚ)], [(-88:ℚ), (4:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (8, [[(1038345:ℚ)], [(130432:ℚ)], [(6134:ℚ)], [(128:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache48_check : equalRawCheck
    (rawScale (rawFactor 2 77) wordCache22 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache22)) wordCache48 = true := by
  decide +kernel

theorem wordCache48_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 2, 2]) = evalSym W k a (symMap wordCache48) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache22_sound W k a, wordCache22_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache48_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache49 : RawSym := [(0, [[(157405636800:ℚ), (4142253600:ℚ)], [(-12856383624:ℚ), (-283822548:ℚ)], [(437480974:ℚ), (7778150:ℚ)], [(-7938735:ℚ), (-106570:ℚ)], [(81025:ℚ), (730:ℚ)], [(-441:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-11084904000:ℚ), (-291708000:ℚ)], [(749253720:ℚ), (15878940:ℚ)], [(-20255650:ℚ), (-324110:ℚ)], [(273775:ℚ), (2940:ℚ)], [(-1850:ℚ), (-10:ℚ)], [(5:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(-307914000:ℚ), (-8103000:ℚ)], [(324450020:ℚ), (8431540:ℚ)], [(-16869010:ℚ), (-332980:ℚ)], [(335970:ℚ), (4460:ℚ)], [(-2990:ℚ), (-20:ℚ)], [(10:ℚ), (0:ℚ)]]),
 (3, [[(-177333156000:ℚ), (0:ℚ)], [(9128930280:ℚ), (-222000:ℚ)], [(-127487676:ℚ), (338960:ℚ)], [(-5074490:ℚ), (-119980:ℚ)], [(206665:ℚ), (3040:ℚ)], [(-2590:ℚ), (-20:ℚ)], [(11:ℚ), (0:ℚ)]]),
 (4, [[(-35945910000:ℚ), (0:ℚ)], [(13348212300:ℚ), (-4500:ℚ)], [(-465163530:ℚ), (8310:ℚ)], [(2952120:ℚ), (-4610:ℚ)], [(105080:ℚ), (810:ℚ)], [(-1980:ℚ), (-10:ℚ)], [(10:ℚ), (0:ℚ)]]),
 (5, [[(-3834230400:ℚ), (0:ℚ)], [(2331260256:ℚ), (-48:ℚ)], [(-374520936:ℚ), (100:ℚ)], [(7750490:ℚ), (-70:ℚ)], [(28345:ℚ), (20:ℚ)], [(-1766:ℚ), (-2:ℚ)], [(11:ℚ), (0:ℚ)]]),
 (6, [[(-252252000:ℚ)], [(200503800:ℚ)], [(-52676080:ℚ)], [(4744930:ℚ)], [(-37770:ℚ)], [(-970:ℚ)], [(10:ℚ)]]),
 (7, [[(-9828000:ℚ)], [(9322200:ℚ)], [(-3233220:ℚ)], [(484930:ℚ)], [(-25985:ℚ)], [(-130:ℚ)], [(5:ℚ)]]),
 (8, [[(-176400:ℚ)], [(190260:ℚ)], [(-79496:ℚ)], [(15975:ℚ)], [(-1505:ℚ)], [(45:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache49_check : equalRawCheck
    (rawScale (rawFactor 3 76) wordCache12 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache12)) wordCache49 = true := by
  decide +kernel

theorem wordCache49_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache49) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache12_sound W k a, wordCache12_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache49_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache50 : RawSym := [(0, [[(2098741824:ℚ), (83591424:ℚ), (746352:ℚ)], [(-143435224:ℚ), (-4602952:ℚ), (-31102:ℚ)], [(3920610:ℚ), (95037:ℚ), (432:ℚ)], [(-53575:ℚ), (-872:ℚ), (-2:ℚ)], [(366:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-88679232:ℚ), (-3532032:ℚ), (-31536:ℚ)], [(4811640:ℚ), (144744:ℚ), (870:ℚ)], [(-97890:ℚ), (-1977:ℚ), (-6:ℚ)], [(885:ℚ), (9:ℚ), (0:ℚ)], [(-3:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(1077699000:ℚ), (28360500:ℚ), (0:ℚ)], [(-28316326:ℚ), (-388646:ℚ), (-438:ℚ)], [(793241:ℚ), (33071:ℚ), (444:ℚ)], [(-27522:ℚ), (-964:ℚ), (-6:ℚ)], [(409:ℚ), (7:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-2184924000:ℚ), (-27195000:ℚ), (0:ℚ)], [(42685272:ℚ), (-402548:ℚ), (-4:ℚ)], [(-203284:ℚ), (-1576:ℚ), (6:ℚ)], [(9002:ℚ), (308:ℚ), (-2:ℚ)], [(-191:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-272916000:ℚ), (-3496500:ℚ)], [(96149880:ℚ), (1163520:ℚ)], [(-1719480:ℚ), (633:ℚ)], [(-2520:ℚ), (18:ℚ)], [(120:ℚ), (-3:ℚ)]]),
 (5, [[(-1037144640:ℚ), (-189840:ℚ)], [(1991280:ℚ), (109732:ℚ)], [(-464824:ℚ), (-15220:ℚ)], [(6994:ℚ), (-91:ℚ)], [(91:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(-202125000:ℚ), (-4200:ℚ)], [(36632050:ℚ), (3230:ℚ)], [(845405:ℚ), (-793:ℚ)], [(-16638:ℚ), (58:ℚ)], [(-155:ℚ), (1:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (7, [[(-15724800:ℚ)], [(5251320:ℚ)], [(-333372:ℚ)], [(-17850:ℚ)], [(39:ℚ)], [(3:ℚ)]]),
 (8, [[(-470400:ℚ)], [(218260:ℚ)], [(-29616:ℚ)], [(511:ℚ)], [(84:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache50_check : equalRawCheck
    (rawScale (rawFactor 3 76) wordCache13 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache13)) wordCache50 = true := by
  decide +kernel

theorem wordCache50_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 2, 1, 1, 1]) = evalSym W k a (symMap wordCache50) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache13_sound W k a, wordCache13_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache50_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache51 : RawSym := [(0, [[(28749888:ℚ), (1544392:ℚ), (26128:ℚ), (142:ℚ)], [(-1571032:ℚ), (-63642:ℚ), (-723:ℚ), (-2:ℚ)], [(32186:ℚ), (874:ℚ), (5:ℚ), (0:ℚ)], [(-293:ℚ), (-4:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(-404928:ℚ), (-21752:ℚ), (-368:ℚ), (-2:ℚ)], [(16424:ℚ), (590:ℚ), (5:ℚ), (0:ℚ)], [(-222:ℚ), (-4:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(28738640:ℚ), (1144640:ℚ), (10220:ℚ)], [(-339076:ℚ), (1694:ℚ), (152:ℚ)], [(-17538:ℚ), (-676:ℚ), (-4:ℚ)], [(376:ℚ), (6:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-29127140:ℚ), (-756000:ℚ), (-4900:ℚ)], [(372076:ℚ), (-5452:ℚ), (-136:ℚ)], [(-5:ℚ), (-90:ℚ), (-3:ℚ)], [(78:ℚ), (4:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(5370750:ℚ), (141330:ℚ), (-210:ℚ)], [(632040:ℚ), (18494:ℚ), (67:ℚ)], [(-8032:ℚ), (32:ℚ), (1:ℚ)], [(-168:ℚ), (-4:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(-25865840:ℚ), (-331240:ℚ)], [(-580096:ℚ), (-12790:ℚ)], [(11047:ℚ), (-76:ℚ)], [(90:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(-1724800:ℚ), (-22400:ℚ)], [(288820:ℚ), (3460:ℚ)], [(11478:ℚ), (194:ℚ)], [(-40:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (7, [[(-5241600:ℚ)], [(-346200:ℚ)], [(-4996:ℚ)], [(54:ℚ)], [(1:ℚ)]]),
 (8, [[(-470400:ℚ)], [(30100:ℚ)], [(4376:ℚ)], [(125:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache51_check : equalRawCheck
    (rawScale (rawFactor 3 76) wordCache14 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache14)) wordCache51 = true := by
  decide +kernel

theorem wordCache51_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 2, 2, 1]) = evalSym W k a (symMap wordCache51) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache14_sound W k a, wordCache14_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache51_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache52 : RawSym := [(0, [[(28361376:ℚ), (1523376:ℚ), (20448:ℚ)], [(-1555052:ℚ), (-63062:ℚ), (-572:ℚ)], [(31967:ℚ), (870:ℚ), (4:ℚ)], [(-292:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-798912:ℚ), (-42912:ℚ), (-576:ℚ)], [(32552:ℚ), (1172:ℚ), (8:ℚ)], [(-442:ℚ), (-8:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-5548:ℚ), (-298:ℚ), (-4:ℚ)], [(5697:ℚ), (302:ℚ), (4:ℚ)], [(-150:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-59052000:ℚ), (-1554000:ℚ)], [(1518760:ℚ), (19520:ℚ)], [(2248:ℚ), (316:ℚ)], [(-310:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (4, [[(-4788000:ℚ), (-126000:ℚ)], [(1654440:ℚ), (41880:ℚ)], [(-18508:ℚ), (64:ℚ)], [(-336:ℚ), (-8:ℚ)], [(4:ℚ), (0:ℚ)]]),
 (5, [[(-127680:ℚ), (-3360:ℚ)], [(74336:ℚ), (1912:ℚ)], [(-10532:ℚ), (-252:ℚ)], [(-26:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (6, [[(28168140:ℚ)], [(95872:ℚ)], [(-10539:ℚ)], [(-18:ℚ)], [(1:ℚ)]]),
 (7, [[(4389840:ℚ)], [(-659688:ℚ)], [(-12700:ℚ)], [(106:ℚ)], [(2:ℚ)]]),
 (8, [[(196980:ℚ)], [(-55216:ℚ)], [(2951:ℚ)], [(124:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache52_check : equalRawCheck
    (rawScale (rawFactor 3 76) wordCache15 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache15)) wordCache52 = true := by
  decide +kernel

theorem wordCache52_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 3, 1, 1]) = evalSym W k a (symMap wordCache52) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache15_sound W k a, wordCache15_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache52_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache53 : RawSym := [(0, [[(393908:ℚ), (26706:ℚ), (582:ℚ), (4:ℚ)], [(-16127:ℚ), (-731:ℚ), (-8:ℚ), (0:ℚ)], [(220:ℚ), (5:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(194180:ℚ), (10430:ℚ), (140:ℚ)], [(333:ℚ), (158:ℚ), (4:ℚ)], [(-114:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-787360:ℚ), (-31360:ℚ), (-280:ℚ)], [(9752:ℚ), (-28:ℚ), (-4:ℚ)], [(160:ℚ), (6:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(-340480:ℚ), (-8960:ℚ)], [(-11024:ℚ), (-408:ℚ)], [(52:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (6, [[(361130:ℚ), (4690:ℚ)], [(5859:ℚ), (137:ℚ)], [(-60:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(136010:ℚ)], [(8663:ℚ)], [(166:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache53_check : equalRawCheck
    (rawScale (rawFactor 3 76) wordCache16 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache16)) wordCache53 = true := by
  decide +kernel

theorem wordCache53_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 3, 2]) = evalSym W k a (symMap wordCache53) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache16_sound W k a, wordCache16_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache53_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache54 : RawSym := [(0, [[(2071126800:ℚ), (82845072:ℚ)], [(-141911274:ℚ), (-4571850:ℚ)], [(3889075:ℚ), (94605:ℚ)], [(-53285:ℚ), (-870:ℚ)], [(365:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-116683200:ℚ), (-4667328:ℚ)], [(6351576:ℚ), (191832:ℚ)], [(-129644:ℚ), (-2628:ℚ)], [(1176:ℚ), (12:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(-2430900:ℚ), (-97236:ℚ)], [(2529462:ℚ), (99882:ℚ)], [(-99894:ℚ), (-2664:ℚ)], [(1338:ℚ), (18:ℚ)], [(-6:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(-44400:ℚ), (-1776:ℚ)], [(67792:ℚ), (2688:ℚ)], [(-23996:ℚ), (-924:ℚ)], [(608:ℚ), (12:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (4, [[(3594591000:ℚ), (0:ℚ)], [(-153758880:ℚ), (-18:ℚ)], [(1897080:ℚ), (33:ℚ)], [(2520:ℚ), (-18:ℚ)], [(-120:ℚ), (3:ℚ)]]),
 (5, [[(766846080:ℚ)], [(-214288704:ℚ)], [(5747800:ℚ)], [(-23860:ℚ)], [(-520:ℚ)], [(4:ℚ)]]),
 (6, [[(75675600:ℚ)], [(-35286300:ℚ)], [(4332306:ℚ)], [(-58794:ℚ)], [(-354:ℚ)], [(6:ℚ)]]),
 (7, [[(3931200:ℚ)], [(-2437200:ℚ)], [(498912:ℚ)], [(-34084:ℚ)], [(48:ℚ)], [(4:ℚ)]]),
 (8, [[(88200:ℚ)], [(-66150:ℚ)], [(18157:ℚ)], [(-2131:ℚ)], [(83:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache54_check : equalRawCheck
    (rawScale (rawFactor 4 75) wordCache7 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache7)) wordCache54 = true := by
  decide +kernel

theorem wordCache54_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache54) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache7_sound W k a, wordCache7_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache54_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache55 : RawSym := [(0, [[(27988200:ℚ), (1502928:ℚ), (15336:ℚ)], [(-1539501:ℚ), (-62490:ℚ), (-429:ℚ)], [(31751:ℚ), (866:ℚ), (3:ℚ)], [(-291:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-788400:ℚ), (-42336:ℚ), (-432:ℚ)], [(32262:ℚ), (1164:ℚ), (6:ℚ)], [(-440:ℚ), (-8:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(14180250:ℚ), (567210:ℚ), (0:ℚ)], [(-175270:ℚ), (477:ℚ), (-3:ℚ)], [(-3034:ℚ), (-38:ℚ), (3:ℚ)], [(38:ℚ), (-1:ℚ), (0:ℚ)]]),
 (3, [[(777000:ℚ), (31080:ℚ)], [(-387160:ℚ), (-15072:ℚ)], [(-1126:ℚ), (-246:ℚ)], [(232:ℚ), (6:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (4, [[(46100250:ℚ), (599130:ℚ)], [(-1393320:ℚ), (-10662:ℚ)], [(9032:ℚ), (44:ℚ)], [(168:ℚ), (4:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (5, [[(4915680:ℚ), (63840:ℚ)], [(-1310624:ℚ), (-16192:ℚ)], [(20042:ℚ), (50:ℚ)], [(104:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (6, [[(19711230:ℚ), (2100:ℚ)], [(238966:ℚ), (-925:ℚ)], [(-3502:ℚ), (96:ℚ)], [(-38:ℚ), (1:ℚ)]]),
 (7, [[(3046680:ℚ)], [(-419544:ℚ)], [(-15402:ℚ)], [(104:ℚ)], [(2:ℚ)]]),
 (8, [[(136710:ℚ)], [(-36603:ℚ)], [(1529:ℚ)], [(123:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache55_check : equalRawCheck
    (rawScale (rawFactor 4 75) wordCache8 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache8)) wordCache55 = true := by
  decide +kernel

theorem wordCache55_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 2, 1, 1]) = evalSym W k a (symMap wordCache55) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache8_sound W k a, wordCache8_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache55_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
