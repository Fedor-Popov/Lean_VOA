import VOA.Classification.COne.OrbIcoZSymbolWords20

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache168 : RawSym := [(0, [[(-409812:ℚ), (-54428:ℚ), (-2273:ℚ), (-30:ℚ)], [(16564:ℚ), (1476:ℚ), (31:ℚ), (0:ℚ)], [(-223:ℚ), (-10:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(404040:ℚ), (42280:ℚ), (1050:ℚ)], [(-4868:ℚ), (44:ℚ), (15:ℚ)], [(-82:ℚ), (-8:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-614250:ℚ), (-55755:ℚ), (-1050:ℚ)], [(10215:ℚ), (204:ℚ), (-10:ℚ)], [(48:ℚ), (7:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-1078000:ℚ), (-68425:ℚ), (-1050:ℚ)], [(21315:ℚ), (484:ℚ), (-6:ℚ)], [(-18:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (7, [[(540540:ℚ), (34650:ℚ)], [(6408:ℚ), (855:ℚ)], [(-93:ℚ), (5:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (9, [[(896000:ℚ), (33600:ℚ)], [(7920:ℚ), (717:ℚ)], [(-159:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (10, [[(-1403325:ℚ), (-34650:ℚ)], [(-4869:ℚ), (-548:ℚ)], [(193:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (13, [[(1039500:ℚ)], [(33765:ℚ)], [(334:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache168_check : equalRawCheck
    (rawScale (rawFactor 6 78) wordCache40 ++
      rawScale (rawSecond 6) (rawShift 6 wordCache40)) wordCache168 = true := by
  decide +kernel

theorem wordCache168_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [6, 4, 3]) = evalSym W k a (symMap wordCache168) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache40_sound W k a, wordCache40_sound W (k - (6 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache168_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache169 : RawSym := [(0, [[(-29107728:ℚ), (-3460824:ℚ), (-102240:ℚ)], [(1586154:ℚ), (142819:ℚ), (2860:ℚ)], [(-32399:ℚ), (-1964:ℚ), (-20:ℚ)], [(294:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(819936:ℚ), (97488:ℚ), (2880:ℚ)], [(-33132:ℚ), (-2650:ℚ), (-40:ℚ)], [(446:ℚ), (18:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5694:ℚ), (677:ℚ), (20:ℚ)], [(-5845:ℚ), (-686:ℚ), (-20:ℚ)], [(152:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(63903840:ℚ), (4096400:ℚ)], [(-2033584:ℚ), (-77840:ℚ)], [(14554:ℚ), (-65:ℚ)], [(91:ℚ), (5:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(-74624550:ℚ), (-3665200:ℚ)], [(880831:ℚ), (-26474:ℚ)], [(8539:ℚ), (500:ℚ)], [(-19:ℚ), (6:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (7, [[(-12612600:ℚ), (-634200:ℚ)], [(2290476:ℚ), (106306:ℚ)], [(-31270:ℚ), (-83:ℚ)], [(-27:ℚ), (-3:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (8, [[(-580650:ℚ), (-29400:ℚ)], [(183757:ℚ), (8932:ℚ)], [(-15031:ℚ), (-648:ℚ)], [(83:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (11, [[(159600700:ℚ)], [(-1766196:ℚ)], [(-20729:ℚ)], [(144:ℚ)], [(1:ℚ)]]),
 (12, [[(42819700:ℚ)], [(-3844366:ℚ)], [(-9366:ℚ)], [(430:ℚ)], [(2:ℚ)]]),
 (13, [[(3095400:ℚ)], [(-498562:ℚ)], [(16475:ℚ)], [(286:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache169_check : equalRawCheck
    (rawScale (rawFactor 6 78) wordCache41 ++
      rawScale (rawSecond 6) (rawShift 6 wordCache41)) wordCache169 = true := by
  decide +kernel

theorem wordCache169_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [6, 5, 1, 1]) = evalSym W k a (symMap wordCache169) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache41_sound W k a, wordCache41_sound W (k - (6 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache169_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache170 : RawSym := [(0, [[(-404274:ℚ), (-53761:ℚ), (-2097:ℚ), (-20:ℚ)], [(16415:ℚ), (1467:ℚ), (29:ℚ), (0:ℚ)], [(-222:ℚ), (-10:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-199290:ℚ), (-23695:ℚ), (-700:ℚ)], [(-409:ℚ), (-362:ℚ), (-20:ℚ)], [(116:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(829920:ℚ), (64120:ℚ), (700:ℚ)], [(-15632:ℚ), (-382:ℚ), (5:ℚ)], [(-14:ℚ), (-6:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-1064525:ℚ), (-67725:ℚ), (-700:ℚ)], [(21217:ℚ), (488:ℚ), (-4:ℚ)], [(-19:ℚ), (5:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (7, [[(327600:ℚ), (21000:ℚ)], [(9060:ℚ), (850:ℚ)], [(-92:ℚ), (5:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-400925:ℚ), (-20300:ℚ)], [(-11041:ℚ), (-816:ℚ)], [(125:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (11, [[(1922900:ℚ), (23450:ℚ)], [(1888:ℚ), (309:ℚ)], [(-227:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (13, [[(562800:ℚ)], [(30866:ℚ)], [(333:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache170_check : equalRawCheck
    (rawScale (rawFactor 6 78) wordCache42 ++
      rawScale (rawSecond 6) (rawShift 6 wordCache42)) wordCache170 = true := by
  decide +kernel

theorem wordCache170_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [6, 5, 2]) = evalSym W k a (symMap wordCache170) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache42_sound W k a, wordCache42_sound W (k - (6 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache170_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache171 : RawSym := [(0, [[(-398736:ℚ), (-53250:ℚ), (-1775:ℚ)], [(16266:ℚ), (1460:ℚ), (25:ℚ)], [(-221:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5616:ℚ), (750:ℚ), (25:ℚ)], [(-150:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-2102100:ℚ), (-134750:ℚ)], [(42238:ℚ), (980:ℚ)], [(-40:ℚ), (10:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (7, [[(-163800:ℚ), (-10500:ℚ)], [(28464:ℚ), (1690:ℚ)], [(-182:ℚ), (10:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (12, [[(-2454725:ℚ)], [(1023:ℚ)], [(261:ℚ)], [(1:ℚ)]]),
 (13, [[(-354900:ℚ)], [(25447:ℚ)], [(332:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache171_check : equalRawCheck
    (rawScale (rawFactor 6 78) wordCache43 ++
      rawScale (rawSecond 6) (rawShift 6 wordCache43)) wordCache171 = true := by
  decide +kernel

theorem wordCache171_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [6, 6, 1]) = evalSym W k a (symMap wordCache171) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache43_sound W k a, wordCache43_sound W (k - (6 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache171_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache172 : RawSym := [(0, [[(-12120234033600:ℚ), (-944433820800:ℚ)], [(1147347175848:ℚ), (77138301744:ℚ)], [(-46542418622:ℚ), (-2624885844:ℚ)], [(1048763569:ℚ), (47632410:ℚ)], [(-14177660:ℚ), (-486150:ℚ)], [(114982:ℚ), (2646:ℚ)], [(-518:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(1024245129600:ℚ), (79811308800:ℚ)], [(-82532928528:ℚ), (-5394626784:ℚ)], [(2770726524:ℚ), (145840680:ℚ)], [(-49603590:ℚ), (-1971180:ℚ)], [(499470:ℚ), (13320:ℚ)], [(-2682:ℚ), (-36:ℚ)], [(6:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(35564067000:ℚ), (2771226000:ℚ)], [(-37935848310:ℚ), (-2920050180:ℚ)], [(2435045685:ℚ), (151821090:ℚ)], [(-64108050:ℚ), (-3023730:ℚ)], [(849300:ℚ), (26910:ℚ)], [(-5640:ℚ), (-90:ℚ)], [(15:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(1299144000:ℚ), (101232000:ℚ)], [(-2017559920:ℚ), (-155897760:ℚ)], [(754205840:ℚ), (56744640:ℚ)], [(-36485980:ℚ), (-2106120:ℚ)], [(702140:ℚ), (27360:ℚ)], [(-6100:ℚ), (-120:ℚ)], [(20:ℚ), (0:ℚ)]]),
 (4, [[(0:ℚ), (0:ℚ)], [(39501000:ℚ), (3078000:ℚ)], [(-73977930:ℚ), (-5724540:ℚ)], [(42380475:ℚ), (3228030:ℚ)], [(-8180640:ℚ), (-595530:ℚ)], [(280590:ℚ), (14130:ℚ)], [(-3510:ℚ), (-90:ℚ)], [(15:ℚ), (0:ℚ)]]),
 (5, [[(0:ℚ), (0:ℚ)], [(842688:ℚ), (65664:ℚ)], [(-1777632:ℚ), (-137664:ℚ)], [(1274964:ℚ), (97560:ℚ)], [(-383550:ℚ), (-28620:ℚ)], [(44502:ℚ), (3096:ℚ)], [(-978:ℚ), (-36:ℚ)], [(6:ℚ), (0:ℚ)]]),
 (6, [[(0:ℚ), (0:ℚ)], [(9240:ℚ), (720:ℚ)], [(-21218:ℚ), (-1644:ℚ)], [(17599:ℚ), (1350:ℚ)], [(-6770:ℚ), (-510:ℚ)], [(1240:ℚ), (90:ℚ)], [(-92:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(57070008777600:ℚ)], [(-3983819310360:ℚ)], [(111943852188:ℚ)], [(-1560816446:ℚ)], [(9980565:ℚ)], [(-4235:ℚ)], [(-273:ℚ)], [(1:ℚ)]]),
 (8, [[(30730004726400:ℚ)], [(-6141159730440:ℚ)], [(287992281072:ℚ)], [(-5759296446:ℚ)], [(51599820:ℚ)], [(-108480:ℚ)], [(-1212:ℚ)], [(6:ℚ)]]),
 (9, [[(7779748032000:ℚ)], [(-2428714663200:ℚ)], [(236506712460:ℚ)], [(-7577973660:ℚ)], [(99395745:ℚ)], [(-402195:ℚ)], [(-1965:ℚ)], [(15:ℚ)]]),
 (10, [[(1166962204800:ℚ)], [(-479382639120:ℚ)], [(69962301600:ℚ)], [(-4203945820:ℚ)], [(88659600:ℚ)], [(-608680:ℚ)], [(-1200:ℚ)], [(20:ℚ)]]),
 (11, [[(108052056000:ℚ)], [(-53858511000:ℚ)], [(10251799140:ℚ)], [(-910487910:ℚ)], [(35894055:ℚ)], [(-434145:ℚ)], [(165:ℚ)], [(15:ℚ)]]),
 (12, [[(5797915200:ℚ)], [(-3346345800:ℚ)], [(772011888:ℚ)], [(-89449446:ℚ)], [(5276580:ℚ)], [(-134040:ℚ)], [(492:ℚ)], [(6:ℚ)]]),
 (13, [[(139708800:ℚ)], [(-90594000:ℚ)], [(24230772:ℚ)], [(-3413696:ℚ)], [(265635:ℚ)], [(-10625:ℚ)], [(153:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache172_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache19 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache19)) wordCache172 = true := by
  decide +kernel

theorem wordCache172_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 1, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache172) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache19_sound W k a, wordCache19_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache172_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache173 : RawSym := [(0, [[(-159476763600:ℚ), (-14553117648:ℚ), (-165690144:ℚ)], [(12998294898:ℚ), (996426818:ℚ), (9143700:ℚ)], [(-441370049:ℚ), (-27286595:ℚ), (-189210:ℚ)], [(7992020:ℚ), (373575:ℚ), (1740:ℚ)], [(-81390:ℚ), (-2557:ℚ), (-6:ℚ)], [(442:ℚ), (7:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(8984606400:ℚ), (819893952:ℚ), (9334656:ℚ)], [(-605754552:ℚ), (-44588920:ℚ), (-383664:ℚ)], [(16334164:ℚ), (909260:ℚ), (5256:ℚ)], [(-220196:ℚ), (-8240:ℚ), (-24:ℚ)], [(1484:ℚ), (28:ℚ), (0:ℚ)], [(-4:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-82982823000:ℚ), (-6466194000:ℚ), (0:ℚ)], [(3350397890:ℚ), (179589144:ℚ), (194472:ℚ)], [(-186697595:ℚ), (-14844000:ℚ), (-199764:ℚ)], [(7972250:ℚ), (563820:ℚ), (5328:ℚ)], [(-159800:ℚ), (-7800:ℚ), (-36:ℚ)], [(1460:ℚ), (36:ℚ), (0:ℚ)], [(-5:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-9094008000:ℚ), (-708624000:ℚ), (0:ℚ)], [(4772501440:ℚ), (362725904:ℚ), (3552:ℚ)], [(-112110640:ℚ), (-4095344:ℚ), (-5376:ℚ)], [(-370080:ℚ), (-56508:ℚ), (1848:ℚ)], [(25840:ℚ), (344:ℚ), (-24:ℚ)], [(-160:ℚ), (4:ℚ), (0:ℚ)]]),
 (4, [[(-553014000:ℚ), (-43092000:ℚ), (0:ℚ)], [(466911270:ℚ), (35823522:ℚ), (36:ℚ)], [(-96923295:ℚ), (-7088083:ℚ), (-66:ℚ)], [(754240:ℚ), (-32797:ℚ), (36:ℚ)], [(55210:ℚ), (3787:ℚ), (-6:ℚ)], [(-1030:ℚ), (-29:ℚ), (0:ℚ)], [(5:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(-19662720:ℚ), (-1532160:ℚ)], [(21253568:ℚ), (1636224:ℚ)], [(-7310504:ℚ), (-548400:ℚ)], [(789020:ℚ), (54360:ℚ)], [(6340:ℚ), (1200:ℚ)], [(-508:ℚ), (-24:ℚ)], [(4:ℚ), (0:ℚ)]]),
 (6, [[(-323400:ℚ), (-25200:ℚ)], [(409990:ℚ), (31620:ℚ)], [(-184757:ℚ), (-13986:ℚ)], [(34594:ℚ), (2514:ℚ)], [(-2036:ℚ), (-126:ℚ)], [(-56:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(687590467200:ℚ), (8385249600:ℚ)], [(-39713600520:ℚ), (-382053060:ℚ)], [(870243996:ℚ), (5953548:ℚ)], [(-8320150:ℚ), (-28861:ℚ)], [(20005:ℚ), (-108:ℚ)], [(190:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(246827347200:ℚ), (3010089600:ℚ)], [(-46352760720:ℚ), (-528569160:ℚ)], [(1754724016:ℚ), (14953108:ℚ)], [(-25118156:ℚ), (-123964:ℚ)], [(111828:ℚ), (-148:ℚ)], [(476:ℚ), (4:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (9, [[(296817696000:ℚ), (457228800:ℚ)], [(-13486443600:ℚ), (-131654880:ℚ)], [(767378780:ℚ), (10640964:ℚ)], [(-19018700:ℚ), (-168054:ℚ)], [(152925:ℚ), (204:ℚ)], [(200:ℚ), (6:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (10, [[(119508177600:ℚ), (34292160:ℚ)], [(-13633885440:ℚ), (-13255704:ℚ)], [(3766800:ℚ), (1729500:ℚ)], [(4120000:ℚ), (-79660:ℚ)], [(-15600:ℚ), (420:ℚ)], [(-160:ℚ), (4:ℚ)]]),
 (11, [[(21697200000:ℚ), (1058400:ℚ)], [(-4253613000:ℚ), (-501900:ℚ)], [(159428500:ℚ), (88096:ℚ)], [(6329530:ℚ), (-6709:ℚ)], [(-146145:ℚ), (176:ℚ)], [(230:ℚ), (1:ℚ)], [(5:ℚ), (0:ℚ)]]),
 (12, [[(1932638400:ℚ)], [(-528754800:ℚ)], [(41357696:ℚ)], [(-105860:ℚ)], [(-72900:ℚ)], [(500:ℚ)], [(4:ℚ)]]),
 (13, [[(69854400:ℚ)], [(-24091200:ℚ)], [(2797236:ℚ)], [(-94696:ℚ)], [(-3457:ℚ)], [(196:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache173_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache20 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache20)) wordCache173 = true := by
  decide +kernel

theorem wordCache173_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 2, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache173) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache20_sound W k a, wordCache20_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache173_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache174 : RawSym := [(0, [[(-2155091400:ℚ), (-226185552:ℚ), (-4933080:ℚ), (-30672:ℚ)], [(146529777:ℚ), (12410458:ℚ), (204451:ℚ), (858:ℚ)], [(-3984328:ℚ), (-255312:ℚ), (-2824:ℚ), (-6:ℚ)], [(54158:ℚ), (2334:ℚ), (13:ℚ), (0:ℚ)], [(-368:ℚ), (-8:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(60706800:ℚ), (6371424:ℚ), (138960:ℚ), (864:ℚ)], [(-3272574:ℚ), (-259852:ℚ), (-3802:ℚ), (-12:ℚ)], [(66142:ℚ), (3532:ℚ), (26:ℚ), (0:ℚ)], [(-594:ℚ), (-16:ℚ), (0:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-2183758500:ℚ), (-199279780:ℚ), (-2268840:ℚ), (0:ℚ)], [(54930505:ℚ), (2420348:ℚ), (-2119:ℚ), (6:ℚ)], [(555142:ℚ), (76210:ℚ), (366:ℚ), (-6:ℚ)], [(-29016:ℚ), (-1424:ℚ), (1:ℚ), (0:ℚ)], [(302:ℚ), (6:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-119658000:ℚ), (-10919440:ℚ), (-124320:ℚ)], [(61176640:ℚ), (5440336:ℚ), (60288:ℚ)], [(-600916:ℚ), (16092:ℚ), (984:ℚ)], [(-37980:ℚ), (-3256:ℚ), (-24:ℚ)], [(772:ℚ), (28:ℚ), (0:ℚ)], [(-4:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-509355000:ℚ), (-39722340:ℚ), (-2520:ℚ)], [(-7816725:ℚ), (-1098104:ℚ), (2028:ℚ)], [(77700:ℚ), (-13508:ℚ), (-360:ℚ)], [(886:ℚ), (-136:ℚ), (-12:ℚ)], [(84:ℚ), (8:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(-54072480:ℚ), (-4213440:ℚ)], [(11748352:ℚ), (860736:ℚ)], [(469618:ℚ), (47772:ℚ)], [(-6114:ℚ), (144:ℚ)], [(-178:ℚ), (-12:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (6, [[(-1778700:ℚ), (-138600:ℚ)], [(718795:ℚ), (54210:ℚ)], [(-52386:ℚ), (-3378:ℚ)], [(-3980:ℚ), (-354:ℚ)], [(-18:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(8488771200:ℚ), (209631240:ℚ), (1294020:ℚ)], [(-385491720:ℚ), (-6930936:ℚ), (-26808:ℚ)], [(5984596:ℚ), (62202:ℚ), (53:ℚ)], [(-28834:ℚ), (56:ℚ), (1:ℚ)], [(-109:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (8, [[(1523625600:ℚ), (37626120:ℚ), (232260:ℚ)], [(-267317960:ℚ), (-6136788:ℚ), (-35014:ℚ)], [(7531408:ℚ), (110204:ℚ), (248:ℚ)], [(-62070:ℚ), (-172:ℚ), (2:ℚ)], [(-76:ℚ), (-4:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (9, [[(6325939200:ℚ), (78109920:ℚ), (11760:ℚ)], [(-734720:ℚ), (666372:ℚ), (-3094:ℚ)], [(-3656044:ℚ), (-14138:ℚ), (195:ℚ)], [(36420:ℚ), (-74:ℚ), (1:ℚ)], [(43:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (10, [[(1405978560:ℚ), (17146080:ℚ)], [(-133815024:ℚ), (-1422792:ℚ)], [(-3435216:ℚ), (-59244:ℚ)], [(107788:ℚ), (592:ℚ)], [(-264:ℚ), (4:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (11, [[(1127290080:ℚ), (1058400:ℚ)], [(41042008:ℚ), (-180600:ℚ)], [(376516:ℚ), (2896:ℚ)], [(8334:ℚ), (438:ℚ)], [(-175:ℚ), (2:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (12, [[(279158880:ℚ)], [(-6705272:ℚ)], [(-1480960:ℚ)], [(-23670:ℚ)], [(340:ℚ)], [(2:ℚ)]]),
 (13, [[(20180160:ℚ)], [(-1923264:ℚ)], [(-89836:ℚ)], [(6128:ℚ)], [(241:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache174_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache21 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache21)) wordCache174 = true := by
  decide +kernel

theorem wordCache174_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 2, 2, 1, 1]) = evalSym W k a (symMap wordCache174) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache21_sound W k a, wordCache21_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache174_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache175 : RawSym := [(0, [[(-29931825:ℚ), (-3563041:ℚ), (-112761:ℚ), (-1391:ℚ), (-6:ℚ)], [(1619416:ℚ), (145607:ℚ), (3078:ℚ), (19:ℚ), (0:ℚ)], [(-32846:ℚ), (-1983:ℚ), (-21:ℚ), (0:ℚ), (0:ℚ)], [(296:ℚ), (9:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-44265375:ℚ), (-4645830:ℚ), (-101325:ℚ), (-630:ℚ)], [(506730:ℚ), (-7788:ℚ), (-1530:ℚ), (-18:ℚ)], [(26988:ℚ), (2730:ℚ), (39:ℚ), (0:ℚ)], [(-570:ℚ), (-24:ℚ), (0:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-20010375:ℚ), (-1826055:ℚ), (-20790:ℚ)], [(-651420:ℚ), (-83253:ℚ), (-1224:ℚ)], [(10218:ℚ), (-153:ℚ), (-18:ℚ)], [(252:ℚ), (21:ℚ), (0:ℚ)], [(-3:ℚ), (0:ℚ), (0:ℚ)]]),
 (6, [[(-2756985:ℚ), (-214830:ℚ)], [(-215446:ℚ), (-19578:ℚ)], [(-4360:ℚ), (-594:ℚ)], [(22:ℚ), (-6:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (7, [[(107452800:ℚ), (4031160:ℚ), (50400:ℚ), (210:ℚ)], [(-3519480:ℚ), (-81604:ℚ), (-390:ℚ), (1:ℚ)], [(31204:ℚ), (150:ℚ), (-3:ℚ), (0:ℚ)], [(30:ℚ), (3:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (9, [[(115718400:ℚ), (2857680:ℚ), (17640:ℚ)], [(1826160:ℚ), (80388:ℚ), (714:ℚ)], [(-78348:ℚ), (-942:ℚ), (3:ℚ)], [(228:ℚ), (-6:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (11, [[(37608480:ℚ), (458640:ℚ)], [(2510088:ℚ), (36204:ℚ)], [(28740:ℚ), (792:ℚ)], [(-546:ℚ), (3:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (13, [[(3669120:ℚ)], [(442512:ℚ)], [(18404:ℚ)], [(288:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache175_check : equalRawCheck
    (rawScale (rawFactor 7 77) wordCache22 ++
      rawScale (rawSecond 7) (rawShift 7 wordCache22)) wordCache175 = true := by
  decide +kernel

theorem wordCache175_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [7, 2, 2, 2]) = evalSym W k a (symMap wordCache175) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache22_sound W k a, wordCache22_sound W (k - (7 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache175_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
