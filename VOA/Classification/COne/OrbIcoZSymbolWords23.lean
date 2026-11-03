import VOA.Classification.COne.OrbIcoZSymbolWords22

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache184 : RawSym := [(0, [[(-2098741824:ℚ), (-221666544:ℚ), (-2612232:ℚ)], [(143435224:ℚ), (12222702:ℚ), (108857:ℚ)], [(-3920610:ℚ), (-252712:ℚ), (-1512:ℚ)], [(53575:ℚ), (2322:ℚ), (7:ℚ)], [(-366:ℚ), (-8:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(88679232:ℚ), (9366192:ℚ), (110376:ℚ)], [(-4811640:ℚ), (-384534:ℚ), (-3045:ℚ)], [(97890:ℚ), (5262:ℚ), (21:ℚ)], [(-885:ℚ), (-24:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-1077699000:ℚ), (-99261750:ℚ), (0:ℚ)], [(28316326:ℚ), (1318651:ℚ), (1533:ℚ)], [(-793241:ℚ), (-73021:ℚ), (-1554:ℚ)], [(27522:ℚ), (2249:ℚ), (21:ℚ)], [(-409:ℚ), (-17:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-88578000:ℚ), (-8158500:ℚ), (0:ℚ)], [(45312988:ℚ), (4066368:ℚ), (14:ℚ)], [(-469548:ℚ), (10025:ℚ), (-21:ℚ)], [(-22061:ℚ), (-1818:ℚ), (7:ℚ)], [(423:ℚ), (13:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-3591000:ℚ), (-330750:ℚ)], [(2985030:ℚ), (270585:ℚ)], [(-590187:ℚ), (-50799:ℚ)], [(-3003:ℚ), (-945:ℚ)], [(363:ℚ), (21:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (5, [[(-63840:ℚ), (-5880:ℚ)], [(68176:ℚ), (6202:ℚ)], [(-22850:ℚ), (-2023:ℚ)], [(2265:ℚ), (182:ℚ)], [(50:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-10284472800:ℚ), (-125420400:ℚ)], [(469150870:ℚ), (4191835:ℚ)], [(-7439117:ℚ), (-39601:ℚ)], [(40011:ℚ), (5:ℚ)], [(77:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (9, [[(-3124396800:ℚ), (-38102400:ℚ)], [(493527120:ℚ), (5553960:ℚ)], [(-13828662:ℚ), (-100911:ℚ)], [(119607:ℚ), (228:ℚ)], [(18:ℚ), (3:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (10, [[(-3998251530:ℚ), (-4286520:ℚ)], [(73664451:ℚ), (1047519:ℚ)], [(-3289589:ℚ), (-67683:ℚ)], [(63719:ℚ), (441:ℚ)], [(-169:ℚ), (3:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (11, [[(-1365115500:ℚ), (-176400:ℚ)], [(117251500:ℚ), (58570:ℚ)], [(2641885:ℚ), (-6373:ℚ)], [(-73338:ℚ), (218:ℚ)], [(155:ℚ), (1:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (12, [[(-181184850:ℚ)], [(29322705:ℚ)], [(-579222:ℚ)], [(-59460:ℚ)], [(504:ℚ)], [(3:ℚ)]]),
 (13, [[(-8731800:ℚ)], [(2035590:ℚ)], [(-121151:ℚ)], [(-1999:ℚ)], [(239:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache184_check : equalRawCheck
    (rawScale (rawFactor 8 76) wordCache13 ++
      rawScale (rawSecond 8) (rawShift 8 wordCache13)) wordCache184 = true := by
  decide +kernel

theorem wordCache184_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [8, 2, 1, 1, 1]) = evalSym W k a (symMap wordCache184) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache13_sound W k a, wordCache13_sound W (k - (8 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache184_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache185 : RawSym := [(0, [[(-28749888:ℚ), (-3435832:ℚ), (-77958:ℚ), (-497:ℚ)], [(1571032:ℚ), (142112:ℚ), (2163:ℚ), (7:ℚ)], [(-32186:ℚ), (-1959:ℚ), (-15:ℚ), (0:ℚ)], [(293:ℚ), (9:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(404928:ℚ), (48392:ℚ), (1098:ℚ), (7:ℚ)], [(-16424:ℚ), (-1320:ℚ), (-15:ℚ), (0:ℚ)], [(222:ℚ), (9:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-28738640:ℚ), (-3035340:ℚ), (-35770:ℚ)], [(339076:ℚ), (-4264:ℚ), (-532:ℚ)], [(17538:ℚ), (1796:ℚ), (14:ℚ)], [(-376:ℚ), (-16:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-787360:ℚ), (-83160:ℚ), (-980:ℚ)], [(392184:ℚ), (40324:ℚ), (462:ℚ)], [(1208:ℚ), (660:ℚ), (14:ℚ)], [(-234:ℚ), (-16:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-6583500:ℚ), (-606375:ℚ)], [(-213195:ℚ), (-27615:ℚ)], [(3413:ℚ), (-49:ℚ)], [(83:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(-351120:ℚ), (-32340:ℚ)], [(71728:ℚ), (6181:ℚ)], [(3981:ℚ), (448:ℚ)], [(12:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-126968800:ℚ), (-3135510:ℚ), (-19355:ℚ)], [(4224470:ℚ), (65602:ℚ), (166:ℚ)], [(-39687:ℚ), (-170:ℚ), (1:ℚ)], [(4:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (9, [[(-12857600:ℚ), (-317520:ℚ), (-1960:ℚ)], [(1872240:ℚ), (42314:ℚ), (237:ℚ)], [(-33794:ℚ), (-312:ℚ), (1:ℚ)], [(75:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (10, [[(-87873660:ℚ), (-1071630:ℚ)], [(-1456758:ℚ), (-30834:ℚ)], [(62158:ℚ), (382:ℚ)], [(-218:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (11, [[(-10848600:ℚ), (-132300:ℚ)], [(771080:ℚ), (7790:ℚ)], [(35178:ℚ), (524:ℚ)], [(-360:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (12, [[(-13726125:ℚ)], [(-948070:ℚ)], [(-11236:ℚ)], [(214:ℚ)], [(1:ℚ)]]),
 (13, [[(-1984500:ℚ)], [(4395:ℚ)], [(9851:ℚ)], [(285:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache185_check : equalRawCheck
    (rawScale (rawFactor 8 76) wordCache14 ++
      rawScale (rawSecond 8) (rawShift 8 wordCache14)) wordCache185 = true := by
  decide +kernel

theorem wordCache185_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [8, 2, 2, 1]) = evalSym W k a (symMap wordCache185) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache14_sound W k a, wordCache14_sound W (k - (8 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache185_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache186 : RawSym := [(0, [[(-28361376:ℚ), (-3389256:ℚ), (-71568:ℚ)], [(1555052:ℚ), (140817:ℚ), (2002:ℚ)], [(-31967:ℚ), (-1950:ℚ), (-14:ℚ)], [(292:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(798912:ℚ), (95472:ℚ), (2016:ℚ)], [(-32552:ℚ), (-2622:ℚ), (-28:ℚ)], [(442:ℚ), (18:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5548:ℚ), (663:ℚ), (14:ℚ)], [(-5697:ℚ), (-672:ℚ), (-14:ℚ)], [(150:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(29526000:ℚ), (2719500:ℚ)], [(-759380:ℚ), (-34160:ℚ)], [(-1124:ℚ), (-553:ℚ)], [(155:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(2394000:ℚ), (220500:ℚ)], [(-827220:ℚ), (-73290:ℚ)], [(9254:ℚ), (-112:ℚ)], [(168:ℚ), (14:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (5, [[(63840:ℚ), (5880:ℚ)], [(-37168:ℚ), (-3346:ℚ)], [(5266:ℚ), (441:ℚ)], [(13:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-125420400:ℚ), (-3096800:ℚ)], [(4191835:ℚ), (65270:ℚ)], [(-39601:ℚ), (-172:ℚ)], [(5:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (9, [[(-25401600:ℚ), (-627200:ℚ)], [(3702640:ℚ), (83680:ℚ)], [(-67274:ℚ), (-628:ℚ)], [(152:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (10, [[(-1428840:ℚ), (-35280:ℚ)], [(349173:ℚ), (8186:ℚ)], [(-22561:ℚ), (-456:ℚ)], [(147:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (11, [[(103383140:ℚ)], [(-416908:ℚ)], [(-28659:ℚ)], [(142:ℚ)], [(1:ℚ)]]),
 (12, [[(27736940:ℚ)], [(-2295138:ℚ)], [(-25510:ℚ)], [(426:ℚ)], [(2:ℚ)]]),
 (13, [[(2005080:ℚ)], [(-308846:ℚ)], [(8261:ℚ)], [(284:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache186_check : equalRawCheck
    (rawScale (rawFactor 8 76) wordCache15 ++
      rawScale (rawSecond 8) (rawShift 8 wordCache15)) wordCache186 = true := by
  decide +kernel

theorem wordCache186_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [8, 3, 1, 1]) = evalSym W k a (symMap wordCache186) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache15_sound W k a, wordCache15_sound W (k - (8 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache186_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache187 : RawSym := [(0, [[(-393908:ℚ), (-52621:ℚ), (-1657:ℚ), (-14:ℚ)], [(16127:ℚ), (1451:ℚ), (23:ℚ), (0:ℚ)], [(-220:ℚ), (-10:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-194180:ℚ), (-23205:ℚ), (-490:ℚ)], [(-333:ℚ), (-348:ℚ), (-14:ℚ)], [(114:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(393680:ℚ), (41580:ℚ), (490:ℚ)], [(-4876:ℚ), (34:ℚ), (7:ℚ)], [(-80:ℚ), (-8:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(170240:ℚ), (15680:ℚ)], [(5512:ℚ), (714:ℚ)], [(-26:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-1567755:ℚ), (-58555:ℚ), (-490:ℚ)], [(32801:ℚ), (496:ℚ), (-2:ℚ)], [(-85:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (10, [[(-535815:ℚ), (-13230:ℚ)], [(-15417:ℚ), (-544:ℚ)], [(191:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (11, [[(1245580:ℚ), (15190:ℚ)], [(9984:ℚ), (307:ℚ)], [(-225:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (13, [[(364560:ℚ)], [(22558:ℚ)], [(331:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache187_check : equalRawCheck
    (rawScale (rawFactor 8 76) wordCache16 ++
      rawScale (rawSecond 8) (rawShift 8 wordCache16)) wordCache187 = true := by
  decide +kernel

theorem wordCache187_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [8, 3, 2]) = evalSym W k a (symMap wordCache187) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache16_sound W k a, wordCache16_sound W (k - (8 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache187_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache188 : RawSym := [(0, [[(-388512:ℚ), (-51972:ℚ), (-1491:ℚ)], [(15980:ℚ), (1442:ℚ), (21:ℚ)], [(-219:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5472:ℚ), (732:ℚ), (21:ℚ)], [(-148:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-598500:ℚ), (-55125:ℚ)], [(10155:ℚ), (210:ℚ)], [(46:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(-31920:ℚ), (-2940:ℚ)], [(8096:ℚ), (707:ℚ)], [(-25:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-1548400:ℚ), (-58065:ℚ)], [(32635:ℚ), (498:ℚ)], [(-86:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (9, [[(-156800:ℚ), (-5880:ℚ)], [(20920:ℚ), (711:ℚ)], [(-157:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (12, [[(-1972495:ℚ)], [(-4621:ℚ)], [(259:ℚ)], [(1:ℚ)]]),
 (13, [[(-285180:ℚ)], [(19661:ℚ)], [(330:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache188_check : equalRawCheck
    (rawScale (rawFactor 8 76) wordCache17 ++
      rawScale (rawSecond 8) (rawShift 8 wordCache17)) wordCache188 = true := by
  decide +kernel

theorem wordCache188_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [8, 4, 1]) = evalSym W k a (symMap wordCache188) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache17_sound W k a, wordCache17_sound W (k - (8 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache188_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache189 : RawSym := [(0, [[(-5396:ℚ), (-801:ℚ), (-28:ℚ)], [(147:ℚ), (11:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (5, [[(10640:ℚ), (980:ℚ)], [(-64:ℚ), (7:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (8, [[(-19355:ℚ), (-980:ℚ)], [(166:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (13, [[(32340:ℚ)], [(377:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache189_check : equalRawCheck
    (rawScale (rawFactor 8 76) wordCache18 ++
      rawScale (rawSecond 8) (rawShift 8 wordCache18)) wordCache189 = true := by
  decide +kernel

theorem wordCache189_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [8, 5]) = evalSym W k a (symMap wordCache189) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache18_sound W k a, wordCache18_sound W (k - (8 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache189_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache190 : RawSym := [(0, [[(-2071126800:ℚ), (-220920192:ℚ)], [(141911274:ℚ), (12191600:ℚ)], [(-3889075:ℚ), (-252280:ℚ)], [(53285:ℚ), (2320:ℚ)], [(-365:ℚ), (-8:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(116683200:ℚ), (12446208:ℚ)], [(-6351576:ℚ), (-511552:ℚ)], [(129644:ℚ), (7008:ℚ)], [(-1176:ℚ), (-32:ℚ)], [(4:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(2430900:ℚ), (259296:ℚ)], [(-2529462:ℚ), (-266352:ℚ)], [(99894:ℚ), (7104:ℚ)], [(-1338:ℚ), (-48:ℚ)], [(6:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(44400:ℚ), (4736:ℚ)], [(-67792:ℚ), (-7168:ℚ)], [(23996:ℚ), (2464:ℚ)], [(-608:ℚ), (-32:ℚ)], [(4:ℚ), (0:ℚ)]]),
 (4, [[(0:ℚ), (0:ℚ)], [(450:ℚ), (48:ℚ)], [(-831:ℚ), (-88:ℚ)], [(461:ℚ), (48:ℚ)], [(-81:ℚ), (-8:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (9, [[(12348806400:ℚ)], [(-562087600:ℚ)], [(8993314:ℚ)], [(-51429:ℚ)], [(-46:ℚ)], [(1:ℚ)]]),
 (10, [[(5556962880:ℚ)], [(-800917704:ℚ)], [(22139900:ℚ)], [(-196060:ℚ)], [(100:ℚ)], [(4:ℚ)]]),
 (11, [[(1029067200:ℚ)], [(-238520280:ℚ)], [(15987096:ℚ)], [(-248934:ℚ)], [(576:ℚ)], [(6:ℚ)]]),
 (12, [[(92030400:ℚ)], [(-28575160:ℚ)], [(3020452:ℚ)], [(-115404:ℚ)], [(668:ℚ)], [(4:ℚ)]]),
 (13, [[(3326400:ℚ)], [(-1269960:ℚ)], [(179942:ℚ)], [(-11101:ℚ)], [(238:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache190_check : equalRawCheck
    (rawScale (rawFactor 9 75) wordCache7 ++
      rawScale (rawSecond 9) (rawShift 9 wordCache7)) wordCache190 = true := by
  decide +kernel

theorem wordCache190_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [9, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache190) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache7_sound W k a, wordCache7_sound W (k - (9 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache190_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache191 : RawSym := [(0, [[(-27988200:ℚ), (-3368808:ℚ), (-40896:ℚ)], [(1539501:ℚ), (140245:ℚ), (1144:ℚ)], [(-31751:ℚ), (-1946:ℚ), (-8:ℚ)], [(291:ℚ), (9:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(788400:ℚ), (94896:ℚ), (1152:ℚ)], [(-32262:ℚ), (-2614:ℚ), (-16:ℚ)], [(440:ℚ), (18:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-14180250:ℚ), (-1512560:ℚ), (0:ℚ)], [(175270:ℚ), (-1397:ℚ), (8:ℚ)], [(3034:ℚ), (228:ℚ), (-8:ℚ)], [(-38:ℚ), (1:ℚ), (0:ℚ)]]),
 (3, [[(-777000:ℚ), (-82880:ℚ)], [(387160:ℚ), (40192:ℚ)], [(1126:ℚ), (656:ℚ)], [(-232:ℚ), (-16:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (4, [[(-15750:ℚ), (-1680:ℚ)], [(12885:ℚ), (1352:ℚ)], [(-2419:ℚ), (-240:ℚ)], [(-45:ℚ), (-8:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (9, [[(148780800:ℚ), (1814400:ℚ)], [(-4979600:ℚ), (-38600:ℚ)], [(48358:ℚ), (119:ℚ)], [(-37:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (10, [[(33475680:ℚ), (408240:ℚ)], [(-4421484:ℚ), (-48942:ℚ)], [(80102:ℚ), (380:ℚ)], [(-216:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (11, [[(51614080:ℚ), (25200:ℚ)], [(427376:ℚ), (-5230:ℚ)], [(-9772:ℚ), (261:ℚ)], [(-38:ℚ), (1:ℚ)]]),
 (12, [[(13293280:ℚ)], [(-809884:ℚ)], [(-41142:ℚ)], [(424:ℚ)], [(2:ℚ)]]),
 (13, [[(960960:ℚ)], [(-127048:ℚ)], [(374:ℚ)], [(283:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache191_check : equalRawCheck
    (rawScale (rawFactor 9 75) wordCache8 ++
      rawScale (rawSecond 9) (rawShift 9 wordCache8)) wordCache191 = true := by
  decide +kernel

theorem wordCache191_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [9, 2, 1, 1]) = evalSym W k a (symMap wordCache191) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache8_sound W k a, wordCache8_sound W (k - (9 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache191_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
