import VOA.Classification.COne.OrbIcoZSymbolWords03

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache32 : RawSym := [(0, [[(-2098741824:ℚ), (-55976400:ℚ), (-373176:ℚ)], [(143435224:ℚ), (3079002:ℚ), (15551:ℚ)], [(-3920610:ℚ), (-63502:ℚ), (-216:ℚ)], [(53575:ℚ), (582:ℚ), (1:ℚ)], [(-366:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(88679232:ℚ), (2365200:ℚ), (15768:ℚ)], [(-4811640:ℚ), (-96786:ℚ), (-435:ℚ)], [(97890:ℚ), (1320:ℚ), (3:ℚ)], [(-885:ℚ), (-6:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-2155398000:ℚ), (-28360500:ℚ), (0:ℚ)], [(55400996:ℚ), (372440:ℚ), (219:ℚ)], [(-305104:ℚ), (-16424:ℚ), (-222:ℚ)], [(4653:ℚ), (520:ℚ), (3:ℚ)], [(-146:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-177156000:ℚ), (-2331000:ℚ), (0:ℚ)], [(90614728:ℚ), (1161780:ℚ), (2:ℚ)], [(-921924:ℚ), (2924:ℚ), (-3:ℚ)], [(-50198:ℚ), (-540:ℚ), (1:ℚ)], [(999:ℚ), (4:ℚ), (0:ℚ)], [(-5:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-514111500:ℚ), (-94500:ℚ)], [(-3862455:ℚ), (77310:ℚ)], [(-704378:ℚ), (-14514:ℚ)], [(-3028:ℚ), (-270:ℚ)], [(566:ℚ), (6:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (5, [[(-81236400:ℚ), (-1680:ℚ)], [(17758880:ℚ), (1772:ℚ)], [(658727:ℚ), (-578:ℚ)], [(-4641:ℚ), (52:ℚ)], [(-167:ℚ), (2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (6, [[(-5336100:ℚ)], [(2156385:ℚ)], [(-157158:ℚ)], [(-11940:ℚ)], [(-54:ℚ)], [(3:ℚ)]]),
 (7, [[(-138600:ℚ)], [(77310:ℚ)], [(-12413:ℚ)], [(209:ℚ)], [(53:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache32_check : equalRawCheck
    (rawScale (rawFactor 2 76) wordCache13 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache13)) wordCache32 = true := by
  decide +kernel

theorem wordCache32_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 1, 1, 1]) = evalSym W k a (symMap wordCache32) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache13_sound W k a, wordCache13_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache32_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache33 : RawSym := [(0, [[(-28749888:ℚ), (-1166104:ℚ), (-15762:ℚ), (-71:ℚ)], [(1571032:ℚ), (47948:ℚ), (435:ℚ), (1:ℚ)], [(-32186:ℚ), (-657:ℚ), (-3:ℚ), (0:ℚ)], [(293:ℚ), (3:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)], [(404928:ℚ), (16424:ℚ), (222:ℚ), (1:ℚ)], [(-16424:ℚ), (-444:ℚ), (-3:ℚ), (0:ℚ)], [(222:ℚ), (3:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-43107960:ℚ), (-1149750:ℚ), (-7665:ℚ)], [(508614:ℚ), (-1770:ℚ), (-114:ℚ)], [(26307:ℚ), (678:ℚ), (3:ℚ)], [(-564:ℚ), (-6:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-1181040:ℚ), (-31500:ℚ), (-210:ℚ)], [(588276:ℚ), (15270:ℚ), (99:ℚ)], [(1812:ℚ), (252:ℚ), (3:ℚ)], [(-351:ℚ), (-6:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-19750500:ℚ), (-259875:ℚ)], [(-639585:ℚ), (-11835:ℚ)], [(10239:ℚ), (-21:ℚ)], [(249:ℚ), (3:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (5, [[(-1053360:ℚ), (-13860:ℚ)], [(215184:ℚ), (2649:ℚ)], [(11943:ℚ), (192:ℚ)], [(36:ℚ), (3:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (6, [[(-2756985:ℚ)], [(-215446:ℚ)], [(-4360:ℚ)], [(22:ℚ)], [(1:ℚ)]]),
 (7, [[(-214830:ℚ)], [(16227:ℚ)], [(2669:ℚ)], [(93:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache33_check : equalRawCheck
    (rawScale (rawFactor 2 76) wordCache14 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache14)) wordCache33 = true := by
  decide +kernel

theorem wordCache33_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 2, 1]) = evalSym W k a (symMap wordCache33) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache14_sound W k a, wordCache14_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache33_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache34 : RawSym := [(0, [[(-2071126800:ℚ), (-55230048:ℚ)], [(141911274:ℚ), (3047900:ℚ)], [(-3889075:ℚ), (-63070:ℚ)], [(53285:ℚ), (580:ℚ)], [(-365:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(116683200:ℚ), (3111552:ℚ)], [(-6351576:ℚ), (-127888:ℚ)], [(129644:ℚ), (1752:ℚ)], [(-1176:ℚ), (-8:ℚ)], [(4:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(2430900:ℚ), (64824:ℚ)], [(-2529462:ℚ), (-66588:ℚ)], [(99894:ℚ), (1776:ℚ)], [(-1338:ℚ), (-12:ℚ)], [(6:ℚ), (0:ℚ)]]),
 (3, [[(2273502000:ℚ), (0:ℚ)], [(-87953860:ℚ), (1184:ℚ)], [(605040:ℚ), (-1792:ℚ)], [(37055:ℚ), (616:ℚ)], [(-840:ℚ), (-8:ℚ)], [(5:ℚ), (0:ℚ)]]),
 (4, [[(368676000:ℚ), (0:ℚ)], [(-132179430:ℚ), (12:ℚ)], [(3078725:ℚ), (-22:ℚ)], [(7825:ℚ), (12:ℚ)], [(-725:ℚ), (-2:ℚ)], [(5:ℚ), (0:ℚ)]]),
 (5, [[(29494080:ℚ)], [(-17554656:ℚ)], [(2655900:ℚ)], [(-25590:ℚ)], [(-540:ℚ)], [(6:ℚ)]]),
 (6, [[(1293600:ℚ)], [(-1011640:ℚ)], [(257164:ℚ)], [(-21036:ℚ)], [(-76:ℚ)], [(4:ℚ)]]),
 (7, [[(25200:ℚ)], [(-23580:ℚ)], [(7988:ℚ)], [(-1141:ℚ)], [(52:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache34_check : equalRawCheck
    (rawScale (rawFactor 3 75) wordCache7 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache7)) wordCache34 = true := by
  decide +kernel

theorem wordCache34_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache34) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache7_sound W k a, wordCache7_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache34_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache35 : RawSym := [(0, [[(-27988200:ℚ), (-1129752:ℚ), (-10224:ℚ)], [(1539501:ℚ), (46939:ℚ), (286:ℚ)], [(-31751:ℚ), (-650:ℚ), (-2:ℚ)], [(291:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(788400:ℚ), (31824:ℚ), (288:ℚ)], [(-32262:ℚ), (-874:ℚ), (-4:ℚ)], [(440:ℚ), (6:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-14180250:ℚ), (-378140:ℚ), (0:ℚ)], [(175270:ℚ), (-293:ℚ), (2:ℚ)], [(3034:ℚ), (0:ℚ), (-2:ℚ)], [(-38:ℚ), (1:ℚ), (0:ℚ)]]),
 (3, [[(28749000:ℚ), (367780:ℚ)], [(-372220:ℚ), (5168:ℚ)], [(2:ℚ), (85:ℚ)], [(-77:ℚ), (-3:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (4, [[(2378250:ℚ), (31080:ℚ)], [(-814335:ℚ), (-10132:ℚ)], [(6835:ℚ), (-76:ℚ)], [(123:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(13172320:ℚ), (840:ℚ)], [(217016:ℚ), (-478:ℚ)], [(-2248:ℚ), (63:ℚ)], [(-38:ℚ), (1:ℚ)]]),
 (6, [[(1724800:ℚ)], [(-288820:ℚ)], [(-11478:ℚ)], [(40:ℚ)], [(2:ℚ)]]),
 (7, [[(67200:ℚ)], [(-21580:ℚ)], [(1148:ℚ)], [(91:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache35_check : equalRawCheck
    (rawScale (rawFactor 3 75) wordCache8 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache8)) wordCache35 = true := by
  decide +kernel

theorem wordCache35_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 2, 1, 1]) = evalSym W k a (symMap wordCache35) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache8_sound W k a, wordCache8_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache35_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache36 : RawSym := [(0, [[(-388725:ℚ), (-21166:ℚ), (-363:ℚ), (-2:ℚ)], [(15983:ℚ), (582:ℚ), (5:ℚ), (0:ℚ)], [(-219:ℚ), (-4:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-383250:ℚ), (-15470:ℚ), (-140:ℚ)], [(-590:ℚ), (-232:ℚ), (-4:ℚ)], [(226:ℚ), (6:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(393680:ℚ), (10500:ℚ), (70:ℚ)], [(-4876:ℚ), (10:ℚ), (1:ℚ)], [(-80:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-86625:ℚ), (-2310:ℚ)], [(-3945:ℚ), (-136:ℚ)], [(-7:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(340480:ℚ), (4480:ℚ)], [(11024:ℚ), (204:ℚ)], [(-52:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (7, [[(67200:ℚ)], [(5300:ℚ)], [(132:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache36_check : equalRawCheck
    (rawScale (rawFactor 3 75) wordCache9 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache9)) wordCache36 = true := by
  decide +kernel

theorem wordCache36_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 2, 2]) = evalSym W k a (symMap wordCache36) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache9_sound W k a, wordCache9_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache36_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache37 : RawSym := [(0, [[(-383400:ℚ), (-20874:ℚ), (-284:ℚ)], [(15837:ℚ), (578:ℚ), (4:ℚ)], [(-218:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5400:ℚ), (294:ℚ), (4:ℚ)], [(-147:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(777000:ℚ), (20720:ℚ)], [(-9760:ℚ), (16:ℚ)], [(-158:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (4, [[(31500:ℚ), (840:ℚ)], [(-10470:ℚ), (-268:ℚ)], [(-16:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (6, [[(-361130:ℚ)], [(-5859:ℚ)], [(60:ℚ)], [(1:ℚ)]]),
 (7, [[(-28140:ℚ)], [(3868:ℚ)], [(131:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache37_check : equalRawCheck
    (rawScale (rawFactor 3 75) wordCache10 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache10)) wordCache37 = true := by
  decide +kernel

theorem wordCache37_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 3, 1]) = evalSym W k a (symMap wordCache37) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache10_sound W k a, wordCache10_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache37_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache38 : RawSym := [(0, [[(-27615024:ℚ), (-1119528:ℚ)], [(1523950:ℚ), (46653:ℚ)], [(-31535:ℚ), (-648:ℚ)], [(290:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(1166832:ℚ), (47304:ℚ)], [(-47958:ℚ), (-1305:ℚ)], [(657:ℚ), (9:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(16206:ℚ), (657:ℚ)], [(-16647:ℚ), (-666:ℚ)], [(444:ℚ), (9:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(148:ℚ), (6:ℚ)], [(-224:ℚ), (-9:ℚ)], [(77:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(-46084500:ℚ)], [(1380435:ℚ)], [(-6613:ℚ)], [(-123:ℚ)], [(1:ℚ)]]),
 (5, [[(-7373520:ℚ)], [(1965936:ℚ)], [(-30063:ℚ)], [(-156:ℚ)], [(3:ℚ)]]),
 (6, [[(-485100:ℚ)], [(219975:ℚ)], [(-24951:ℚ)], [(57:ℚ)], [(3:ℚ)]]),
 (7, [[(-12600:ℚ)], [(7650:ℚ)], [(-1501:ℚ)], [(90:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache38_check : equalRawCheck
    (rawScale (rawFactor 4 74) wordCache4 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache4)) wordCache38 = true := by
  decide +kernel

theorem wordCache38_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 1, 1, 1]) = evalSym W k a (symMap wordCache38) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache4_sound W k a, wordCache4_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache38_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache39 : RawSym := [(0, [[(-378288:ℚ), (-20590:ℚ), (-213:ℚ)], [(15694:ℚ), (574:ℚ), (3:ℚ)], [(-217:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5328:ℚ), (290:ℚ), (3:ℚ)], [(-146:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-189070:ℚ), (-7665:ℚ)], [(-257:ℚ), (-114:ℚ)], [(112:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (3, [[(-5180:ℚ), (-210:ℚ)], [(2512:ℚ), (99:ℚ)], [(41:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(-598500:ℚ), (-7875:ℚ)], [(10155:ℚ), (30:ℚ)], [(46:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(-31920:ℚ), (-420:ℚ)], [(8096:ℚ), (101:ℚ)], [(-25:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(-250635:ℚ)], [(-7217:ℚ)], [(59:ℚ)], [(1:ℚ)]]),
 (7, [[(-19530:ℚ)], [(2439:ℚ)], [(130:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache39_check : equalRawCheck
    (rawScale (rawFactor 4 74) wordCache5 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache5)) wordCache39 = true := by
  decide +kernel

theorem wordCache39_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 2, 1]) = evalSym W k a (symMap wordCache39) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache5_sound W k a, wordCache5_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache39_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
