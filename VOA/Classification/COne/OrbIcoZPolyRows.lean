import VOA.Classification.COne.OrbIcoZEliminate

/-! Genuine polynomial skew and circle relations, before conformal specialization. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def polySkew70 : ModeRel := [(70, [mkRat (2) 1])]

set_option maxHeartbeats 4000000 in
theorem polySkew70_holds : evalRel Wi selfMode polySkew70 = 0 := by
  have h := selfMode_skew (70) (by omega)
  change selfMode (70) = sgn (71) •
    ∑ i ∈ Finset.range 1, cbz 0 (i : ℤ) • selfMode (70 + i) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [polySkew70, evalRel, zp, mkRat]
  module

def polySkew62 : ModeRel := [(62, [mkRat (2) 1]),
 (63, [mkRat (8) 1]),
 (64, [mkRat (28) 1]),
 (65, [mkRat (56) 1]),
 (66, [mkRat (70) 1]),
 (67, [mkRat (56) 1]),
 (68, [mkRat (28) 1]),
 (69, [mkRat (8) 1]),
 (70, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polySkew62_holds : evalRel Wi selfMode polySkew62 = 0 := by
  have h := selfMode_skew (62) (by omega)
  change selfMode (62) = sgn (63) •
    ∑ i ∈ Finset.range 9, cbz 8 (i : ℤ) • selfMode (62 + i) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [polySkew62, evalRel, zp, mkRat]
  module

def polySkew46 : ModeRel := [(46, [mkRat (2) 1]),
 (47, [mkRat (24) 1]),
 (48, [mkRat (276) 1]),
 (49, [mkRat (2024) 1]),
 (50, [mkRat (10626) 1]),
 (51, [mkRat (42504) 1]),
 (52, [mkRat (134596) 1]),
 (53, [mkRat (346104) 1]),
 (54, [mkRat (735471) 1]),
 (55, [mkRat (1307504) 1]),
 (56, [mkRat (1961256) 1]),
 (57, [mkRat (2496144) 1]),
 (58, [mkRat (2704156) 1]),
 (59, [mkRat (2496144) 1]),
 (60, [mkRat (1961256) 1]),
 (61, [mkRat (1307504) 1]),
 (62, [mkRat (735471) 1]),
 (63, [mkRat (346104) 1]),
 (64, [mkRat (134596) 1]),
 (65, [mkRat (42504) 1]),
 (66, [mkRat (10626) 1]),
 (67, [mkRat (2024) 1]),
 (68, [mkRat (276) 1]),
 (69, [mkRat (24) 1]),
 (70, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polySkew46_holds : evalRel Wi selfMode polySkew46 = 0 := by
  have h := selfMode_skew (46) (by omega)
  change selfMode (46) = sgn (47) •
    ∑ i ∈ Finset.range 25, cbz 24 (i : ℤ) • selfMode (46 + i) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [polySkew46, evalRel, zp, mkRat]
  module

def polySkew22 : ModeRel := [(22, [mkRat (2) 1]),
 (23, [mkRat (48) 1]),
 (24, [mkRat (1128) 1]),
 (25, [mkRat (17296) 1]),
 (26, [mkRat (194580) 1]),
 (27, [mkRat (1712304) 1]),
 (28, [mkRat (12271512) 1]),
 (29, [mkRat (73629072) 1]),
 (30, [mkRat (377348994) 1]),
 (31, [mkRat (1677106640) 1]),
 (32, [mkRat (6540715896) 1]),
 (33, [mkRat (22595200368) 1]),
 (34, [mkRat (69668534468) 1]),
 (35, [mkRat (192928249296) 1]),
 (36, [mkRat (482320623240) 1]),
 (37, [mkRat (1093260079344) 1]),
 (38, [mkRat (2254848913647) 1]),
 (39, [mkRat (4244421484512) 1]),
 (40, [mkRat (7309837001104) 1]),
 (41, [mkRat (11541847896480) 1]),
 (42, [mkRat (16735679449896) 1]),
 (43, [mkRat (22314239266528) 1]),
 (44, [mkRat (27385657281648) 1]),
 (45, [mkRat (30957699535776) 1]),
 (46, [mkRat (32247603683100) 1]),
 (47, [mkRat (30957699535776) 1]),
 (48, [mkRat (27385657281648) 1]),
 (49, [mkRat (22314239266528) 1]),
 (50, [mkRat (16735679449896) 1]),
 (51, [mkRat (11541847896480) 1]),
 (52, [mkRat (7309837001104) 1]),
 (53, [mkRat (4244421484512) 1]),
 (54, [mkRat (2254848913647) 1]),
 (55, [mkRat (1093260079344) 1]),
 (56, [mkRat (482320623240) 1]),
 (57, [mkRat (192928249296) 1]),
 (58, [mkRat (69668534468) 1]),
 (59, [mkRat (22595200368) 1]),
 (60, [mkRat (6540715896) 1]),
 (61, [mkRat (1677106640) 1]),
 (62, [mkRat (377348994) 1]),
 (63, [mkRat (73629072) 1]),
 (64, [mkRat (12271512) 1]),
 (65, [mkRat (1712304) 1]),
 (66, [mkRat (194580) 1]),
 (67, [mkRat (17296) 1]),
 (68, [mkRat (1128) 1]),
 (69, [mkRat (48) 1]),
 (70, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polySkew22_holds : evalRel Wi selfMode polySkew22 = 0 := by
  have h := selfMode_skew (22) (by omega)
  change selfMode (22) = sgn (23) •
    ∑ i ∈ Finset.range 49, cbz 48 (i : ℤ) • selfMode (22 + i) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [polySkew22, evalRel, zp, mkRat]
  module

def polySkewneg10 : ModeRel := [(-10, [mkRat (2) 1]),
 (-9, [mkRat (80) 1]),
 (-8, [mkRat (3160) 1]),
 (-7, [mkRat (82160) 1]),
 (-6, [mkRat (1581580) 1]),
 (-5, [mkRat (24040016) 1]),
 (-4, [mkRat (300500200) 1]),
 (-3, [mkRat (3176716400) 1]),
 (-2, [mkRat (28987537150) 1]),
 (-1, [mkRat (231900297200) 1]),
 (0, [mkRat (1646492110120) 1]),
 (1, [mkRat (10477677064400) 1]),
 (2, [mkRat (60246643120300) 1]),
 (3, [mkRat (315136287090800) 1]),
 (4, [mkRat (1508152231077400) 1]),
 (5, [mkRat (6635869816740560) 1]),
 (6, [mkRat (26958221130508525) 1]),
 (7, [mkRat (101489773667796800) 1]),
 (8, [mkRat (355214207837288800) 1]),
 (9, [mkRat (1159120046626942400) 1]),
 (10, [mkRat (3535316142212174320) 1]),
 (11, [mkRat (10100903263463355200) 1]),
 (12, [mkRat (27088786024742634400) 1]),
 (13, [mkRat (68310851714568382400) 1]),
 (14, [mkRat (162238272822099908200) 1]),
 (15, [mkRat (363413731121503794368) 1]),
 (16, [mkRat (768759815833950334240) 1]),
 (17, [mkRat (1537519631667900668480) 1]),
 (18, [mkRat (2910305017085669122480) 1]),
 (19, [mkRat (5218477961670854978240) 1]),
 (20, [mkRat (8871412534840453463008) 1]),
 (21, [mkRat (14308729894903957198400) 1]),
 (22, [mkRat (21910242651571684460050) 1]),
 (23, [mkRat (31869443856831541032800) 1]),
 (24, [mkRat (44054819449149483192400) 1]),
 (25, [mkRat (57900619847453606481440) 1]),
 (26, [mkRat (72375774809317008101800) 1]),
 (27, [mkRat (86068488962431036661600) 1]),
 (28, [mkRat (97393290141698278327600) 1]),
 (29, [mkRat (104885081691059684352800) 1]),
 (30, [mkRat (107507208733336176461620) 1]),
 (31, [mkRat (104885081691059684352800) 1]),
 (32, [mkRat (97393290141698278327600) 1]),
 (33, [mkRat (86068488962431036661600) 1]),
 (34, [mkRat (72375774809317008101800) 1]),
 (35, [mkRat (57900619847453606481440) 1]),
 (36, [mkRat (44054819449149483192400) 1]),
 (37, [mkRat (31869443856831541032800) 1]),
 (38, [mkRat (21910242651571684460050) 1]),
 (39, [mkRat (14308729894903957198400) 1]),
 (40, [mkRat (8871412534840453463008) 1]),
 (41, [mkRat (5218477961670854978240) 1]),
 (42, [mkRat (2910305017085669122480) 1]),
 (43, [mkRat (1537519631667900668480) 1]),
 (44, [mkRat (768759815833950334240) 1]),
 (45, [mkRat (363413731121503794368) 1]),
 (46, [mkRat (162238272822099908200) 1]),
 (47, [mkRat (68310851714568382400) 1]),
 (48, [mkRat (27088786024742634400) 1]),
 (49, [mkRat (10100903263463355200) 1]),
 (50, [mkRat (3535316142212174320) 1]),
 (51, [mkRat (1159120046626942400) 1]),
 (52, [mkRat (355214207837288800) 1]),
 (53, [mkRat (101489773667796800) 1]),
 (54, [mkRat (26958221130508525) 1]),
 (55, [mkRat (6635869816740560) 1]),
 (56, [mkRat (1508152231077400) 1]),
 (57, [mkRat (315136287090800) 1]),
 (58, [mkRat (60246643120300) 1]),
 (59, [mkRat (10477677064400) 1]),
 (60, [mkRat (1646492110120) 1]),
 (61, [mkRat (231900297200) 1]),
 (62, [mkRat (28987537150) 1]),
 (63, [mkRat (3176716400) 1]),
 (64, [mkRat (300500200) 1]),
 (65, [mkRat (24040016) 1]),
 (66, [mkRat (1581580) 1]),
 (67, [mkRat (82160) 1]),
 (68, [mkRat (3160) 1]),
 (69, [mkRat (80) 1]),
 (70, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polySkewneg10_holds : evalRel Wi selfMode polySkewneg10 = 0 := by
  have h := selfMode_skew (-10) (by omega)
  change selfMode (-10) = sgn (-9) •
    ∑ i ∈ Finset.range 81, cbz 80 (i : ℤ) • selfMode (-10 + i) at h
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial, sgn] at h
  convert sub_eq_zero.mpr h using 1
  norm_num [polySkewneg10, evalRel, zp, mkRat]
  module

def polyCircle1 : ModeRel := [(-3, [mkRat (1) 1]),
 (-2, [mkRat (36) 1]),
 (-1, [mkRat (630) 1]),
 (0, [mkRat (7140) 1]),
 (1, [mkRat (58905) 1]),
 (2, [mkRat (376992) 1]),
 (3, [mkRat (1947792) 1]),
 (4, [mkRat (8347680) 1]),
 (5, [mkRat (30260340) 1]),
 (6, [mkRat (94143280) 1]),
 (7, [mkRat (254186856) 1]),
 (8, [mkRat (600805296) 1]),
 (9, [mkRat (1251677700) 1]),
 (10, [mkRat (2310789600) 1]),
 (11, [mkRat (3796297200) 1]),
 (12, [mkRat (5567902560) 1]),
 (13, [mkRat (7307872110) 1]),
 (14, [mkRat (8597496600) 1]),
 (15, [mkRat (9075135300) 1]),
 (16, [mkRat (8597496600) 1]),
 (17, [mkRat (7307872110) 1]),
 (18, [mkRat (5567902560) 1]),
 (19, [mkRat (3796297200) 1]),
 (20, [mkRat (2310789600) 1]),
 (21, [mkRat (1251677700) 1]),
 (22, [mkRat (600805296) 1]),
 (23, [mkRat (254186856) 1]),
 (24, [mkRat (94143280) 1]),
 (25, [mkRat (30260340) 1]),
 (26, [mkRat (8347680) 1]),
 (27, [mkRat (1947792) 1]),
 (28, [mkRat (376992) 1]),
 (29, [mkRat (58905) 1]),
 (30, [mkRat (7140) 1]),
 (31, [mkRat (630) 1]),
 (32, [mkRat (36) 1]),
 (33, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polyCircle1_holds : evalRel Wi selfMode polyCircle1 = 0 := by
  have h := selfMode_circle 1
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1
  norm_num [polyCircle1, evalRel, zp, mkRat]
  module

def polyCircle3 : ModeRel := [(-5, [mkRat (1) 1]),
 (-4, [mkRat (36) 1]),
 (-3, [mkRat (630) 1]),
 (-2, [mkRat (7140) 1]),
 (-1, [mkRat (58905) 1]),
 (0, [mkRat (376992) 1]),
 (1, [mkRat (1947792) 1]),
 (2, [mkRat (8347680) 1]),
 (3, [mkRat (30260340) 1]),
 (4, [mkRat (94143280) 1]),
 (5, [mkRat (254186856) 1]),
 (6, [mkRat (600805296) 1]),
 (7, [mkRat (1251677700) 1]),
 (8, [mkRat (2310789600) 1]),
 (9, [mkRat (3796297200) 1]),
 (10, [mkRat (5567902560) 1]),
 (11, [mkRat (7307872110) 1]),
 (12, [mkRat (8597496600) 1]),
 (13, [mkRat (9075135300) 1]),
 (14, [mkRat (8597496600) 1]),
 (15, [mkRat (7307872110) 1]),
 (16, [mkRat (5567902560) 1]),
 (17, [mkRat (3796297200) 1]),
 (18, [mkRat (2310789600) 1]),
 (19, [mkRat (1251677700) 1]),
 (20, [mkRat (600805296) 1]),
 (21, [mkRat (254186856) 1]),
 (22, [mkRat (94143280) 1]),
 (23, [mkRat (30260340) 1]),
 (24, [mkRat (8347680) 1]),
 (25, [mkRat (1947792) 1]),
 (26, [mkRat (376992) 1]),
 (27, [mkRat (58905) 1]),
 (28, [mkRat (7140) 1]),
 (29, [mkRat (630) 1]),
 (30, [mkRat (36) 1]),
 (31, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polyCircle3_holds : evalRel Wi selfMode polyCircle3 = 0 := by
  have h := selfMode_circle 3
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1
  norm_num [polyCircle3, evalRel, zp, mkRat]
  module

def polyCircle5 : ModeRel := [(-7, [mkRat (1) 1]),
 (-6, [mkRat (36) 1]),
 (-5, [mkRat (630) 1]),
 (-4, [mkRat (7140) 1]),
 (-3, [mkRat (58905) 1]),
 (-2, [mkRat (376992) 1]),
 (-1, [mkRat (1947792) 1]),
 (0, [mkRat (8347680) 1]),
 (1, [mkRat (30260340) 1]),
 (2, [mkRat (94143280) 1]),
 (3, [mkRat (254186856) 1]),
 (4, [mkRat (600805296) 1]),
 (5, [mkRat (1251677700) 1]),
 (6, [mkRat (2310789600) 1]),
 (7, [mkRat (3796297200) 1]),
 (8, [mkRat (5567902560) 1]),
 (9, [mkRat (7307872110) 1]),
 (10, [mkRat (8597496600) 1]),
 (11, [mkRat (9075135300) 1]),
 (12, [mkRat (8597496600) 1]),
 (13, [mkRat (7307872110) 1]),
 (14, [mkRat (5567902560) 1]),
 (15, [mkRat (3796297200) 1]),
 (16, [mkRat (2310789600) 1]),
 (17, [mkRat (1251677700) 1]),
 (18, [mkRat (600805296) 1]),
 (19, [mkRat (254186856) 1]),
 (20, [mkRat (94143280) 1]),
 (21, [mkRat (30260340) 1]),
 (22, [mkRat (8347680) 1]),
 (23, [mkRat (1947792) 1]),
 (24, [mkRat (376992) 1]),
 (25, [mkRat (58905) 1]),
 (26, [mkRat (7140) 1]),
 (27, [mkRat (630) 1]),
 (28, [mkRat (36) 1]),
 (29, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polyCircle5_holds : evalRel Wi selfMode polyCircle5 = 0 := by
  have h := selfMode_circle 5
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1
  norm_num [polyCircle5, evalRel, zp, mkRat]
  module

def polyCircle7 : ModeRel := [(-9, [mkRat (1) 1]),
 (-8, [mkRat (36) 1]),
 (-7, [mkRat (630) 1]),
 (-6, [mkRat (7140) 1]),
 (-5, [mkRat (58905) 1]),
 (-4, [mkRat (376992) 1]),
 (-3, [mkRat (1947792) 1]),
 (-2, [mkRat (8347680) 1]),
 (-1, [mkRat (30260340) 1]),
 (0, [mkRat (94143280) 1]),
 (1, [mkRat (254186856) 1]),
 (2, [mkRat (600805296) 1]),
 (3, [mkRat (1251677700) 1]),
 (4, [mkRat (2310789600) 1]),
 (5, [mkRat (3796297200) 1]),
 (6, [mkRat (5567902560) 1]),
 (7, [mkRat (7307872110) 1]),
 (8, [mkRat (8597496600) 1]),
 (9, [mkRat (9075135300) 1]),
 (10, [mkRat (8597496600) 1]),
 (11, [mkRat (7307872110) 1]),
 (12, [mkRat (5567902560) 1]),
 (13, [mkRat (3796297200) 1]),
 (14, [mkRat (2310789600) 1]),
 (15, [mkRat (1251677700) 1]),
 (16, [mkRat (600805296) 1]),
 (17, [mkRat (254186856) 1]),
 (18, [mkRat (94143280) 1]),
 (19, [mkRat (30260340) 1]),
 (20, [mkRat (8347680) 1]),
 (21, [mkRat (1947792) 1]),
 (22, [mkRat (376992) 1]),
 (23, [mkRat (58905) 1]),
 (24, [mkRat (7140) 1]),
 (25, [mkRat (630) 1]),
 (26, [mkRat (36) 1]),
 (27, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polyCircle7_holds : evalRel Wi selfMode polyCircle7 = 0 := by
  have h := selfMode_circle 7
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1
  norm_num [polyCircle7, evalRel, zp, mkRat]
  module

def polyCircle9 : ModeRel := [(-11, [mkRat (1) 1]),
 (-10, [mkRat (36) 1]),
 (-9, [mkRat (630) 1]),
 (-8, [mkRat (7140) 1]),
 (-7, [mkRat (58905) 1]),
 (-6, [mkRat (376992) 1]),
 (-5, [mkRat (1947792) 1]),
 (-4, [mkRat (8347680) 1]),
 (-3, [mkRat (30260340) 1]),
 (-2, [mkRat (94143280) 1]),
 (-1, [mkRat (254186856) 1]),
 (0, [mkRat (600805296) 1]),
 (1, [mkRat (1251677700) 1]),
 (2, [mkRat (2310789600) 1]),
 (3, [mkRat (3796297200) 1]),
 (4, [mkRat (5567902560) 1]),
 (5, [mkRat (7307872110) 1]),
 (6, [mkRat (8597496600) 1]),
 (7, [mkRat (9075135300) 1]),
 (8, [mkRat (8597496600) 1]),
 (9, [mkRat (7307872110) 1]),
 (10, [mkRat (5567902560) 1]),
 (11, [mkRat (3796297200) 1]),
 (12, [mkRat (2310789600) 1]),
 (13, [mkRat (1251677700) 1]),
 (14, [mkRat (600805296) 1]),
 (15, [mkRat (254186856) 1]),
 (16, [mkRat (94143280) 1]),
 (17, [mkRat (30260340) 1]),
 (18, [mkRat (8347680) 1]),
 (19, [mkRat (1947792) 1]),
 (20, [mkRat (376992) 1]),
 (21, [mkRat (58905) 1]),
 (22, [mkRat (7140) 1]),
 (23, [mkRat (630) 1]),
 (24, [mkRat (36) 1]),
 (25, [mkRat (1) 1])]

set_option maxHeartbeats 4000000 in
theorem polyCircle9_holds : evalRel Wi selfMode polyCircle9 = 0 := by
  have h := selfMode_circle 9
  norm_num [Finset.sum_range_succ, cbz_apply_nonneg, gBinom, Nat.factorial] at h
  convert h using 1
  norm_num [polyCircle9, evalRel, zp, mkRat]
  module

end VOA.Classification.COne.OrbIcoZ
