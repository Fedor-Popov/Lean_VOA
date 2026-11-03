import VOA.Classification.COne.OrbOctaZCCache06

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing34 : ModeRel := [
  (25, [
    mkRat (-2558844000) 1]),
  (26, [
    mkRat (-9229865200) 1]),
  (27, [
    mkRat (-9077302400) 1,
    mkRat (3411792000) 1]),
  (28, [
    mkRat (3687626400) 1,
    mkRat (11290188800) 1]),
  (29, [
    mkRat (10369750112) 1,
    mkRat (-5016174912) 1,
    mkRat (10950074880) 1]),
  (30, [
    mkRat (3105839696) 1,
    mkRat (-68876118656) 1,
    mkRat (36326406400) 1]),
  (31, [
    mkRat (0) 1,
    mkRat (-131368093184) 1,
    mkRat (57799926784) 1,
    mkRat (-1034895360) 1]),
  (32, [
    mkRat (4449242240) 1,
    mkRat (-117567311648) 1,
    mkRat (49412330048) 1,
    mkRat (-1811266560) 1]),
  (33, [
    mkRat (4538636064) 1,
    mkRat (-52432600608) 1,
    mkRat (21905088608) 1,
    mkRat (-1178234368) 1,
    mkRat (5013504) 1]),
  (34, [
    mkRat (1246590000) 1,
    mkRat (-9417448800) 1,
    mkRat (3969632304) 1,
    mkRat (-274509568) 1,
    mkRat (2801664) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing34_check : equalRelCheck (modeVectorN s9v 34) sing34 = true := by
  decide +kernel

theorem sing34_holds : evalRel OrbOctaR.W selfMode sing34 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing34_check, modeVectorN_eval]
  exact s9_mode_relation 34

def sing35 : ModeRel := [
  (26, [
    mkRat (-1416377600) 1]),
  (27, [
    mkRat (-2832755200) 1]),
  (28, [
    mkRat (3587574720) 1,
    mkRat (3086250400) 1]),
  (29, [
    mkRat (10928697120) 1,
    mkRat (1445551840) 1]),
  (30, [
    mkRat (3843577040) 1,
    mkRat (-57458472560) 1,
    mkRat (15425684480) 1]),
  (31, [
    mkRat (0) 1,
    mkRat (-189591833600) 1,
    mkRat (52502353920) 1]),
  (32, [
    mkRat (16955717040) 1,
    mkRat (-280611404560) 1,
    mkRat (82506911840) 1,
    mkRat (-1164357120) 1]),
  (33, [
    mkRat (28059984320) 1,
    mkRat (-222212504160) 1,
    mkRat (69298072800) 1,
    mkRat (-2094005760) 1]),
  (34, [
    mkRat (16776589200) 1,
    mkRat (-91850864000) 1,
    mkRat (30207079280) 1,
    mkRat (-1380995840) 1,
    mkRat (5160960) 1]),
  (35, [
    mkRat (3578347520) 1,
    mkRat (-15641318400) 1,
    mkRat (5392527360) 1,
    mkRat (-323993600) 1,
    mkRat (2949120) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing35_check : equalRelCheck (modeVectorN s9v 35) sing35 = true := by
  decide +kernel

theorem sing35_holds : evalRel OrbOctaR.W selfMode sing35 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing35_check, modeVectorN_eval]
  exact s9_mode_relation 35

def sing37 : ModeRel := [
  (28, [
    mkRat (953389008) 1]),
  (29, [
    mkRat (4079831264) 1]),
  (30, [
    mkRat (1722119296) 1,
    mkRat (-10169482752) 1]),
  (31, [
    mkRat (0) 1,
    mkRat (-100046152192) 1]),
  (32, [
    mkRat (70565966768) 1,
    mkRat (-399230659200) 1,
    mkRat (27840776832) 1]),
  (33, [
    mkRat (244804146080) 1,
    mkRat (-820652054528) 1,
    mkRat (98593796608) 1]),
  (34, [
    mkRat (364041160800) 1,
    mkRat (-967344949136) 1,
    mkRat (153895290304) 1,
    mkRat (-1452174336) 1]),
  (35, [
    mkRat (284296870016) 1,
    mkRat (-664378757312) 1,
    mkRat (126893484992) 1,
    mkRat (-2734709760) 1]),
  (36, [
    mkRat (115035755760) 1,
    mkRat (-248357600016) 1,
    mkRat (54174513776) 1,
    mkRat (-1850288896) 1,
    mkRat (5455872) 1]),
  (37, [
    mkRat (19124737632) 1,
    mkRat (-39191340672) 1,
    mkRat (9476577792) 1,
    mkRat (-440399872) 1,
    mkRat (3244032) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing37_check : equalRelCheck (modeVectorN s9v 37) sing37 = true := by
  decide +kernel

theorem sing37_holds : evalRel OrbOctaR.W selfMode sing37 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing37_check, modeVectorN_eval]
  exact s9_mode_relation 37

def sing38 : ModeRel := [
  (29, [
    mkRat (893269216) 1]),
  (30, [
    mkRat (446634608) 1]),
  (31, [
    mkRat (0) 1,
    mkRat (-28584614912) 1]),
  (32, [
    mkRat (80363556000) 1,
    mkRat (-225522748544) 1]),
  (33, [
    mkRat (395403229280) 1,
    mkRat (-779459490944) 1,
    mkRat (36124163840) 1]),
  (34, [
    mkRat (849275859984) 1,
    mkRat (-1468805633600) 1,
    mkRat (129992327040) 1]),
  (35, [
    mkRat (1002715301376) 1,
    mkRat (-1631900863936) 1,
    mkRat (203121365888) 1,
    mkRat (-1611159552) 1]),
  (36, [
    mkRat (679861231520) 1,
    mkRat (-1072972665312) 1,
    mkRat (166778031936) 1,
    mkRat (-3094563840) 1]),
  (37, [
    mkRat (249543422688) 1,
    mkRat (-387718892576) 1,
    mkRat (70768285856) 1,
    mkRat (-2118709760) 1,
    mkRat (5603328) 1]),
  (38, [
    mkRat (38595133808) 1,
    mkRat (-59528428512) 1,
    mkRat (12296735088) 1,
    mkRat (-507951872) 1,
    mkRat (3391488) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing38_check : equalRelCheck (modeVectorN s9v 38) sing38 = true := by
  decide +kernel

theorem sing38_holds : evalRel OrbOctaR.W selfMode sing38 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing38_check, modeVectorN_eval]
  exact s9_mode_relation 38

end VOA.Classification.COne.OrbOctaZC
