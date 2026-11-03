import VOA.Classification.COne.OrbOctaZCLow

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing2 : ModeRel := [
  (-7, [
    mkRat (-226790207072) 1]),
  (-6, [
    mkRat (-2788762391536) 1]),
  (-5, [
    mkRat (-11575702353024) 1,
    mkRat (39881538688) 1]),
  (-4, [
    mkRat (-22159732019040) 1,
    mkRat (239007612928) 1]),
  (-3, [
    mkRat (-18813340622752) 1,
    mkRat (418400447680) 1,
    mkRat (-919725568) 1]),
  (-2, [
    mkRat (-552977269680) 1,
    mkRat (-27953449088) 1,
    mkRat (742649088) 1]),
  (-1, [
    mkRat (10739918315520) 1,
    mkRat (-789677940736) 1,
    mkRat (14258929664) 1,
    mkRat (-37748736) 1]),
  (0, [
    mkRat (6636588711296) 1,
    mkRat (-719181164832) 1,
    mkRat (22602879552) 1,
    mkRat (-184335360) 1]),
  (1, [
    mkRat (711308900640) 1,
    mkRat (-109749748256) 1,
    mkRat (5500167776) 1,
    mkRat (-94424576) 1,
    mkRat (294912) 1]),
  (2, [
    mkRat (-299735804368) 1,
    mkRat (67815684768) 1,
    mkRat (-5452878288) 1,
    mkRat (179515648) 1,
    mkRat (-1916928) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing2_check : equalRelCheck (modeVectorN s9v 2) sing2 = true := by
  decide +kernel

theorem sing2_holds : evalRel OrbOctaR.W selfMode sing2 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing2_check, modeVectorN_eval]
  exact s9_mode_relation 2

def sing3 : ModeRel := [
  (-6, [
    mkRat (-100489745664) 1]),
  (-5, [
    mkRat (-1808815421952) 1]),
  (-4, [
    mkRat (-8745617106240) 1,
    mkRat (32779951008) 1]),
  (-3, [
    mkRat (-18850342959840) 1,
    mkRat (220268711136) 1]),
  (-2, [
    mkRat (-19177880301360) 1,
    mkRat (466299374736) 1,
    mkRat (-1137008640) 1]),
  (-1, [
    mkRat (-5607810686976) 1,
    mkRat (210488647680) 1,
    mkRat (-1258291200) 1]),
  (0, [
    mkRat (5568380396976) 1,
    mkRat (-460903612176) 1,
    mkRat (9427702368) 1,
    mkRat (-28626432) 1]),
  (1, [
    mkRat (4704442937280) 1,
    mkRat (-556903182432) 1,
    mkRat (19214321376) 1,
    mkRat (-173514240) 1]),
  (2, [
    mkRat (713594210448) 1,
    mkRat (-120382724736) 1,
    mkRat (6625105776) 1,
    mkRat (-125817600) 1,
    mkRat (442368) 1]),
  (3, [
    mkRat (-179499220992) 1,
    mkRat (44773198848) 1,
    mkRat (-3986952192) 1,
    mkRat (146423808) 1,
    mkRat (-1769472) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing3_check : equalRelCheck (modeVectorN s9v 3) sing3 = true := by
  decide +kernel

theorem sing3_holds : evalRel OrbOctaR.W selfMode sing3 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing3_check, modeVectorN_eval]
  exact s9_mode_relation 3

def sing5 : ModeRel := [
  (-4, [
    mkRat (73988059600) 1]),
  (-3, [
    mkRat (-275836736800) 1]),
  (-2, [
    mkRat (-3626913290880) 1,
    mkRat (17058273280) 1]),
  (-1, [
    mkRat (-10905380167680) 1,
    mkRat (153088737280) 1]),
  (0, [
    mkRat (-14738759989840) 1,
    mkRat (429103388800) 1,
    mkRat (-1279461760) 1]),
  (1, [
    mkRat (-8687928213600) 1,
    mkRat (434686796800) 1,
    mkRat (-3907776000) 1]),
  (2, [
    mkRat (-208059219360) 1,
    mkRat (-19123054480) 1,
    mkRat (1432633280) 1,
    mkRat (-9047040) 1]),
  (3, [
    mkRat (1922423457920) 1,
    mkRat (-279200383680) 1,
    mkRat (11945373120) 1,
    mkRat (-136412160) 1]),
  (4, [
    mkRat (495160009200) 1,
    mkRat (-101409194000) 1,
    mkRat (6838179440) 1,
    mkRat (-161688320) 1,
    mkRat (737280) 1]),
  (5, [
    mkRat (-57875577760) 1,
    mkRat (17888649600) 1,
    mkRat (-1992967680) 1,
    mkRat (93030400) 1,
    mkRat (-1474560) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing5_check : equalRelCheck (modeVectorN s9v 5) sing5 = true := by
  decide +kernel

theorem sing5_holds : evalRel OrbOctaR.W selfMode sing5 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing5_check, modeVectorN_eval]
  exact s9_mode_relation 5

def sing6 : ModeRel := [
  (-3, [
    mkRat (122690700000) 1]),
  (-2, [
    mkRat (239569071984) 1]),
  (-1, [
    mkRat (-1629837926400) 1,
    mkRat (9587490816) 1]),
  (0, [
    mkRat (-7179997900128) 1,
    mkRat (113167554432) 1]),
  (1, [
    mkRat (-11441091388320) 1,
    mkRat (367803961728) 1,
    mkRat (-1222732032) 1]),
  (2, [
    mkRat (-8094103593456) 1,
    mkRat (450290824128) 1,
    mkRat (-4568120448) 1]),
  (3, [
    mkRat (-1427617067520) 1,
    mkRat (105291081792) 1,
    mkRat (-1545822336) 1,
    mkRat (780288) 1]),
  (4, [
    mkRat (1056915799200) 1,
    mkRat (-174347715552) 1,
    mkRat (8510938944) 1,
    mkRat (-112020480) 1]),
  (5, [
    mkRat (367451616480) 1,
    mkRat (-83682052128) 1,
    mkRat (6305369760) 1,
    mkRat (-168055296) 1,
    mkRat (884736) 1]),
  (6, [
    mkRat (-30800250000) 1,
    mkRat (10724205600) 1,
    mkRat (-1352724624) 1,
    mkRat (72099072) 1,
    mkRat (-1327104) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing6_check : equalRelCheck (modeVectorN s9v 6) sing6 = true := by
  decide +kernel

theorem sing6_holds : evalRel OrbOctaR.W selfMode sing6 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing6_check, modeVectorN_eval]
  exact s9_mode_relation 6

end VOA.Classification.COne.OrbOctaZC
