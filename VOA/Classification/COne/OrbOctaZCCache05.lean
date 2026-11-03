import VOA.Classification.COne.OrbOctaZCCache04

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing25 : ModeRel := [
  (16, [
    mkRat (4849059600) 1]),
  (17, [
    mkRat (14674167200) 1]),
  (18, [
    mkRat (7293039520) 1,
    mkRat (1446442560) 1]),
  (19, [
    mkRat (-16685460480) 1,
    mkRat (8939990720) 1]),
  (20, [
    mkRat (-19882015120) 1,
    mkRat (17311952160) 1,
    mkRat (-783206400) 1]),
  (21, [
    mkRat (-4876290400) 1,
    mkRat (12216995200) 1,
    mkRat (-1815633920) 1]),
  (22, [
    mkRat (1055766240) 1,
    mkRat (1524626800) 1,
    mkRat (-87332480) 1,
    mkRat (-246466560) 1]),
  (23, [
    mkRat (179371520) 1,
    mkRat (-169232000) 1,
    mkRat (179431040) 1,
    mkRat (-224962560) 1]),
  (24, [
    mkRat (-10206000) 1,
    mkRat (-169830000) 1,
    mkRat (267849200) 1,
    mkRat (-139897600) 1,
    mkRat (3686400) 1]),
  (25, [
    mkRat (1049760) 1,
    mkRat (-40176000) 1,
    mkRat (86791680) 1,
    mkRat (-34048000) 1,
    mkRat (1474560) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing25_check : equalRelCheck (modeVectorN s9v 25) sing25 = true := by
  decide +kernel

theorem sing25_holds : evalRel OrbOctaR.W selfMode sing25 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing25_check, modeVectorN_eval]
  exact s9_mode_relation 25

def sing26 : ModeRel := [
  (17, [
    mkRat (7707700000) 1]),
  (18, [
    mkRat (33025073744) 1]),
  (19, [
    mkRat (53429001600) 1,
    mkRat (-104534144) 1]),
  (20, [
    mkRat (40988024352) 1,
    mkRat (2482124032) 1]),
  (21, [
    mkRat (16942148960) 1,
    mkRat (7753780288) 1,
    mkRat (-840159232) 1]),
  (22, [
    mkRat (5536779984) 1,
    mkRat (6411132928) 1,
    mkRat (-2307921408) 1]),
  (23, [
    mkRat (1487600640) 1,
    mkRat (42895232) 1,
    mkRat (-454502656) 1,
    mkRat (-304361472) 1]),
  (24, [
    mkRat (-23195200) 1,
    mkRat (-571020192) 1,
    mkRat (428725824) 1,
    mkRat (-327367680) 1]),
  (25, [
    mkRat (-21571680) 1,
    mkRat (-268575008) 1,
    mkRat (509281760) 1,
    mkRat (-196691456) 1,
    mkRat (3833856) 1]),
  (26, [
    mkRat (5390000) 1,
    mkRat (-64284000) 1,
    mkRat (147093936) 1,
    mkRat (-46331648) 1,
    mkRat (1622016) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing26_check : equalRelCheck (modeVectorN s9v 26) sing26 = true := by
  decide +kernel

theorem sing26_holds : evalRel OrbOctaR.W selfMode sing26 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing26_check, modeVectorN_eval]
  exact s9_mode_relation 26

def sing27 : ModeRel := [
  (18, [
    mkRat (8537488128) 1]),
  (19, [
    mkRat (39814654464) 1]),
  (20, [
    mkRat (72579931776) 1,
    mkRat (-1528530912) 1]),
  (21, [
    mkRat (65587750560) 1,
    mkRat (-3784339872) 1]),
  (22, [
    mkRat (31128900048) 1,
    mkRat (-2139545520) 1,
    mkRat (-736397568) 1]),
  (23, [
    mkRat (7488990720) 1,
    mkRat (-40082688) 1,
    mkRat (-2330906112) 1]),
  (24, [
    mkRat (410220720) 1,
    mkRat (-1586846736) 1,
    mkRat (-240680736) 1,
    mkRat (-368948736) 1]),
  (25, [
    mkRat (-250547904) 1,
    mkRat (-890968032) 1,
    mkRat (1112077152) 1,
    mkRat (-446031360) 1]),
  (26, [
    mkRat (10495440) 1,
    mkRat (-405694656) 1,
    mkRat (949489776) 1,
    mkRat (-265925376) 1,
    mkRat (3981312) 1]),
  (27, [
    mkRat (13381632) 1,
    mkRat (-110840832) 1,
    mkRat (244518912) 1,
    mkRat (-61489152) 1,
    mkRat (1769472) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing27_check : equalRelCheck (modeVectorN s9v 27) sing27 = true := by
  decide +kernel

theorem sing27_holds : evalRel OrbOctaR.W selfMode sing27 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing27_check, modeVectorN_eval]
  exact s9_mode_relation 27

def sing28 : ModeRel := [
  (19, [
    mkRat (7606849536) 1]),
  (20, [
    mkRat (36409942448) 1]),
  (21, [
    mkRat (67659943360) 1,
    mkRat (-2572209792) 1]),
  (22, [
    mkRat (60671687760) 1,
    mkRat (-8562000064) 1]),
  (23, [
    mkRat (25736522240) 1,
    mkRat (-9806254464) 1,
    mkRat (-409789440) 1]),
  (24, [
    mkRat (3104581424) 1,
    mkRat (-4725715520) 1,
    mkRat (-1645385600) 1]),
  (25, [
    mkRat (-1096773024) 1,
    mkRat (-2357948576) 1,
    mkRat (915415168) 1,
    mkRat (-440543232) 1]),
  (26, [
    mkRat (-213253120) 1,
    mkRat (-1097949632) 1,
    mkRat (2499435776) 1,
    mkRat (-581898240) 1]),
  (27, [
    mkRat (101058048) 1,
    mkRat (-692958336) 1,
    mkRat (1690678976) 1,
    mkRat (-348544000) 1,
    mkRat (4128768) 1]),
  (28, [
    mkRat (21835008) 1,
    mkRat (-209319552) 1,
    mkRat (395533008) 1,
    mkRat (-79835392) 1,
    mkRat (1916928) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing28_check : equalRelCheck (modeVectorN s9v 28) sing28 = true := by
  decide +kernel

theorem sing28_holds : evalRel OrbOctaR.W selfMode sing28 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing28_check, modeVectorN_eval]
  exact s9_mode_relation 28

end VOA.Classification.COne.OrbOctaZC
