import VOA.Classification.COne.OrbOctaZCCache02

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing16 : ModeRel := [
  (7, [
    mkRat (-15897600000) 1]),
  (8, [
    mkRat (-29725936) 1]),
  (9, [
    mkRat (286349958400) 1,
    mkRat (-4429592064) 1]),
  (10, [
    mkRat (815123540112) 1,
    mkRat (-33160015168) 1]),
  (11, [
    mkRat (944725627520) 1,
    mkRat (-77503862592) 1,
    mkRat (651245568) 1]),
  (12, [
    mkRat (475284982064) 1,
    mkRat (-66002204672) 1,
    mkRat (1534895872) 1]),
  (13, [
    mkRat (56686390560) 1,
    mkRat (-5821429088) 1,
    mkRat (-585783296) 1,
    mkRat (25387008) 1]),
  (14, [
    mkRat (-18460871200) 1,
    mkRat (12059782528) 1,
    mkRat (-2285218816) 1,
    mkRat (120913920) 1]),
  (15, [
    mkRat (66355200) 1,
    mkRat (-182458368) 1,
    mkRat (132296960) 1,
    mkRat (-32690176) 1,
    mkRat (2359296) 1]),
  (16, [
    mkRat (0) 1,
    mkRat (-518400) 1,
    mkRat (1360656) 1,
    mkRat (-863488) 1,
    mkRat (147456) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing16_check : equalRelCheck (modeVectorN s9v 16) sing16 = true := by
  decide +kernel

theorem sing16_holds : evalRel OrbOctaR.W selfMode sing16 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing16_check, modeVectorN_eval]
  exact s9_mode_relation 16

def sing17 : ModeRel := [
  (8, [
    mkRat (-26113239152) 1]),
  (9, [
    mkRat (-86435885536) 1]),
  (10, [
    mkRat (8706111456) 1,
    mkRat (-1907243072) 1]),
  (11, [
    mkRat (376051576320) 1,
    mkRat (-21806965952) 1]),
  (12, [
    mkRat (594548108528) 1,
    mkRat (-61956484640) 1,
    mkRat (664562432) 1]),
  (13, [
    mkRat (363997625760) 1,
    mkRat (-64307915648) 1,
    mkRat (1999392768) 1]),
  (14, [
    mkRat (69560972640) 1,
    mkRat (-16515016336) 1,
    mkRat (533786624) 1,
    mkRat (13553664) 1]),
  (15, [
    mkRat (-6934042624) 1,
    mkRat (6565333248) 1,
    mkRat (-1711481088) 1,
    mkRat (122327040) 1]),
  (16, [
    mkRat (-9796080) 1,
    mkRat (-5886896) 1,
    mkRat (38184176) 1,
    mkRat (-20032256) 1,
    mkRat (2506752) 1]),
  (17, [
    mkRat (76832) 1,
    mkRat (-696192) 1,
    mkRat (1900032) 1,
    mkRat (-1452032) 1,
    mkRat (294912) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing17_check : equalRelCheck (modeVectorN s9v 17) sing17 = true := by
  decide +kernel

theorem sing17_holds : evalRel OrbOctaR.W selfMode sing17 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing17_check, modeVectorN_eval]
  exact s9_mode_relation 17

def sing18 : ModeRel := [
  (9, [
    mkRat (-30893806944) 1]),
  (10, [
    mkRat (-138699276912) 1]),
  (11, [
    mkRat (-185138455680) 1,
    mkRat (420697728) 1]),
  (12, [
    mkRat (32918101920) 1,
    mkRat (-10107523584) 1]),
  (13, [
    mkRat (282898850400) 1,
    mkRat (-42214699584) 1,
    mkRat (612564480) 1]),
  (14, [
    mkRat (232754109264) 1,
    mkRat (-54001607040) 1,
    mkRat (2224546560) 1]),
  (15, [
    mkRat (58596581376) 1,
    mkRat (-20369154816) 1,
    mkRat (1427931648) 1,
    mkRat (-2138112) 1]),
  (16, [
    mkRat (-1519292160) 1,
    mkRat (2792468448) 1,
    mkRat (-1131355584) 1,
    mkRat (115983360) 1]),
  (17, [
    mkRat (3352608) 1,
    mkRat (10766304) 1,
    mkRat (2323296) 1,
    mkRat (-11312640) 1,
    mkRat (2654208) 1]),
  (18, [
    mkRat (73008) 1,
    mkRat (-1341792) 1,
    mkRat (2906928) 1,
    mkRat (-2080512) 1,
    mkRat (442368) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing18_check : equalRelCheck (modeVectorN s9v 18) sing18 = true := by
  decide +kernel

theorem sing18_holds : evalRel OrbOctaR.W selfMode sing18 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing18_check, modeVectorN_eval]
  exact s9_mode_relation 18

def sing19 : ModeRel := [
  (10, [
    mkRat (-30947616000) 1]),
  (11, [
    mkRat (-159279731200) 1]),
  (12, [
    mkRat (-294008158400) 1,
    mkRat (2350692000) 1]),
  (13, [
    mkRat (-196316851680) 1,
    mkRat (646170080) 1]),
  (14, [
    mkRat (45349640912) 1,
    mkRat (-21391568112) 1,
    mkRat (497041920) 1]),
  (15, [
    mkRat (114187606016) 1,
    mkRat (-38583911936) 1,
    mkRat (2192174080) 1]),
  (16, [
    mkRat (38404866480) 1,
    mkRat (-19075341584) 1,
    mkRat (2031808864) 1,
    mkRat (-22003200) 1]),
  (17, [
    mkRat (199989440) 1,
    mkRat (647711392) 1,
    mkRat (-612369952) 1,
    mkRat (100938240) 1]),
  (18, [
    mkRat (5086224) 1,
    mkRat (-10272768) 1,
    mkRat (2504048) 1,
    mkRat (-7475968) 1,
    mkRat (2801664) 1]),
  (19, [
    mkRat (0) 1,
    mkRat (-2073600) 1,
    mkRat (4829184) 1,
    mkRat (-3063808) 1,
    mkRat (589824) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing19_check : equalRelCheck (modeVectorN s9v 19) sing19 = true := by
  decide +kernel

theorem sing19_holds : evalRel OrbOctaR.W selfMode sing19 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing19_check, modeVectorN_eval]
  exact s9_mode_relation 19

end VOA.Classification.COne.OrbOctaZC
