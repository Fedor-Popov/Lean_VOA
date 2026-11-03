import VOA.Classification.COne.OrbOctaZCCache03

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing20 : ModeRel := [
  (11, [
    mkRat (-27308441600) 1]),
  (12, [
    mkRat (-153470045200) 1]),
  (13, [
    mkRat (-326905318080) 1,
    mkRat (3729101440) 1]),
  (14, [
    mkRat (-313381295280) 1,
    mkRat (9385245760) 1]),
  (15, [
    mkRat (-104669440000) 1,
    mkRat (-2276046080) 1,
    mkRat (324392960) 1]),
  (16, [
    mkRat (26614935600) 1,
    mkRat (-21494206400) 1,
    mkRat (1902207360) 1]),
  (17, [
    mkRat (18907791840) 1,
    mkRat (-14602143520) 1,
    mkRat (2306956160) 1,
    mkRat (-46356480) 1]),
  (18, [
    mkRat (243389120) 1,
    mkRat (-221305920) 1,
    mkRat (-205520640) 1,
    mkRat (76247040) 1]),
  (19, [
    mkRat (-4646400) 1,
    mkRat (-18512000) 1,
    mkRat (19856960) 1,
    mkRat (-9466880) 1,
    mkRat (2949120) 1]),
  (20, [
    mkRat (154880) 1,
    mkRat (-2947200) 1,
    mkRat (7797840) 1,
    mkRat (-4716800) 1,
    mkRat (737280) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing20_check : equalRelCheck (modeVectorN s9v 20) sing20 = true := by
  decide +kernel

theorem sing20_holds : evalRel OrbOctaR.W selfMode sing20 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing20_check, modeVectorN_eval]
  exact s9_mode_relation 20

def sing21 : ModeRel := [
  (12, [
    mkRat (-21192030000) 1]),
  (13, [
    mkRat (-128379979296) 1]),
  (14, [
    mkRat (-299999788800) 1,
    mkRat (4462423296) 1]),
  (15, [
    mkRat (-334935072768) 1,
    mkRat (15340760832) 1]),
  (16, [
    mkRat (-171729498960) 1,
    mkRat (12896456448) 1,
    mkRat (106147968) 1]),
  (17, [
    mkRat (-24281095776) 1,
    mkRat (-5754972672) 1,
    mkRat (1375314432) 1]),
  (18, [
    mkRat (5265717600) 1,
    mkRat (-8892221328) 1,
    mkRat (2246533824) 1,
    mkRat (-75512832) 1]),
  (19, [
    mkRat (-78768000) 1,
    mkRat (-291191232) 1,
    mkRat (59968704) 1,
    mkRat (40965120) 1]),
  (20, [
    mkRat (-5969040) 1,
    mkRat (-11199888) 1,
    mkRat (41474160) 1,
    mkRat (-18230016) 1,
    mkRat (3096576) 1]),
  (21, [
    mkRat (540000) 1,
    mkRat (-4752000) 1,
    mkRat (12151296) 1,
    mkRat (-7354368) 1,
    mkRat (884736) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing21_check : equalRelCheck (modeVectorN s9v 21) sing21 = true := by
  decide +kernel

theorem sing21_holds : evalRel OrbOctaR.W selfMode sing21 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing21_check, modeVectorN_eval]
  exact s9_mode_relation 21

def sing22 : ModeRel := [
  (13, [
    mkRat (-13855175712) 1]),
  (14, [
    mkRat (-91901541136) 1]),
  (15, [
    mkRat (-233409910784) 1,
    mkRat (4524139008) 1]),
  (16, [
    mkRat (-287098020960) 1,
    mkRat (18100757888) 1]),
  (17, [
    mkRat (-172978974112) 1,
    mkRat (22627067520) 1,
    mkRat (-140506368) 1]),
  (18, [
    mkRat (-42417272560) 1,
    mkRat (6326986432) 1,
    mkRat (655520128) 1]),
  (19, [
    mkRat (-1346680320) 1,
    mkRat (-3595641536) 1,
    mkRat (1880566144) 1,
    mkRat (-109787136) 1]),
  (20, [
    mkRat (-182109664) 1,
    mkRat (-37575392) 1,
    mkRat (181888832) 1,
    mkRat (-5852160) 1]),
  (21, [
    mkRat (5338080) 1,
    mkRat (-8364576) 1,
    mkRat (63030176) 1,
    mkRat (-34710016) 1,
    mkRat (3244032) 1]),
  (22, [
    mkRat (734832) 1,
    mkRat (-8582112) 1,
    mkRat (18959472) 1,
    mkRat (-11291392) 1,
    mkRat (1032192) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing22_check : equalRelCheck (modeVectorN s9v 22) sing22 = true := by
  decide +kernel

theorem sing22_holds : evalRel OrbOctaR.W selfMode sing22 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing22_check, modeVectorN_eval]
  exact s9_mode_relation 22

def sing23 : ModeRel := [
  (14, [
    mkRat (-6466863104) 1]),
  (15, [
    mkRat (-51734904832) 1]),
  (16, [
    mkRat (-148064187360) 1,
    mkRat (3957571168) 1]),
  (17, [
    mkRat (-199864092960) 1,
    mkRat (17643494176) 1]),
  (18, [
    mkRat (-132215852080) 1,
    mkRat (26277296176) 1,
    mkRat (-392202880) 1]),
  (19, [
    mkRat (-37567395456) 1,
    mkRat (13381313920) 1,
    mkRat (-187173120) 1]),
  (20, [
    mkRat (-2447297424) 1,
    mkRat (139355504) 1,
    mkRat (1281183008) 1,
    mkRat (-149494272) 1]),
  (21, [
    mkRat (-25219840) 1,
    mkRat (167968608) 1,
    mkRat (190286496) 1,
    mkRat (-65149440) 1]),
  (22, [
    mkRat (15794928) 1,
    mkRat (-31118816) 1,
    mkRat (91402736) 1,
    mkRat (-59851520) 1,
    mkRat (3391488) 1]),
  (23, [
    mkRat (401408) 1,
    mkRat (-15286272) 1,
    mkRat (30547968) 1,
    mkRat (-16842752) 1,
    mkRat (1179648) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing23_check : equalRelCheck (modeVectorN s9v 23) sing23 = true := by
  decide +kernel

theorem sing23_holds : evalRel OrbOctaR.W selfMode sing23 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing23_check, modeVectorN_eval]
  exact s9_mode_relation 23

end VOA.Classification.COne.OrbOctaZC
