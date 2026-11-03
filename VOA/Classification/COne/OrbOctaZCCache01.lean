import VOA.Classification.COne.OrbOctaZCCache00

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing7 : ModeRel := [
  (-2, [
    mkRat (148735623168) 1]),
  (-1, [
    mkRat (589278347264) 1]),
  (0, [
    mkRat (-92493997664) 1,
    mkRat (2953212768) 1]),
  (1, [
    mkRat (-3987457842720) 1,
    mkRat (73717633568) 1]),
  (2, [
    mkRat (-8134550623792) 1,
    mkRat (292358827440) 1,
    mkRat (-1096791168) 1]),
  (3, [
    mkRat (-6812362076800) 1,
    mkRat (422004126592) 1,
    mkRat (-4821738752) 1]),
  (4, [
    mkRat (-1926139735440) 1,
    mkRat (177456606064) 1,
    mkRat (-3794395616) 1,
    mkRat (10212864) 1]),
  (5, [
    mkRat (477844729856) 1,
    mkRat (-93646189472) 1,
    mkRat (5417658272) 1,
    mkRat (-84994560) 1]),
  (6, [
    mkRat (256231609200) 1,
    mkRat (-65373680736) 1,
    mkRat (5546068976) 1,
    mkRat (-167969536) 1,
    mkRat (1032192) 1]),
  (7, [
    mkRat (-15533088768) 1,
    mkRat (6153781248) 1,
    mkRat (-887758848) 1,
    mkRat (54591488) 1,
    mkRat (-1179648) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing7_check : equalRelCheck (modeVectorN s9v 7) sing7 = true := by
  decide +kernel

theorem sing7_holds : evalRel OrbOctaR.W selfMode sing7 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing7_check, modeVectorN_eval]
  exact s9_mode_relation 7

def sing8 : ModeRel := [
  (-1, [
    mkRat (155694923776) 1]),
  (0, [
    mkRat (788990792528) 1]),
  (1, [
    mkRat (985346186880) 1,
    mkRat (-2558212352) 1]),
  (2, [
    mkRat (-1453967921520) 1,
    mkRat (37416488896) 1]),
  (3, [
    mkRat (-5149510522240) 1,
    mkRat (211803685696) 1,
    mkRat (-915942400) 1]),
  (4, [
    mkRat (-5242275116496) 1,
    mkRat (364194547840) 1,
    mkRat (-4713108480) 1]),
  (5, [
    mkRat (-1951191107424) 1,
    mkRat (207915405344) 1,
    mkRat (-5322172672) 1,
    mkRat (18935808) 1]),
  (6, [
    mkRat (123123178400) 1,
    mkRat (-35469603072) 1,
    mkRat (2762105856) 1,
    mkRat (-56279040) 1]),
  (7, [
    mkRat (168203194368) 1,
    mkRat (-48503814656) 1,
    mkRat (4674290816) 1,
    mkRat (-162375680) 1,
    mkRat (1179648) 1]),
  (8, [
    mkRat (-7341064192) 1,
    mkRat (3350016768) 1,
    mkRat (-559543152) 1,
    mkRat (40192768) 1,
    mkRat (-1032192) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing8_check : equalRelCheck (modeVectorN s9v 8) sing8 = true := by
  decide +kernel

theorem sing8_holds : evalRel OrbOctaR.W selfMode sing8 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing8_check, modeVectorN_eval]
  exact s9_mode_relation 8

def sing9 : ModeRel := [
  (0, [
    mkRat (147661866000) 1]),
  (1, [
    mkRat (861662512800) 1]),
  (2, [
    mkRat (1640206893600) 1,
    mkRat (-6773688000) 1]),
  (3, [
    mkRat (387301017600) 1,
    mkRat (6239217600) 1]),
  (4, [
    mkRat (-2679824415888) 1,
    mkRat (133541309088) 1,
    mkRat (-695646720) 1]),
  (5, [
    mkRat (-3668274571104) 1,
    mkRat (289681052544) 1,
    mkRat (-4297420800) 1]),
  (6, [
    mkRat (-1702029895200) 1,
    mkRat (207258600816) 1,
    mkRat (-6169516416) 1,
    mkRat (26634240) 1]),
  (7, [
    mkRat (-67808309760) 1,
    mkRat (3077914752) 1,
    mkRat (599730048) 1,
    mkRat (-26818560) 1]),
  (8, [
    mkRat (103677347664) 1,
    mkRat (-34153172208) 1,
    mkRat (3778561008) 1,
    mkRat (-152218368) 1,
    mkRat (1327104) 1]),
  (9, [
    mkRat (-3201660000) 1,
    mkRat (1709251200) 1,
    mkRat (-335632896) 1,
    mkRat (28588032) 1,
    mkRat (-884736) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing9_check : equalRelCheck (modeVectorN s9v 9) sing9 = true := by
  decide +kernel

theorem sing9_holds : evalRel OrbOctaR.W selfMode sing9 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing9_check, modeVectorN_eval]
  exact s9_mode_relation 9

def sing10 : ModeRel := [
  (1, [
    mkRat (128882426400) 1]),
  (2, [
    mkRat (834307182800) 1]),
  (3, [
    mkRat (1933235086720) 1,
    mkRat (-9625795200) 1]),
  (4, [
    mkRat (1573251513120) 1,
    mkRat (-18528712960) 1]),
  (5, [
    mkRat (-808160947360) 1,
    mkRat (63243666240) 1,
    mkRat (-451998720) 1]),
  (6, [
    mkRat (-2272964350000) 1,
    mkRat (209317638400) 1,
    mkRat (-3637959680) 1]),
  (7, [
    mkRat (-1328380584960) 1,
    mkRat (185431603840) 1,
    mkRat (-6402824960) 1,
    mkRat (32993280) 1]),
  (8, [
    mkRat (-148165727680) 1,
    mkRat (25562086240) 1,
    mkRat (-1049905600) 1,
    mkRat (2442240) 1]),
  (9, [
    mkRat (59605207200) 1,
    mkRat (-22729524000) 1,
    mkRat (2924538080) 1,
    mkRat (-138442240) 1,
    mkRat (1474560) 1]),
  (10, [
    mkRat (-1260236880) 1,
    mkRat (803325600) 1,
    mkRat (-189141840) 1,
    mkRat (19462400) 1,
    mkRat (-737280) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing10_check : equalRelCheck (modeVectorN s9v 10) sing10 = true := by
  decide +kernel

theorem sing10_holds : evalRel OrbOctaR.W selfMode sing10 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing10_check, modeVectorN_eval]
  exact s9_mode_relation 10

end VOA.Classification.COne.OrbOctaZC
