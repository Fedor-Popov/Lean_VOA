import VOA.Classification.COne.OrbOctaZCCache01

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing11 : ModeRel := [
  (2, [
    mkRat (103448800000) 1]),
  (3, [
    mkRat (735225741824) 1]),
  (4, [
    mkRat (1939651315200) 1,
    mkRat (-11141952224) 1]),
  (5, [
    mkRat (2188970008992) 1,
    mkRat (-36251703968) 1]),
  (6, [
    mkRat (467676520400) 1,
    mkRat (4847305168) 1,
    mkRat (-201202432) 1]),
  (7, [
    mkRat (-1154291114496) 1,
    mkRat (131753244928) 1,
    mkRat (-2803481088) 1]),
  (8, [
    mkRat (-933884358480) 1,
    mkRat (151235731952) 1,
    mkRat (-6109290016) 1,
    mkRat (37698048) 1]),
  (9, [
    mkRat (-160998692800) 1,
    mkRat (35748941088) 1,
    mkRat (-2197880736) 1,
    mkRat (30558720) 1]),
  (10, [
    mkRat (31593833040) 1,
    mkRat (-14186224448) 1,
    mkRat (2157634160) 1,
    mkRat (-121991936) 1,
    mkRat (1622016) 1]),
  (11, [
    mkRat (-432640000) 1,
    mkRat (338764800) 1,
    mkRat (-98217984) 1,
    mkRat (12500992) 1,
    mkRat (-589824) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing11_check : equalRelCheck (modeVectorN s9v 11) sing11 = true := by
  decide +kernel

theorem sing11_holds : evalRel OrbOctaR.W selfMode sing11 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing11_check, modeVectorN_eval]
  exact s9_mode_relation 11

def sing12 : ModeRel := [
  (3, [
    mkRat (75058679808) 1]),
  (4, [
    mkRat (591722313264) 1]),
  (5, [
    mkRat (1739653346496) 1,
    mkRat (-11430913152) 1]),
  (6, [
    mkRat (2347911992400) 1,
    mkRat (-46881523392) 1]),
  (7, [
    mkRat (1209311635968) 1,
    mkRat (-39370704000) 1,
    mkRat (40952832) 1]),
  (8, [
    mkRat (-344330650320) 1,
    mkRat (63346491072) 1,
    mkRat (-1865592192) 1]),
  (9, [
    mkRat (-582474314400) 1,
    mkRat (112005216864) 1,
    mkRat (-5391655296) 1,
    mkRat (40433664) 1]),
  (10, [
    mkRat (-138492998784) 1,
    mkRat (37252845888) 1,
    mkRat (-2880676608) 1,
    mkRat (56586240) 1]),
  (11, [
    mkRat (15151848960) 1,
    mkRat (-8197439616) 1,
    mkRat (1505635776) 1,
    mkRat (-103812096) 1,
    mkRat (1769472) 1]),
  (12, [
    mkRat (-122266368) 1,
    mkRat (122732928) 1,
    mkRat (-45519408) 1,
    mkRat (7388928) 1,
    mkRat (-442368) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing12_check : equalRelCheck (modeVectorN s9v 12) sing12 = true := by
  decide +kernel

theorem sing12_holds : evalRel OrbOctaR.W selfMode sing12 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing12_check, modeVectorN_eval]
  exact s9_mode_relation 12

def sing13 : ModeRel := [
  (4, [
    mkRat (46841096016) 1]),
  (5, [
    mkRat (428335258208) 1]),
  (6, [
    mkRat (1410979086400) 1,
    mkRat (-10667210112) 1]),
  (7, [
    mkRat (2174864102400) 1,
    mkRat (-50876297344) 1]),
  (8, [
    mkRat (1514634597680) 1,
    mkRat (-68648967744) 1,
    mkRat (259616640) 1]),
  (9, [
    mkRat (172062375584) 1,
    mkRat (8214073600) 1,
    mkRat (-896130560) 1]),
  (10, [
    mkRat (-306261390624) 1,
    mkRat (73438436464) 1,
    mkRat (-4362974912) 1,
    mkRat (40885248) 1]),
  (11, [
    mkRat (-102684062080) 1,
    mkRat (33289405888) 1,
    mkRat (-3154934464) 1,
    mkRat (79580160) 1]),
  (12, [
    mkRat (6371687088) 1,
    mkRat (-4294304976) 1,
    mkRat (981324656) 1,
    mkRat (-84847360) 1,
    mkRat (1916928) 1]),
  (13, [
    mkRat (-25404192) 1,
    mkRat (35157888) 1,
    mkRat (-17690112) 1,
    mkRat (3811328) 1,
    mkRat (-294912) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing13_check : equalRelCheck (modeVectorN s9v 13) sing13 = true := by
  decide +kernel

theorem sing13_holds : evalRel OrbOctaR.W selfMode sing13 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing13_check, modeVectorN_eval]
  exact s9_mode_relation 13

def sing14 : ModeRel := [
  (5, [
    mkRat (21246940000) 1]),
  (6, [
    mkRat (265586750000) 1]),
  (7, [
    mkRat (1023226944000) 1,
    mkRat (-9074144000) 1]),
  (8, [
    mkRat (1792118000160) 1,
    mkRat (-49105228160) 1]),
  (9, [
    mkRat (1497892802912) 1,
    mkRat (-83542810112) 1,
    mkRat (441401600) 1]),
  (10, [
    mkRat (440048186256) 1,
    mkRat (-31608341696) 1,
    mkRat (35456640) 1]),
  (11, [
    mkRat (-113828981760) 1,
    mkRat (39562202816) 1,
    mkRat (-3141371776) 1,
    mkRat (38737920) 1]),
  (12, [
    mkRat (-67006521760) 1,
    mkRat (26520538272) 1,
    mkRat (-3092213952) 1,
    mkRat (98595840) 1]),
  (13, [
    mkRat (2218626144) 1,
    mkRat (-1966246688) 1,
    mkRat (585098528) 1,
    mkRat (-66042368) 1,
    mkRat (2064384) 1]),
  (14, [
    mkRat (-2890000) 1,
    mkRat (6420000) 1,
    mkRat (-4835856) 1,
    mkRat (1453312) 1,
    mkRat (-147456) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing14_check : equalRelCheck (modeVectorN s9v 14) sing14 = true := by
  decide +kernel

theorem sing14_holds : evalRel OrbOctaR.W selfMode sing14 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing14_check, modeVectorN_eval]
  exact s9_mode_relation 14

end VOA.Classification.COne.OrbOctaZC
