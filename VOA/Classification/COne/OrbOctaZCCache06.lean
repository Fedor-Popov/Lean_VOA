import VOA.Classification.COne.OrbOctaZCCache05

/-! Compact normal forms for four singular-vector mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu

def sing29 : ModeRel := [
  (20, [
    mkRat (5427730000) 1]),
  (21, [
    mkRat (25808079200) 1]),
  (22, [
    mkRat (46151870400) 1,
    mkRat (-3012944000) 1]),
  (23, [
    mkRat (36679357440) 1,
    mkRat (-10701357440) 1]),
  (24, [
    mkRat (9704766512) 1,
    mkRat (-13034520512) 1,
    mkRat (211122560) 1]),
  (25, [
    mkRat (-2828007264) 1,
    mkRat (-5797596416) 1,
    mkRat (29544960) 1]),
  (26, [
    mkRat (-1555460640) 1,
    mkRat (-1898525584) 1,
    mkRat (3448622144) 1,
    mkRat (-519459840) 1]),
  (27, [
    mkRat (246093440) 1,
    mkRat (-1614389568) 1,
    mkRat (4924458048) 1,
    mkRat (-735912960) 1]),
  (28, [
    mkRat (213083184) 1,
    mkRat (-1418715728) 1,
    mkRat (2861983088) 1,
    mkRat (-445491968) 1,
    mkRat (4276224) 1]),
  (29, [
    mkRat (23660000) 1,
    mkRat (-416976000) 1,
    mkRat (621003264) 1,
    mkRat (-101685248) 1,
    mkRat (2064384) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing29_check : equalRelCheck (modeVectorN s9v 29) sing29 = true := by
  decide +kernel

theorem sing29_holds : evalRel OrbOctaR.W selfMode sing29 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing29_check, modeVectorN_eval]
  exact s9_mode_relation 29

def sing30 : ModeRel := [
  (21, [
    mkRat (2661141600) 1]),
  (22, [
    mkRat (11975137200) 1]),
  (23, [
    mkRat (18092997120) 1,
    mkRat (-2700837120) 1]),
  (24, [
    mkRat (7441516320) 1,
    mkRat (-9452929920) 1]),
  (25, [
    mkRat (-5907169440) 1,
    mkRat (-10608288000) 1,
    mkRat (1207645440) 1]),
  (26, [
    mkRat (-5429727600) 1,
    mkRat (-2888395200) 1,
    mkRat (3019113600) 1]),
  (27, [
    mkRat (-162447360) 1,
    mkRat (-1257122880) 1,
    mkRat (7872574080) 1,
    mkRat (-606013440) 1]),
  (28, [
    mkRat (923389920) 1,
    mkRat (-3723754080) 1,
    mkRat (8789747520) 1,
    mkRat (-909020160) 1]),
  (29, [
    mkRat (251407200) 1,
    mkRat (-3167604000) 1,
    mkRat (4622084640) 1,
    mkRat (-557713920) 1,
    mkRat (4423680) 1]),
  (30, [
    mkRat (12806640) 1,
    mkRat (-834386400) 1,
    mkRat (946721520) 1,
    mkRat (-127353600) 1,
    mkRat (2211840) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing30_check : equalRelCheck (modeVectorN s9v 30) sing30 = true := by
  decide +kernel

theorem sing30_holds : evalRel OrbOctaR.W selfMode sing30 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing30_check, modeVectorN_eval]
  exact s9_mode_relation 30

def sing32 : ModeRel := [
  (23, [
    mkRat (-1958469632) 1]),
  (24, [
    mkRat (-9688890736) 1]),
  (25, [
    mkRat (-19941348864) 1,
    mkRat (103303168) 1]),
  (26, [
    mkRat (-20181579120) 1,
    mkRat (2284312768) 1]),
  (27, [
    mkRat (-7137476992) 1,
    mkRat (6080098240) 1,
    mkRat (4705144832) 1]),
  (28, [
    mkRat (3765111600) 1,
    mkRat (1677236992) 1,
    mkRat (14480418048) 1]),
  (29, [
    mkRat (3608969760) 1,
    mkRat (-17047459936) 1,
    mkRat (24872681984) 1,
    mkRat (-803291136) 1]),
  (30, [
    mkRat (617154656) 1,
    mkRat (-25484172672) 1,
    mkRat (22827727872) 1,
    mkRat (-1316290560) 1]),
  (31, [
    mkRat (0) 1,
    mkRat (-14537179136) 1,
    mkRat (10706878976) 1,
    mkRat (-831758336) 1,
    mkRat (4718592) 1]),
  (32, [
    mkRat (47071232) 1,
    mkRat (-3044228352) 1,
    mkRat (2029838352) 1,
    mkRat (-191405312) 1,
    mkRat (2506752) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing32_check : equalRelCheck (modeVectorN s9v 32) sing32 = true := by
  decide +kernel

theorem sing32_holds : evalRel OrbOctaR.W selfMode sing32 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing32_check, modeVectorN_eval]
  exact s9_mode_relation 32

def sing33 : ModeRel := [
  (24, [
    mkRat (-2834247024) 1]),
  (25, [
    mkRat (-12341007072) 1]),
  (26, [
    mkRat (-19733711520) 1,
    mkRat (2026054848) 1]),
  (27, [
    mkRat (-11222545920) 1,
    mkRat (9169797696) 1]),
  (28, [
    mkRat (4177125360) 1,
    mkRat (9656294496) 1,
    mkRat (7422700800) 1]),
  (29, [
    mkRat (7224959904) 1,
    mkRat (-15188607360) 1,
    mkRat (23847813120) 1]),
  (30, [
    mkRat (1709268576) 1,
    mkRat (-53051623056) 1,
    mkRat (38917264128) 1,
    mkRat (-914644992) 1]),
  (31, [
    mkRat (0) 1,
    mkRat (-57483382272) 1,
    mkRat (34197536256) 1,
    mkRat (-1552343040) 1]),
  (32, [
    mkRat (686125968) 1,
    mkRat (-28431230256) 1,
    mkRat (15520268016) 1,
    mkRat (-995470080) 1,
    mkRat (4866048) 1]),
  (33, [
    mkRat (330347808) 1,
    mkRat (-5463925632) 1,
    mkRat (2868162048) 1,
    mkRat (-230418432) 1,
    mkRat (2654208) 1])]

set_option maxHeartbeats 500000 in
-- Normalizing thirty level-nine words at this one mode index.
theorem sing33_check : equalRelCheck (modeVectorN s9v 33) sing33 = true := by
  decide +kernel

theorem sing33_holds : evalRel OrbOctaR.W selfMode sing33 = 0 := by
  rw [← equalRelCheck_sound OrbOctaR.W selfMode sing33_check, modeVectorN_eval]
  exact s9_mode_relation 33

end VOA.Classification.COne.OrbOctaZC
