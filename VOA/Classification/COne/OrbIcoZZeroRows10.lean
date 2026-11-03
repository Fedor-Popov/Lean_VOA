import VOA.Classification.COne.OrbIcoZZeroRows09

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing69 : ModeRel := [(56, [mkRat (371976889843944000) 1]), (57, [mkRat (2294954386640608000) 1]), (58, [mkRat (6816600078903203264) 1]), (59, [mkRat (13332116931420178944) 1]), (60, [mkRat (17871919788273919104) 1]), (61, [mkRat (14640445931754115200) 1]), (62, [mkRat (5117896333243370304) 1]), (63, [mkRat (-1609466887570882560) 1]), (64, [mkRat (-1941216406953621504) 1]), (65, [mkRat (-166069105607385216) 1]), (66, [mkRat (434228185832505920) 1]), (67, [mkRat (215011588089436672) 1]), (68, [mkRat (38723186096165952) 1]), (69, [mkRat (2186348274000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing69_check : equalRelCheck (constVector s13v (69)) sing69 = true := by
  decide +kernel

theorem sing69_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing69 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing69_check]
  exact const_singular_relation f hf (69)

def sing70 : ModeRel := [(57, [mkRat (617767684534000000) 1]), (58, [mkRat (4015489949471000000) 1]), (59, [mkRat (11528112829226273280) 1]), (60, [mkRat (19234231116563503040) 1]), (61, [mkRat (19629239169367004800) 1]), (62, [mkRat (10330427054196748800) 1]), (63, [mkRat (-631940917378713600) 1]), (64, [mkRat (-4121613869494470720) 1]), (65, [mkRat (-1485883649552883840) 1]), (66, [mkRat (778083926433699200) 1]), (67, [mkRat (805061534643735040) 1]), (68, [mkRat (255646998810423360) 1]), (69, [mkRat (31806249620320000) 1]), (70, [mkRat (948862239416000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing70_check : equalRelCheck (constVector s13v (70)) sing70 = true := by
  decide +kernel

theorem sing70_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing70 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing70_check]
  exact const_singular_relation f hf (70)

def sing71 : ModeRel := [(58, [mkRat (714584068118728704) 1]), (59, [mkRat (4619786566724739072) 1]), (60, [mkRat (12599343675105532928) 1]), (61, [mkRat (18438064024019601280) 1]), (62, [mkRat (14062857428269209024) 1]), (63, [mkRat (1905017828182702080) 1]), (64, [mkRat (-6100253589165649536) 1]), (65, [mkRat (-4380739913330974080) 1]), (66, [mkRat (479297531768879040) 1]), (67, [mkRat (2009338786525157376) 1]), (68, [mkRat (1039203158514778368) 1]), (69, [mkRat (216089962050544000) 1]), (70, [mkRat (13473843799707200) 1])]

set_option maxHeartbeats 4000000 in
theorem sing71_check : equalRelCheck (constVector s13v (71)) sing71 = true := by
  decide +kernel

theorem sing71_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing71 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing71_check]
  exact const_singular_relation f hf (71)

def sing72 : ModeRel := [(59, [mkRat (664564316024733696) 1]), (60, [mkRat (4149813646213035328) 1]), (61, [mkRat (10362470936515295360) 1]), (62, [mkRat (12257575655272364160) 1]), (63, [mkRat (4132966792235132928) 1]), (64, [mkRat (-6641183922982018368) 1]), (65, [mkRat (-8186357915463597696) 1]), (66, [mkRat (-1421616433474705920) 1]), (67, [mkRat (3459165403589469696) 1]), (68, [mkRat (2905760828479753152) 1]), (69, [mkRat (910007817144440960) 1]), (70, [mkRat (88918843597811584) 1]), (72, [mkRat (2599870699819008) 1])]

set_option maxHeartbeats 4000000 in
theorem sing72_check : equalRelCheck (constVector s13v (72)) sing72 = true := by
  decide +kernel

theorem sing72_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing72 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing72_check]
  exact const_singular_relation f hf (72)

def sing73 : ModeRel := [(60, [mkRat (494709908077000000) 1]), (61, [mkRat (2852941286603264000) 1]), (62, [mkRat (5877970266688488000) 1]), (63, [mkRat (3409091855061671936) 1]), (64, [mkRat (-5767488615596336384) 1]), (65, [mkRat (-11003521175011937664) 1]), (66, [mkRat (-4964877922471867200) 1]), (67, [mkRat (4026881884461252096) 1]), (68, [mkRat (5912542400339283840) 1]), (69, [mkRat (2658542138977057664) 1]), (70, [mkRat (361475582694525376) 1]), (72, [mkRat (47100753268431808) 1]), (73, [mkRat (16547520668801408) 1])]

set_option maxHeartbeats 4000000 in
theorem sing73_check : equalRelCheck (constVector s13v (73)) sing73 = true := by
  decide +kernel

theorem sing73_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing73 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing73_check]
  exact const_singular_relation f hf (73)

def sing74 : ModeRel := [(61, [mkRat (252927830812176000) 1]), (62, [mkRat (1138175238654792000) 1]), (63, [mkRat (708145366828427264) 1]), (64, [mkRat (-4694625369332325056) 1]), (65, [mkRat (-11246323145013277056) 1]), (66, [mkRat (-8483551152114576000) 1]), (67, [mkRat (2740957063631291904) 1]), (68, [mkRat (9032433332231972160) 1]), (69, [mkRat (5712898982705114496) 1]), (70, [mkRat (1011208491679916544) 1]), (72, [mkRat (396138128339284672) 1]), (73, [mkRat (290059586393587712) 1]), (74, [mkRat (57938153658840000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing74_check : equalRelCheck (constVector s13v (74)) sing74 = true := by
  decide +kernel

theorem sing74_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing74 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing74_check]
  exact const_singular_relation f hf (74)

end VOA.Classification.COne.OrbIcoZ
