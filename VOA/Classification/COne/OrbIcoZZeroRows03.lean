import VOA.Classification.COne.OrbIcoZZeroRows02

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing23 : ModeRel := [(10, [mkRat (61438521238848000000) 1]), (11, [mkRat (180116868559002624000) 1]), (12, [mkRat (-1541921802618592192000) 1]), (13, [mkRat (-10405163149036452520064) 1]), (14, [mkRat (-26302522595671001093184) 1]), (15, [mkRat (-32690556166325980145664) 1]), (16, [mkRat (-15734904696906390019200) 1]), (17, [mkRat (7527955434825821844096) 1]), (18, [mkRat (12570637596981880943040) 1]), (19, [mkRat (4344307205072826660864) 1]), (20, [mkRat (-467621001087411642624) 1]), (21, [mkRat (-338534361625956675200) 1]), (22, [mkRat (32454586259295545408) 1]), (23, [mkRat (-566172134871662592) 1])]

set_option maxHeartbeats 4000000 in
theorem sing23_check : equalRelCheck (constVector s13v (23)) sing23 = true := by
  decide +kernel

theorem sing23_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing23 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing23_check]
  exact const_singular_relation f hf (23)

def sing24 : ModeRel := [(11, [mkRat (70767607174742016000) 1]), (12, [mkRat (357816498439806472000) 1]), (13, [mkRat (-445563164106368292736) 1]), (14, [mkRat (-7162767847959411229056) 1]), (15, [mkRat (-21432091958320794003456) 1]), (16, [mkRat (-30119457570797629320000) 1]), (17, [mkRat (-18630616815029698068096) 1]), (18, [mkRat (1879680656270118696960) 1]), (19, [mkRat (9143388580151390762496) 1]), (20, [mkRat (3893076784809737578944) 1]), (21, [mkRat (-135723083071081340800) 1]), (22, [mkRat (-257635557083613043328) 1]), (23, [mkRat (20255219051906138112) 1]), (24, [mkRat (-297526691151360000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing24_check : equalRelCheck (constVector s13v (24)) sing24 = true := by
  decide +kernel

theorem sing24_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing24 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing24_check]
  exact const_singular_relation f hf (24)

def sing25 : ModeRel := [(12, [mkRat (75209909270221000000) 1]), (13, [mkRat (484911012044440847360) 1]), (14, [mkRat (452041315800374813760) 1]), (15, [mkRat (-4245455518960992931840) 1]), (16, [mkRat (-16510209974778797024000) 1]), (17, [mkRat (-26433282447386181959040) 1]), (18, [mkRat (-19573760090016062817600) 1]), (19, [mkRat (-2199604185279323496960) 1]), (20, [mkRat (6196246400493989631360) 1]), (21, [mkRat (3308458445100980528000) 1]), (22, [mkRat (72780812488754130880) 1]), (23, [mkRat (-190296344713898373120) 1]), (24, [mkRat (12273517123672600000) 1]), (25, [mkRat (-150019285111696000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing25_check : equalRelCheck (constVector s13v (25)) sing25 = true := by
  decide +kernel

theorem sing25_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing25 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing25_check]
  exact const_singular_relation f hf (25)

def sing26 : ModeRel := [(13, [mkRat (75385615857420806784) 1]), (14, [mkRat (564608315076946443072) 1]), (15, [mkRat (1145950725372803237888) 1]), (16, [mkRat (-1732619762903280954560) 1]), (17, [mkRat (-11807382862939033086336) 1]), (18, [mkRat (-22103708907547525215360) 1]), (19, [mkRat (-19016640567694783842816) 1]), (20, [mkRat (-4899529598756189273280) 1]), (21, [mkRat (3777996631150232534400) 1]), (22, [mkRat (2679505951833545726976) 1]), (23, [mkRat (189283233146720329728) 1]), (24, [mkRat (-136397190451539080000) 1]), (25, [mkRat (7194880915612083200) 1]), (26, [mkRat (-72100305225000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing26_check : equalRelCheck (constVector s13v (26)) sing26 = true := by
  decide +kernel

theorem sing26_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing26 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing26_check]
  exact const_singular_relation f hf (26)

def sing27 : ModeRel := [(14, [mkRat (71994624402706661376) 1]), (15, [mkRat (601623540418058518528) 1]), (16, [mkRat (1641276753721871319680) 1]), (17, [mkRat (330696302336466295680) 1]), (18, [mkRat (-7527091662139372446912) 1]), (19, [mkRat (-17530018849835165925888) 1]), (20, [mkRat (-17384255621948624472576) 1]), (21, [mkRat (-6440904645254593123200) 1]), (22, [mkRat (1889030363478267245376) 1]), (23, [mkRat (2068891178952991813632) 1]), (24, [mkRat (240464325092030952320) 1]), (25, [mkRat (-94774739785141045376) 1]), (26, [mkRat (4062204614794760640) 1]), (27, [mkRat (-32748473181929472) 1])]

set_option maxHeartbeats 4000000 in
theorem sing27_check : equalRelCheck (constVector s13v (27)) sing27 = true := by
  decide +kernel

theorem sing27_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing27 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing27_check]
  exact const_singular_relation f hf (27)

def sing28 : ModeRel := [(15, [mkRat (65777950830592000000) 1]), (16, [mkRat (601756045841278328000) 1]), (17, [mkRat (1951299660730499856000) 1]), (18, [mkRat (1929643789589200891136) 1]), (19, [mkRat (-3809303194278144303104) 1]), (20, [mkRat (-13034680034104897366464) 1]), (21, [mkRat (-15058310827750678992000) 1]), (22, [mkRat (-7055425728485442155904) 1]), (23, [mkRat (494925761126539653120) 1]), (24, [mkRat (1517094125870131022144) 1]), (25, [mkRat (248066806437097115776) 1]), (26, [mkRat (-63722684278132346880) 1]), (27, [mkRat (2196406803716866048) 1]), (28, [mkRat (-13899394755592192) 1])]

set_option maxHeartbeats 4000000 in
theorem sing28_check : equalRelCheck (constVector s13v (28)) sing28 = true := by
  decide +kernel

theorem sing28_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing28 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing28_check]
  exact const_singular_relation f hf (28)

end VOA.Classification.COne.OrbIcoZ
