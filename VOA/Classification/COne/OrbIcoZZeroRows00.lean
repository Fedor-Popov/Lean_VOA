import VOA.Classification.COne.OrbIcoZConst

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing4 : ModeRel := [(-9, [mkRat (-137486438538149888000) 1]), (-8, [mkRat (2627190871424422424000) 1]), (-7, [mkRat (34608998117071489947264) 1]), (-6, [mkRat (154875952798664729375744) 1]), (-5, [mkRat (340659198902472315510784) 1]), (-4, [mkRat (343635815762725282056000) 1]), (-3, [mkRat (-41060188753137836397696) 1]), (-2, [mkRat (-500129480737780870024320) 1]), (-1, [mkRat (-523627173740082563887104) 1]), (0, [mkRat (-186902606276419890652096) 1]), (1, [mkRat (43321002960809558346880) 1]), (2, [mkRat (46672824997324872214272) 1]), (3, [mkRat (5080533869063202537472) 1]), (4, [mkRat (-1934813447142768640000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing4_check : equalRelCheck (constVector s13v (4)) sing4 = true := by
  decide +kernel

theorem sing4_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing4 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing4_check]
  exact const_singular_relation f hf (4)

def sing5 : ModeRel := [(-8, [mkRat (-244178945263071000000) 1]), (-7, [mkRat (937431178933806385920) 1]), (-6, [mkRat (24845837470041910562240) 1]), (-5, [mkRat (128090142873097664596480) 1]), (-4, [mkRat (310546543694649837264000) 1]), (-3, [mkRat (365954700360603351765120) 1]), (-2, [mkRat (75755740636648327099200) 1]), (-1, [mkRat (-343103995490578635571200) 1]), (0, [mkRat (-430750486295303560458240) 1]), (1, [mkRat (-182514230272093754294400) 1]), (2, [mkRat (18772303482416792070720) 1]), (3, [mkRat (35820922732578690112000) 1]), (4, [mkRat (4845826878001062440000) 1]), (5, [mkRat (-1413385410212064432000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing5_check : equalRelCheck (constVector s13v (5)) sing5 = true := by
  decide +kernel

theorem sing5_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing5 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing5_check]
  exact const_singular_relation f hf (5)

def sing6 : ModeRel := [(-7, [mkRat (-321858770590571550336) 1]), (-6, [mkRat (-456634921381216305728) 1]), (-5, [mkRat (16110950148094763944448) 1]), (-4, [mkRat (101843641092775493361600) 1]), (-3, [mkRat (273964375093959540799104) 1]), (-2, [mkRat (366162088702510644902400) 1]), (-1, [mkRat (158084268439432831432704) 1]), (0, [mkRat (-213531074960014631100480) 1]), (1, [mkRat (-343760021928300828762240) 1]), (2, [mkRat (-169731224400795917226624) 1]), (3, [mkRat (1674282424621963954688) 1]), (4, [mkRat (26896875304356457384000) 1]), (5, [mkRat (4407735576670381612800) 1]), (6, [mkRat (-1023940782424989000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing6_check : equalRelCheck (constVector s13v (6)) sing6 = true := by
  decide +kernel

theorem sing6_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing6 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing6_check]
  exact const_singular_relation f hf (6)

def sing7 : ModeRel := [(-6, [mkRat (-372966492073618386944) 1]), (-5, [mkRat (-1559627564486074703872) 1]), (-4, [mkRat (8532272282633614771200) 1]), (-3, [mkRat (77064394526849064675200) 1]), (-2, [mkRat (233884660905495658061248) 1]), (-1, [mkRat (349563244933937848891392) 1]), (0, [mkRat (211072238899793222953344) 1]), (1, [mkRat (-109959407279886182686080) 1]), (2, [mkRat (-265186063703002559713344) 1]), (3, [mkRat (-151843662741308453644288) 1]), (4, [mkRat (-9568578495964625688320) 1]), (5, [mkRat (19702670722635833057664) 1]), (6, [mkRat (3870733377631564924480) 1]), (7, [mkRat (-735316772091018084352) 1])]

set_option maxHeartbeats 4000000 in
theorem sing7_check : equalRelCheck (constVector s13v (7)) sing7 = true := by
  decide +kernel

theorem sing7_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing7 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing7_check]
  exact const_singular_relation f hf (7)

def sing8 : ModeRel := [(-5, [mkRat (-400415845533696000000) 1]), (-4, [mkRat (-2385464843798451000000) 1]), (-3, [mkRat (2171266064796395600000) 1]), (-2, [mkRat (54435100944781036126336) 1]), (-1, [mkRat (192767917975196197349376) 1]), (0, [mkRat (320913698159642625145536) 1]), (1, [mkRat (239832680338280899363200) 1]), (2, [mkRat (-30173286127384787157504) 1]), (3, [mkRat (-196451647232334770035200) 1]), (4, [mkRat (-131386090698341080435776) 1]), (5, [mkRat (-16325936028813186762624) 1]), (6, [mkRat (14018390106267838445440) 1]), (7, [mkRat (3305325167175382335488) 1]), (8, [mkRat (-523158051262198689792) 1])]

set_option maxHeartbeats 4000000 in
theorem sing8_check : equalRelCheck (constVector s13v (8)) sing8 = true := by
  decide +kernel

theorem sing8_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing8 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing8_check]
  exact const_singular_relation f hf (8)

def sing9 : ModeRel := [(-4, [mkRat (-407423527861779000000) 1]), (-3, [mkRat (-2955279988224512000000) 1]), (-2, [mkRat (-2966813107080564876736) 1]), (-1, [mkRat (34417630041927264313344) 1]), (0, [mkRat (152580816390870495277824) 1]), (1, [mkRat (284361632160626944963200) 1]), (2, [mkRat (249250249172909115405504) 1]), (3, [mkRat (28519845205846359129600) 1]), (4, [mkRat (-138115175715336646322304) 1]), (5, [mkRat (-110245654307830118622336) 1]), (6, [mkRat (-19748290757021780799040) 1]), (7, [mkRat (9620588744987086569472) 1]), (8, [mkRat (2756845791863291524032) 1]), (9, [mkRat (-368554557853132560000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing9_check : equalRelCheck (constVector s13v (9)) sing9 = true := by
  decide +kernel

theorem sing9_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing9 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing9_check]
  exact const_singular_relation f hf (9)

end VOA.Classification.COne.OrbIcoZ
