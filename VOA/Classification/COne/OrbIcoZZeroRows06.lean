import VOA.Classification.COne.OrbIcoZZeroRows05

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing42 : ModeRel := [(29, [mkRat (-16074770744980531584) 1]), (30, [mkRat (-134992035219172897472) 1]), (31, [mkRat (-426041194710472284160) 1]), (32, [mkRat (-556799143482218669760) 1]), (33, [mkRat (18514130110078205568) 1]), (34, [mkRat (930921143441735252352) 1]), (35, [mkRat (1100581057866911491584) 1]), (36, [mkRat (507609201609283287360) 1]), (37, [mkRat (50818994231016902016) 1]), (38, [mkRat (-19006275385077539328) 1]), (39, [mkRat (-65772827081113600) 1]), (40, [mkRat (-1390721069224256) 1]), (41, [mkRat (5380476917760) 1]), (42, [mkRat (200229962688) 1])]

set_option maxHeartbeats 4000000 in
theorem sing42_check : equalRelCheck (constVector s13v (42)) sing42 = true := by
  decide +kernel

theorem sing42_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing42 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing42_check]
  exact const_singular_relation f hf (42)

def sing43 : ModeRel := [(30, [mkRat (-13895768932352000000) 1]), (31, [mkRat (-126422481894129664000) 1]), (32, [mkRat (-443879448859939248000) 1]), (33, [mkRat (-726515338561452379264) 1]), (34, [mkRat (-408695202074798608064) 1]), (35, [mkRat (394029211378770279936) 1]), (36, [mkRat (752199474943169433600) 1]), (37, [mkRat (421319089129884986496) 1]), (38, [mkRat (67356652246964055360) 1]), (39, [mkRat (-9409591441426210816) 1]), (40, [mkRat (-84166266583389824) 1]), (41, [mkRat (-278779705096320) 1]), (42, [mkRat (17728670507968) 1]), (43, [mkRat (90949419008) 1])]

set_option maxHeartbeats 4000000 in
theorem sing43_check : equalRelCheck (constVector s13v (43)) sing43 = true := by
  decide +kernel

theorem sing43_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing43 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing43_check]
  exact const_singular_relation f hf (43)

def sing44 : ModeRel := [(31, [mkRat (-11221696055771136000) 1]), (32, [mkRat (-111057444374158152000) 1]), (33, [mkRat (-426721642334783076736) 1]), (34, [mkRat (-803504669509318989056) 1]), (35, [mkRat (-697832982455178756096) 1]), (36, [mkRat (-32027196350735140800) 1]), (37, [mkRat (435152355261739154304) 1]), (38, [mkRat (316377326489173107840) 1]), (39, [mkRat (66947589434042474496) 1]), (40, [mkRat (-3490026303470414016) 1]), (41, [mkRat (-23860952246724480) 1]), (42, [mkRat (834338619100672) 1]), (43, [mkRat (10254546993152) 1])]

set_option maxHeartbeats 4000000 in
theorem sing44_check : equalRelCheck (constVector s13v (44)) sing44 = true := by
  decide +kernel

theorem sing44_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing44 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing44_check]
  exact const_singular_relation f hf (44)

def sing45 : ModeRel := [(32, [mkRat (-8289663747183000000) 1]), (33, [mkRat (-91010230637843628800) 1]), (34, [mkRat (-382109629478012749120) 1]), (35, [mkRat (-800734179272657794560) 1]), (36, [mkRat (-856715200856266819200) 1]), (37, [mkRat (-337805398162452912000) 1]), (38, [mkRat (171478801178823758400) 1]), (39, [mkRat (210759808251742740480) 1]), (40, [mkRat (56405467809387068160) 1]), (41, [mkRat (-418776829617052800) 1]), (42, [mkRat (23347585081835840) 1]), (43, [mkRat (939343127349760) 1]), (44, [mkRat (-10777623480000) 1]), (45, [mkRat (159668496000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing45_check : equalRelCheck (constVector s13v (45)) sing45 = true := by
  decide +kernel

theorem sing45_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing45 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing45_check]
  exact const_singular_relation f hf (45)

def sing46 : ModeRel := [(33, [mkRat (-5319470444690669696) 1]), (34, [mkRat (-68366097419668932928) 1]), (35, [mkRat (-318136818235850767872) 1]), (36, [mkRat (-734380992916814259520) 1]), (37, [mkRat (-901395593882628642176) 1]), (38, [mkRat (-525925032394329342720) 1]), (39, [mkRat (-27371553650784731136) 1]), (40, [mkRat (117141041379400201920) 1]), (41, [mkRat (41383215676456122240) 1]), (42, [mkRat (722817697324021376) 1]), (43, [mkRat (33088139520045568) 1]), (44, [mkRat (156571414344000) 1]), (45, [mkRat (-25162180908800) 1]), (46, [mkRat (660275000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing46_check : equalRelCheck (constVector s13v (46)) sing46 = true := by
  decide +kernel

theorem sing46_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing46 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing46_check]
  exact const_singular_relation f hf (46)

def sing47 : ModeRel := [(34, [mkRat (-2503675483925704704) 1]), (35, [mkRat (-45066158710662684672) 1]), (36, [mkRat (-242876207627314858240) 1]), (37, [mkRat (-622269420043950093440) 1]), (38, [mkRat (-853578895192983127872) 1]), (39, [mkRat (-608465408804386848768) 1]), (40, [mkRat (-159119831097177511296) 1]), (41, [mkRat (43044990581719716480) 1]), (42, [mkRat (26076607314268975296) 1]), (43, [mkRat (769400532944074752) 1]), (44, [mkRat (15614100381404160) 1]), (45, [mkRat (-757676785663616) 1]), (46, [mkRat (-15969509675200) 1]), (47, [mkRat (1302621585408) 1])]

set_option maxHeartbeats 4000000 in
theorem sing47_check : equalRelCheck (constVector s13v (47)) sing47 = true := by
  decide +kernel

theorem sing47_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing47 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing47_check]
  exact const_singular_relation f hf (47)

end VOA.Classification.COne.OrbIcoZ
