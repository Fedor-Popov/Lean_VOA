import VOA.Classification.COne.OrbIcoZZeroRows00

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing10 : ModeRel := [(-3, [mkRat (-397357066972502000000) 1]), (-2, [mkRat (-3295469478141626480320) 1]), (-1, [mkRat (-6922714994598756833280) 1]), (0, [mkRat (17280007381097588936000) 1]), (1, [mkRat (114826945000140075740800) 1]), (2, [mkRat (243424106029497568337280) 1]), (3, [mkRat (243839953537345621132800) 1]), (4, [mkRat (69054637873291726474560) 1]), (5, [mkRat (-90083351270204652032640) 1]), (6, [mkRat (-89766578862294453184000) 1]), (7, [mkRat (-20781272784835111485440) 1]), (8, [mkRat (6294767638389512022720) 1]), (9, [mkRat (2252343186097600000000) 1]), (10, [mkRat (-256925923730281000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing10_check : equalRelCheck (constVector s13v (10)) sing10 = true := by
  decide +kernel

theorem sing10_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing10 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing10_check]
  exact const_singular_relation f hf (10)

def sing11 : ModeRel := [(-2, [mkRat (-373602115545156550656) 1]), (-1, [mkRat (-3435905303996392931328) 1]), (0, [mkRat (-9773340652919811179392) 1]), (1, [mkRat (3124690175585510949760) 1]), (2, [mkRat (80587232190187008001344) 1]), (3, [mkRat (200990860964446987599360) 1]), (4, [mkRat (227652085363224262401024) 1]), (5, [mkRat (94421551862768441224320) 1]), (6, [mkRat (-51794190512016694322880) 1]), (7, [mkRat (-70847982637385831399424) 1]), (8, [mkRat (-20184685869736007770752) 1]), (9, [mkRat (3843295981770132400000) 1]), (10, [mkRat (1805900831251086680000) 1]), (11, [mkRat (-177112757606400000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing11_check : equalRelCheck (constVector s13v (11)) sing11 = true := by
  decide +kernel

theorem sing11_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing11 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing11_check]
  exact const_singular_relation f hf (11)

def sing12 : ModeRel := [(-1, [mkRat (-339449859512855691264) 1]), (0, [mkRat (-3408335383901238039872) 1]), (1, [mkRat (-11622463604935952030080) 1]), (2, [mkRat (-8082949955945204609280) 1]), (3, [mkRat (50566896756496786833408) 1]), (4, [mkRat (159349906494959307281472) 1]), (5, [mkRat (204216394236860366216064) 1]), (6, [mkRat (107524175174366150029440) 1]), (7, [mkRat (-22370940302034823102464) 1]), (8, [mkRat (-54033041022142840636608) 1]), (9, [mkRat (-18554120930381814232960) 1]), (10, [mkRat (2089899357663582728704) 1]), (11, [mkRat (1422698709588394475520) 1]), (12, [mkRat (-120640607781893701632) 1])]

set_option maxHeartbeats 4000000 in
theorem sing12_check : equalRelCheck (constVector s13v (12)) sing12 = true := by
  decide +kernel

theorem sing12_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing12 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing12_check]
  exact const_singular_relation f hf (12)

def sing13 : ModeRel := [(0, [mkRat (-298004642372591000000) 1]), (1, [mkRat (-3244987770411505888000) 1]), (2, [mkRat (-12592201656027446856000) 1]), (3, [mkRat (-16486841124117508478464) 1]), (4, [mkRat (25146194272969997981056) 1]), (5, [mkRat (120229583498170800990336) 1]), (6, [mkRat (176518806140847056078400) 1]), (7, [mkRat (111074990673315258679296) 1]), (8, [mkRat (-748486408992157221120) 1]), (9, [mkRat (-39588344792771635924096) 1]), (10, [mkRat (-16343479262694628485824) 1]), (11, [mkRat (881617962819682920960) 1]), (12, [mkRat (1102063594182113912128) 1]), (13, [mkRat (-81127357954987307392) 1])]

set_option maxHeartbeats 4000000 in
theorem sing13_check : equalRelCheck (constVector s13v (13)) sing13 = true := by
  decide +kernel

theorem sing13_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing13 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing13_check]
  exact const_singular_relation f hf (13)

def sing14 : ModeRel := [(1, [mkRat (-252111393425585232000) 1]), (2, [mkRat (-2977386741320418504000) 1]), (3, [mkRat (-12815367112684017204736) 1]), (4, [mkRat (-22313852956132905640256) 1]), (5, [mkRat (4432614738330013006464) 1]), (6, [mkRat (84852348415688822841600) 1]), (7, [mkRat (147004386959588172693504) 1]), (8, [mkRat (107524351439773903293120) 1]), (9, [mkRat (14225604818133745792896) 1]), (10, [mkRat (-27572950821745503624576) 1]), (11, [mkRat (-13887184403464300776960) 1]), (12, [mkRat (88960107067417214272) 1]), (13, [mkRat (839717651293945716992) 1]), (14, [mkRat (-53809134421581000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing14_check : equalRelCheck (constVector s13v (14)) sing14 = true := by
  decide +kernel

theorem sing14_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing14 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing14_check]
  exact const_singular_relation f hf (14)

def sing15 : ModeRel := [(2, [mkRat (-204302011852224000000) 1]), (3, [mkRat (-2635382214779747164160) 1]), (4, [mkRat (-12428779565823161939200) 1]), (5, [mkRat (-25849433956611778634880) 1]), (6, [mkRat (-11687430920779527201600) 1]), (7, [mkRat (53996093196855168368640) 1]), (8, [mkRat (117600740674693989955200) 1]), (9, [mkRat (99017511386213007995520) 1]), (10, [mkRat (23712916282688853716160) 1]), (11, [mkRat (-17897128822465819084800) 1]), (12, [mkRat (-11421220897693903052800) 1]), (13, [mkRat (-395175156980210130560) 1]), (14, [mkRat (629398234731417480000) 1]), (15, [mkRat (-35163585127415808000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing15_check : equalRelCheck (constVector s13v (15)) sing15 = true := by
  decide +kernel

theorem sing15_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing15 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing15_check]
  exact const_singular_relation f hf (15)

end VOA.Classification.COne.OrbIcoZ
