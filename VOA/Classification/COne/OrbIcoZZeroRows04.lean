import VOA.Classification.COne.OrbIcoZZeroRows03

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing29 : ModeRel := [(16, [mkRat (57482742952381032000) 1]), (17, [mkRat (571485693219624864000) 1]), (18, [mkRat (2095551968581952387264) 1]), (19, [mkRat (3074857019416017631744) 1]), (20, [mkRat (-736104495056906918016) 1]), (21, [mkRat (-8863324662557881776000) 1]), (22, [mkRat (-12366801987121495413696) 1]), (23, [mkRat (-6969653186696740638720) 1]), (24, [mkRat (-461613266777453839104) 1]), (25, [mkRat (1046696014032524536704) 1]), (26, [mkRat (229068103032653417280) 1]), (27, [mkRat (-41344435631007753728) 1]), (28, [mkRat (1128897566806974272) 1]), (29, [mkRat (-5427466838640000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing29_check : equalRelCheck (constVector s13v (29)) sing29 = true := by
  decide +kernel

theorem sing29_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing29 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing29_check]
  exact const_singular_relation f hf (29)

def sing30 : ModeRel := [(17, [mkRat (47831627633886000000) 1]), (18, [mkRat (517599868507902358720) 1]), (19, [mkRat (2097943627487788720640) 1]), (20, [mkRat (3797450872306779430080) 1]), (21, [mkRat (1661117699941312656000) 1]), (22, [mkRat (-5188323106598017102080) 1]), (23, [mkRat (-9578511419940198604800) 1]), (24, [mkRat (-6393073952143111790400) 1]), (25, [mkRat (-1050667855789125978240) 1]), (26, [mkRat (666509746134428265600) 1]), (27, [mkRat (196116227340039057920) 1]), (28, [mkRat (-25786481393283934400) 1]), (29, [mkRat (546082390859040000) 1]), (30, [mkRat (-1906612375752000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing30_check : equalRelCheck (constVector s13v (30)) sing30 = true := by
  decide +kernel

theorem sing30_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing30 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing30_check]
  exact const_singular_relation f hf (30)

def sing31 : ModeRel := [(18, [mkRat (37496913189503832064) 1]), (19, [mkRat (446860406345725878272) 1]), (20, [mkRat (1984991688353467093248) 1]), (21, [mkRat (4143963124251660694400) 1]), (22, [mkRat (3393498504999875226304) 1]), (23, [mkRat (-2115148607056436428800) 1]), (24, [mkRat (-6901689227581797453696) 1]), (25, [mkRat (-5509929563900139396480) 1]), (26, [mkRat (-1346938301577849733440) 1]), (27, [mkRat (375358120707549157376) 1]), (28, [mkRat (158120177452283135488) 1]), (29, [mkRat (-15378917887838736000) 1]), (30, [mkRat (245174326894484800) 1]), (31, [mkRat (-582160384000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing31_check : equalRelCheck (constVector s13v (31)) sing31 = true := by
  decide +kernel

theorem sing31_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing31 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing31_check]
  exact const_singular_relation f hf (31)

def sing32 : ModeRel := [(19, [mkRat (27079965978531987456) 1]), (20, [mkRat (365717269837406680128) 1]), (21, [mkRat (1784206181643936540800) 1]), (22, [mkRat (4171447954971533756800) 1]), (23, [mkRat (4506018229696260354048) 1]), (24, [mkRat (309246478658675385792) 1]), (25, [mkRat (-4486151133988919101056) 1]), (26, [mkRat (-4474388121005382900480) 1]), (27, [mkRat (-1423467427252937746944) 1]), (28, [mkRat (165376752063843026112) 1]), (29, [mkRat (120908628348437220480) 1]), (30, [mkRat (-8706602882115979136) 1]), (31, [mkRat (100090282647879680) 1]), (32, [mkRat (-145798242250752) 1])]

set_option maxHeartbeats 4000000 in
theorem sing32_check : equalRelCheck (constVector s13v (32)) sing32 = true := by
  decide +kernel

theorem sing32_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing32 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing32_check]
  exact const_singular_relation f hf (32)

def sing33 : ModeRel := [(20, [mkRat (17095887506061000000) 1]), (21, [mkRat (280073561872216000000) 1]), (22, [mkRat (1522672298478384200000) 1]), (23, [mkRat (3942893740088228622336) 1]), (24, [mkRat (5068772775870487435776) 1]), (25, [mkRat (2086774462067998417536) 1]), (26, [mkRat (-2428019966291876020800) 1]), (27, [mkRat (-3408573175306627029504) 1]), (28, [mkRat (-1347135070255931644800) 1]), (29, [mkRat (24775168582007754624) 1]), (30, [mkRat (87891821084392093376) 1]), (31, [mkRat (-4630970976079400960) 1]), (32, [mkRat (35962056083498688) 1]), (33, [mkRat (-26742383217792) 1])]

set_option maxHeartbeats 4000000 in
theorem sing33_check : equalRelCheck (constVector s13v (33)) sing33 = true := by
  decide +kernel

theorem sing33_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing33 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing33_check]
  exact const_singular_relation f hf (33)

def sing34 : ModeRel := [(21, [mkRat (7963439231314000000) 1]), (22, [mkRat (195104261167193000000) 1]), (23, [mkRat (1225857417526498443264) 1]), (24, [mkRat (3523103665841074593344) 1]), (25, [mkRat (5168573429541493777024) 1]), (26, [mkRat (3257941255872723907200) 1]), (27, [mkRat (-776362867846749866496) 1]), (28, [mkRat (-2402928439525430116800) 1]), (29, [mkRat (-1175743923314626802304) 1]), (30, [mkRat (-59964021528032033536) 1]), (31, [mkRat (60680377903686031360) 1]), (32, [mkRat (-2279066024705790528) 1]), (33, [mkRat (10728948914232832) 1]), (34, [mkRat (-2674533160000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing34_check : equalRelCheck (constVector s13v (34)) sing34 = true := by
  decide +kernel

theorem sing34_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing34 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing34_check]
  exact const_singular_relation f hf (34)

end VOA.Classification.COne.OrbIcoZ
