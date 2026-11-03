import VOA.Classification.COne.OrbIcoZZeroRows06

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing49 : ModeRel := [(36, [mkRat (2073756571364296000) 1]), (37, [mkRat (-2989377904235968000) 1]), (38, [mkRat (-87752020143569132736) 1]), (39, [mkRat (-331747177967355437056) 1]), (40, [mkRat (-580264868657179360256) 1]), (41, [mkRat (-535346439765138288000) 1]), (42, [mkRat (-246520859436911148096) 1]), (43, [mkRat (-38386111651919485440) 1]), (44, [mkRat (3964397572868858496) 1]), (45, [mkRat (-52855136939952256) 1]), (46, [mkRat (-22008432383470400) 1]), (47, [mkRat (-537560816099328) 1]), (48, [mkRat (52787268382912) 1]), (49, [mkRat (1385624240000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing49_check : equalRelCheck (constVector s13v (49)) sing49 = true := by
  decide +kernel

theorem sing49_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing49 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing49_check]
  exact const_singular_relation f hf (49)

def sing50 : ModeRel := [(37, [mkRat (3642213296898000000) 1]), (38, [mkRat (13372877320719428160) 1]), (39, [mkRat (-19864082415163555840) 1]), (40, [mkRat (-185064859999187426240) 1]), (41, [mkRat (-404266018667132016000) 1]), (42, [mkRat (-425675417359447482240) 1]), (43, [mkRat (-225528859829666265600) 1]), (44, [mkRat (-49728228170229812160) 1]), (45, [mkRat (-1346387040579584640) 1]), (46, [mkRat (-288270044923296000) 1]), (47, [mkRat (-19355772868945920) 1]), (48, [mkRat (522811555180480) 1]), (49, [mkRat (64414011200000) 1]), (50, [mkRat (564772824000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing50_check : equalRelCheck (constVector s13v (50)) sing50 = true := by
  decide +kernel

theorem sing50_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing50 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing50_check]
  exact const_singular_relation f hf (50)

def sing51 : ModeRel := [(38, [mkRat (4672364207809757184) 1]), (39, [mkRat (25631863900651651072) 1]), (40, [mkRat (35869889769785122688) 1]), (41, [mkRat (-54266952636608837760) 1]), (42, [mkRat (-230972432228591027136) 1]), (43, [mkRat (-297408428549566978560) 1]), (44, [mkRat (-179959414039438185216) 1]), (45, [mkRat (-47407727017819409280) 1]), (46, [mkRat (-3351601487196772800) 1]), (47, [mkRat (-296587921688193024) 1]), (48, [mkRat (-4297849797273472) 1]), (49, [mkRat (1424379233200000) 1]), (50, [mkRat (32643869227200) 1])]

set_option maxHeartbeats 4000000 in
theorem sing51_check : equalRelCheck (constVector s13v (51)) sing51 = true := by
  decide +kernel

theorem sing51_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing51 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing51_check]
  exact const_singular_relation f hf (51)

def sing52 : ModeRel := [(39, [mkRat (5171154044663627776) 1]), (40, [mkRat (33524445139605230528) 1]), (41, [mkRat (77065358327776241280) 1]), (42, [mkRat (52123799938567585280) 1]), (43, [mkRat (-76964924033920090112) 1]), (44, [mkRat (-169768300351783543488) 1]), (45, [mkRat (-123218003895325262976) 1]), (46, [mkRat (-36736463183774121600) 1]), (47, [mkRat (-3066628020650164224) 1]), (48, [mkRat (-145766056662251968) 1]), (49, [mkRat (13262034051925120) 1]), (50, [mkRat (1517676023533824) 1]), (51, [mkRat (-35344846684160) 1]), (52, [mkRat (1087533744128) 1])]

set_option maxHeartbeats 4000000 in
theorem sing52_check : equalRelCheck (constVector s13v (52)) sing52 = true := by
  decide +kernel

theorem sing52_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing52 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing52_check]
  exact const_singular_relation f hf (52)

def sing53 : ModeRel := [(40, [mkRat (5180938061409000000) 1]), (41, [mkRat (37142008106368608000) 1]), (42, [mkRat (102845018105734616000) 1]), (43, [mkRat (129138838195238427136) 1]), (44, [mkRat (46230317029290439296) 1]), (45, [mkRat (-57621496185356398464) 1]), (46, [mkRat (-66623174766346296000) 1]), (47, [mkRat (-22671533755730939904) 1]), (48, [mkRat (-1614890565647316480) 1]), (49, [mkRat (51873709512476544) 1]), (50, [mkRat (23100820588915776) 1]), (51, [mkRat (563424132958720) 1]), (52, [mkRat (-101084023010752) 1]), (53, [mkRat (5244601799808) 1])]

set_option maxHeartbeats 4000000 in
theorem sing53_check : equalRelCheck (constVector s13v (53)) sing53 = true := by
  decide +kernel

theorem sing53_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing53 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing53_check]
  exact const_singular_relation f hf (53)

def sing54 : ModeRel := [(41, [mkRat (4773183860560752000) 1]), (42, [mkRat (36884359431186904000) 1]), (43, [mkRat (113713890767937227264) 1]), (44, [mkRat (175258860836068407744) 1]), (45, [mkRat (132350692958790893184) 1]), (46, [mkRat (29206312157407872000) 1]), (47, [mkRat (-18534147171710109696) 1]), (48, [mkRat (-9195818149656813120) 1]), (49, [mkRat (23802466807168896) 1]), (50, [mkRat (193189077123525504) 1]), (51, [mkRat (19473929002887680) 1]), (52, [mkRat (-1074675622881728) 1]), (53, [mkRat (-106303120028928) 1]), (54, [mkRat (12969522360000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing54_check : equalRelCheck (constVector s13v (54)) sing54 = true := by
  decide +kernel

theorem sing54_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing54 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing54_check]
  exact const_singular_relation f hf (54)

end VOA.Classification.COne.OrbIcoZ
