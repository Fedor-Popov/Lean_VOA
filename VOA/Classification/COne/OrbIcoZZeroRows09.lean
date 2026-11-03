import VOA.Classification.COne.OrbIcoZZeroRows08

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing62 : ModeRel := [(49, [mkRat (-1717169112040846464) 1]), (50, [mkRat (-10813044044300887872) 1]), (51, [mkRat (-27661373084070714880) 1]), (52, [mkRat (-37597700832609462080) 1]), (53, [mkRat (-31363081191211588992) 1]), (54, [mkRat (-19805752023366505728) 1]), (55, [mkRat (-11197417557053300736) 1]), (56, [mkRat (-4432193030057751360) 1]), (57, [mkRat (-587286637393217664) 1]), (58, [mkRat (185417139884376192) 1]), (59, [mkRat (65961113272496640) 1]), (60, [mkRat (995861749943104) 1]), (61, [mkRat (-838955314574080) 1]), (62, [mkRat (122642649125568) 1])]

set_option maxHeartbeats 4000000 in
theorem sing62_check : equalRelCheck (constVector s13v (62)) sing62 = true := by
  decide +kernel

theorem sing62_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing62 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing62_check]
  exact const_singular_relation f hf (62)

def sing63 : ModeRel := [(50, [mkRat (-1804307908032000000) 1]), (51, [mkRat (-12201532522339328000) 1]), (52, [mkRat (-34220489359546336000) 1]), (53, [mkRat (-52218830465539726464) 1]), (54, [mkRat (-48672080073411918144) 1]), (55, [mkRat (-30246207425030897664) 1]), (56, [mkRat (-13042223455419849600) 1]), (57, [mkRat (-3097971436473400704) 1]), (58, [mkRat (256063920548479680) 1]), (59, [mkRat (330640417764808704) 1]), (60, [mkRat (42777017553138176) 1]), (61, [mkRat (-8207997451955840) 1]), (62, [mkRat (-548661868961472) 1]), (63, [mkRat (352046653636608) 1])]

set_option maxHeartbeats 4000000 in
theorem sing63_check : equalRelCheck (constVector s13v (63)) sing63 = true := by
  decide +kernel

theorem sing63_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing63 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing63_check]
  exact const_singular_relation f hf (63)

def sing64 : ModeRel := [(51, [mkRat (-1669013302280192000) 1]), (52, [mkRat (-11784817540916824000) 1]), (53, [mkRat (-34539298775130404736) 1]), (54, [mkRat (-54801169130107632256) 1]), (55, [mkRat (-51717822935945179136) 1]), (56, [mkRat (-29955596062912718400) 1]), (57, [mkRat (-9858778704441722496) 1]), (58, [mkRat (-537702566510503680) 1]), (59, [mkRat (1030810658087056896) 1]), (60, [mkRat (325237175041913024) 1]), (61, [mkRat (-14992548264076160) 1]), (62, [mkRat (-15185884512889728) 1]), (63, [mkRat (1563567559278592) 1]), (64, [mkRat (753107264000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing64_check : equalRelCheck (constVector s13v (64)) sing64 = true := by
  decide +kernel

theorem sing64_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing64 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing64_check]
  exact const_singular_relation f hf (64)

def sing65 : ModeRel := [(52, [mkRat (-1356936276915000000) 1]), (53, [mkRat (-9890148437143810560) 1]), (54, [mkRat (-29643929225573790400) 1]), (55, [mkRat (-47252472751492935680) 1]), (56, [mkRat (-42965474213310681600) 1]), (57, [mkRat (-21402284536665701760) 1]), (58, [mkRat (-3603837696002356800) 1]), (59, [mkRat (2125794456444741120) 1]), (60, [mkRat (1350521943912620160) 1]), (61, [mkRat (129278014056931200) 1]), (62, [mkRat (-85721572615982400) 1]), (63, [mkRat (-11347857346703360) 1]), (64, [mkRat (6471577319480000) 1]), (65, [mkRat (1326786722352000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing65_check : equalRelCheck (constVector s13v (65)) sing65 = true := by
  decide +kernel

theorem sing65_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing65 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing65_check]
  exact const_singular_relation f hf (65)

def sing66 : ModeRel := [(53, [mkRat (-928911222036475776) 1]), (54, [mkRat (-6988303567938081728) 1]), (55, [mkRat (-21140012768479608832) 1]), (56, [mkRat (-32789237382108665280) 1]), (57, [mkRat (-26682952307956780416) 1]), (58, [mkRat (-8574769001371447680) 1]), (59, [mkRat (3072866695668831744) 1]), (60, [mkRat (3734736185286765120) 1]), (61, [mkRat (982920344522321280) 1]), (62, [mkRat (-204634798562375424) 1]), (63, [mkRat (-124718828818081792) 1]), (64, [mkRat (13031350400152000) 1]), (65, [mkRat (14573170236556800) 1]), (66, [mkRat (1993435191000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing66_check : equalRelCheck (constVector s13v (66)) sing66 = true := by
  decide +kernel

theorem sing66_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing66 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing66_check]
  exact const_singular_relation f hf (66)

def sing67 : ModeRel := [(54, [mkRat (-453720909685981184) 1]), (55, [mkRat (-3629767277487849472) 1]), (56, [mkRat (-10960241453880658560) 1]), (57, [mkRat (-15343038196585644160) 1]), (58, [mkRat (-8013666964018269632) 1]), (59, [mkRat (4032278212725130752) 1]), (60, [mkRat (7617462677540669184) 1]), (61, [mkRat (3521300260402680960) 1]), (62, [mkRat (-9858625708699584) 1]), (63, [mkRat (-517808043848316928) 1]), (64, [mkRat (-74243838690492800) 1]), (65, [mkRat (64201805535106944) 1]), (66, [mkRat (24944508507232960) 1]), (67, [mkRat (2559771083276288) 1])]

set_option maxHeartbeats 4000000 in
theorem sing67_check : equalRelCheck (constVector s13v (67)) sing67 = true := by
  decide +kernel

theorem sing67_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing67 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing67_check]
  exact const_singular_relation f hf (67)

end VOA.Classification.COne.OrbIcoZ
