import VOA.Classification.COne.OrbIcoZZeroRows01

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing16 : ModeRel := [(3, [mkRat (-156759497752577048576) 1]), (4, [mkRat (-2246388167519543393728) 1]), (5, [mkRat (-11567586304942786242432) 1]), (6, [mkRat (-27415661605000314954880) 1]), (7, [mkRat (-23499031532014220066816) 1]), (8, [mkRat (28059391725784109046720) 1]), (9, [mkRat (89756586179644958300544) 1]), (10, [mkRat (87374775198509956197120) 1]), (11, [mkRat (28826189072779898119680) 1]), (12, [mkRat (-10371186032688969519424) 1]), (13, [mkRat (-9102428711868059499392) 1]), (14, [mkRat (-657359387972220528000) 1]), (15, [mkRat (463990788362218700800) 1]), (16, [mkRat (-22612685765824000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing16_check : equalRelCheck (constVector s13v (16)) sing16 = true := by
  decide +kernel

theorem sing16_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing16 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing16_check]
  exact const_singular_relation f hf (16)

def sing17 : ModeRel := [(4, [mkRat (-111298333599695841984) 1]), (5, [mkRat (-1834820862758031785472) 1]), (6, [mkRat (-10360601004395039469760) 1]), (7, [mkRat (-27351985036146657935360) 1]), (8, [mkRat (-31412554167201270239232) 1]), (9, [mkRat (7127631604896142733952) 1]), (10, [mkRat (64490849330198523393984) 1]), (11, [mkRat (74090148090480735413760) 1]), (12, [mkRat (30588749819747606783616) 1]), (13, [mkRat (-4745023020270358681728) 1]), (14, [mkRat (-7025713166576204654400) 1]), (15, [mkRat (-765938798720934035456) 1]), (16, [mkRat (336290361530572602560) 1]), (17, [mkRat (-14290086638642550912) 1])]

set_option maxHeartbeats 4000000 in
theorem sing17_check : equalRelCheck (constVector s13v (17)) sing17 = true := by
  decide +kernel

theorem sing17_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing17 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing17_check]
  exact const_singular_relation f hf (17)

def sing18 : ModeRel := [(5, [mkRat (-69359401737054000000) 1]), (6, [mkRat (-1421723693971429784000) 1]), (7, [mkRat (-8926641630631948288000) 1]), (8, [mkRat (-25998817207303741155264) 1]), (9, [mkRat (-35921710908300842542464) 1]), (10, [mkRat (-8962461567524764040064) 1]), (11, [mkRat (42448216684263109977600) 1]), (12, [mkRat (60344253421040838674496) 1]), (13, [mkRat (29908629843324405144960) 1]), (14, [mkRat (-739255924410247593216) 1]), (15, [mkRat (-5239010591388199757824) 1]), (16, [mkRat (-773526647422632825920) 1]), (17, [mkRat (239484850331033184768) 1]), (18, [mkRat (-8860483409758972992) 1])]

set_option maxHeartbeats 4000000 in
theorem sing18_check : equalRelCheck (constVector s13v (18)) sing18 = true := by
  decide +kernel

theorem sing18_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing18 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing18_check]
  exact const_singular_relation f hf (18)

def sing19 : ModeRel := [(6, [mkRat (-32017571633954816000) 1]), (7, [mkRat (-1024562292286554112000) 1]), (8, [mkRat (-7371823533613605956736) 1]), (9, [mkRat (-23684025434088487037056) 1]), (10, [mkRat (-37566552669435547791296) 1]), (11, [mkRat (-20561881326679861516800) 1]), (12, [mkRat (23957706280212358658304) 1]), (13, [mkRat (47027720741643166938240) 1]), (14, [mkRat (27564762644415374930496) 1]), (15, [mkRat (1931150674826606557184) 1]), (16, [mkRat (-3755987120111754154880) 1]), (17, [mkRat (-719500444066502195328) 1]), (18, [mkRat (167434219990281180352) 1]), (19, [mkRat (-5380618387456000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing19_check : equalRelCheck (constVector s13v (19)) sing19 = true := by
  decide +kernel

theorem sing19_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing19 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing19_check]
  exact const_singular_relation f hf (19)

def sing21 : ModeRel := [(8, [mkRat (26286847547096291904) 1]), (9, [mkRat (-329831718390084124928) 1]), (10, [mkRat (-4250473027005015748672) 1]), (11, [mkRat (-17357113009039582840320) 1]), (12, [mkRat (-34470434410540797653376) 1]), (13, [mkRat (-32302175896848579227520) 1]), (14, [mkRat (-2278922326869842732736) 1]), (15, [mkRat (23982689156539050577920) 1]), (16, [mkRat (20338448850864072445440) 1]), (17, [mkRat (4336956279106054805376) 1]), (18, [mkRat (-1645313846886240567232) 1]), (19, [mkRat (-531986151853048256000) 1]), (20, [mkRat (77099857389628315200) 1]), (21, [mkRat (-1847663877150000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing21_check : equalRelCheck (constVector s13v (21)) sing21 = true := by
  decide +kernel

theorem sing21_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing21 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing21_check]
  exact const_singular_relation f hf (21)

def sing22 : ModeRel := [(9, [mkRat (46723428259186496896) 1]), (10, [mkRat (-49459947827163844672) 1]), (11, [mkRat (-2820272831224899171840) 1]), (12, [mkRat (-13855580396109356991040) 1]), (13, [mkRat (-30783177879130628108672) 1]), (14, [mkRat (-33612084997819440519168) 1]), (15, [mkRat (-10429086127514632144896) 1]), (16, [mkRat (14879111166627693458880) 1]), (17, [mkRat (16365953294590668160896) 1]), (18, [mkRat (4542977523037465876352) 1]), (19, [mkRat (-958237784525557552640) 1]), (20, [mkRat (-431389242330940218816) 1]), (21, [mkRat (50633756764240249600) 1]), (22, [mkRat (-1039197222119248192) 1])]

set_option maxHeartbeats 4000000 in
theorem sing22_check : equalRelCheck (constVector s13v (22)) sing22 = true := by
  decide +kernel

theorem sing22_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing22 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing22_check]
  exact const_singular_relation f hf (22)

end VOA.Classification.COne.OrbIcoZ
