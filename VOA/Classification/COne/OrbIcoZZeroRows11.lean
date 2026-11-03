import VOA.Classification.COne.OrbIcoZZeroRows10

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing76 : ModeRel := [(63, [mkRat (-202136564921532416) 1]), (64, [mkRat (-1621378742075460928) 1]), (65, [mkRat (-5306192614052272512) 1]), (66, [mkRat (-7916406334941640960) 1]), (67, [mkRat (-2089631590940327936) 1]), (68, [mkRat (9487760520525618240) 1]), (69, [mkRat (11846154050597952384) 1]), (70, [mkRat (3143356582668654720) 1]), (72, [mkRat (7360416483577606976) 1]), (73, [mkRat (12079689540897843328) 1]), (74, [mkRat (8246567451055680000) 1]), (75, [mkRat (2741229015868211200) 1]), (76, [mkRat (367847014400000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing76_check : equalRelCheck (constVector s13v (76)) sing76 = true := by
  decide +kernel

theorem sing76_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing76 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing76_check]
  exact const_singular_relation f hf (76)

def sing77 : ModeRel := [(64, [mkRat (-304633588283365824) 1]), (65, [mkRat (-1915924244209097472) 1]), (66, [mkRat (-4365827834299597120) 1]), (67, [mkRat (-2465576591549765120) 1]), (68, [mkRat (6640318793355746688) 1]), (69, [mkRat (11767591212711798912) 1]), (70, [mkRat (3651325804215426624) 1]), (72, [mkRat (19278621335807506176) 1]), (73, [mkRat (42544103351978562432) 1]), (74, [mkRat (41767623668765977920) 1]), (75, [mkRat (22384903651050433024) 1]), (76, [mkRat (6429452783015071040) 1]), (77, [mkRat (780834720355417728) 1])]

set_option maxHeartbeats 4000000 in
theorem sing77_check : equalRelCheck (constVector s13v (77)) sing77 = true := by
  decide +kernel

theorem sing77_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing77 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing77_check]
  exact const_singular_relation f hf (77)

def sing78 : ModeRel := [(65, [mkRat (-286292422674000000) 1]), (66, [mkRat (-1375283036243912000) 1]), (67, [mkRat (-1395448605164224000) 1]), (68, [mkRat (3676211265410963136) 1]), (69, [mkRat (9157635611801901696) 1]), (70, [mkRat (3231893102942689536) 1]), (72, [mkRat (38106913048517436096) 1]), (73, [mkRat (109861917604480513920) 1]), (74, [mkRat (146648302427770210944) 1]), (75, [mkRat (113399665717869195776) 1]), (76, [mkRat (52580179000536704320) 1]), (77, [mkRat (13675243876667912448) 1]), (78, [mkRat (1543557111807791808) 1])]

set_option maxHeartbeats 4000000 in
theorem sing78_check : equalRelCheck (constVector s13v (78)) sing78 = true := by
  decide +kernel

theorem sing78_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing78 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing78_check]
  exact const_singular_relation f hf (78)

def sing79 : ModeRel := [(66, [mkRat (-164887994889728000) 1]), (67, [mkRat (-329775989779456000) 1]), (68, [mkRat (1668866080399467264) 1]), (69, [mkRat (5518463489962703744) 1]), (70, [mkRat (2153476653047944384) 1]), (72, [mkRat (57733239968998514304) 1]), (73, [mkRat (214402779802060452480) 1]), (74, [mkRat (377419808351928136896) 1]), (75, [mkRat (398012050961513314304) 1]), (76, [mkRat (266601499585155758080) 1]), (77, [mkRat (111999426927953830272) 1]), (78, [mkRat (27080235285549527872) 1]), (79, [mkRat (2888343876239360000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing79_check : equalRelCheck (constVector s13v (79)) sing79 = true := by
  decide +kernel

theorem sing79_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing79 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing79_check]
  exact const_singular_relation f hf (79)

def sing81 : ModeRel := [(68, [mkRat (120015571460076864) 1]), (69, [mkRat (762752909488886272) 1]), (70, [mkRat (341371264257750848) 1]), (72, [mkRat (59706218186835400704) 1]), (73, [mkRat (368754650089354588800) 1]), (74, [mkRat (1091474402298994413504) 1]), (75, [mkRat (1983442234156125611520) 1]), (76, [mkRat (2403116543176307564160) 1]), (77, [mkRat (1994555999428878485376) 1]), (78, [mkRat (1127075306280117457088) 1]), (79, [mkRat (416325840010215424000) 1]), (80, [mkRat (90936811372455748800) 1]), (81, [mkRat (8928242694126000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing81_check : equalRelCheck (constVector s13v (81)) sing81 = true := by
  decide +kernel

theorem sing81_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing81 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing81_check]
  exact const_singular_relation f hf (81)

def sing82 : ModeRel := [(69, [mkRat (116861334187056256) 1]), (70, [mkRat (58430667093528128) 1]), (72, [mkRat (39402241663327400000) 1]), (73, [mkRat (322308327668199979648) 1]), (74, [mkRat (1245260320573838654592) 1]), (75, [mkRat (2939401505799877830144) 1]), (76, [mkRat (4648394547779135430720) 1]), (77, [mkRat (5115923752920043625856) 1]), (78, [mkRat (3953661278350323206912) 1]), (79, [mkRat (2113240442527215278080) 1]), (80, [mkRat (746340319205611107264) 1]), (81, [mkRat (157071364994398190080) 1]), (82, [mkRat (14944168142353216448) 1])]

set_option maxHeartbeats 4000000 in
theorem sing82_check : equalRelCheck (constVector s13v (82)) sing82 = true := by
  decide +kernel

theorem sing82_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing82 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing82_check]
  exact const_singular_relation f hf (82)

end VOA.Classification.COne.OrbIcoZ
