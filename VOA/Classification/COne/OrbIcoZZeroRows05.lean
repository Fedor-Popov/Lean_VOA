import VOA.Classification.COne.OrbIcoZZeroRows04

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing36 : ModeRel := [(23, [mkRat (-6578801738835296256) 1]), (24, [mkRat (43537576085805748672) 1]), (25, [mkRat (614709281300201633408) 1]), (26, [mkRat (2357420313551078338560) 1]), (27, [mkRat (4364487131704402796544) 1]), (28, [mkRat (4074837587435920100160) 1]), (29, [mkRat (1298964002253926730624) 1]), (30, [mkRat (-789858691257550231680) 1]), (31, [mkRat (-725475285013506478080) 1]), (32, [mkRat (-115138904506823231424) 1]), (33, [mkRat (24302649181524434048) 1]), (34, [mkRat (-389615455546400000) 1]), (35, [mkRat (237027409920000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing36_check : equalRelCheck (constVector s13v (36)) sing36 = true := by
  decide +kernel

theorem sing36_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing36 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing36_check]
  exact const_singular_relation f hf (36)

def sing37 : ModeRel := [(24, [mkRat (-11655259820496188864) 1]), (25, [mkRat (-17235616937791343872) 1]), (26, [mkRat (335906156062911107520) 1]), (27, [mkRat (1721444665917684984320) 1]), (28, [mkRat (3652613497515403182208) 1]), (29, [mkRat (3904548552058344607872) 1]), (30, [mkRat (1786974671628513017664) 1]), (31, [mkRat (-230485785614919720960) 1]), (32, [mkRat (-508308721057712600064) 1]), (33, [mkRat (-108806750794711470208) 1]), (34, [mkRat (13817317194318091840) 1]), (35, [mkRat (-118382437430724096) 1]), (36, [mkRat (-30422536249280) 1]), (37, [mkRat (46984611968) 1])]

set_option maxHeartbeats 4000000 in
theorem sing37_check : equalRelCheck (constVector s13v (37)) sing37 = true := by
  decide +kernel

theorem sing37_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing37 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing37_check]
  exact const_singular_relation f hf (37)

def sing38 : ModeRel := [(25, [mkRat (-15202142965674000000) 1]), (26, [mkRat (-65691768249244008000) 1]), (27, [mkRat (92204471669271104000) 1]), (28, [mkRat (1110255053635478297536) 1]), (29, [mkRat (2851376451431575971456) 1]), (30, [mkRat (3479066975055009486336) 1]), (31, [mkRat (1980777955502995814400) 1]), (32, [mkRat (163634178760006159296) 1]), (33, [mkRat (-321057429609756270720) 1]), (34, [mkRat (-92016516898426797696) 1]), (35, [mkRat (7128473607475186176) 1]), (36, [mkRat (-21083018313237440) 1]), (37, [mkRat (8549342275328) 1]), (38, [mkRat (38480764608) 1])]

set_option maxHeartbeats 4000000 in
theorem sing38_check : equalRelCheck (constVector s13v (38)) sing38 = true := by
  decide +kernel

theorem sing38_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing38 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing38_check]
  exact const_singular_relation f hf (38)

def sing39 : ModeRel := [(26, [mkRat (-17272278029901312000) 1]), (27, [mkRat (-101209251552932864000) 1]), (28, [mkRat (-108397511146310004736) 1]), (29, [mkRat (557509819727565903744) 1]), (30, [mkRat (2034820424598905993664) 1]), (31, [mkRat (2891986732012858521600) 1]), (32, [mkRat (1945346122877451525504) 1]), (33, [mkRat (408746510229139374720) 1]), (34, [mkRat (-171815889105280855104) 1]), (35, [mkRat (-71151099113390155776) 1]), (36, [mkRat (3205298538036573440) 1]), (37, [mkRat (2519073170342272) 1]), (38, [mkRat (11505748617792) 1])]

set_option maxHeartbeats 4000000 in
theorem sing39_check : equalRelCheck (constVector s13v (39)) sing39 = true := by
  decide +kernel

theorem sing39_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing39 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing39_check]
  exact const_singular_relation f hf (39)

def sing40 : ModeRel := [(27, [mkRat (-17985862264832000000) 1]), (28, [mkRat (-123952640684439367360) 1]), (29, [mkRat (-261674397693788284800) 1]), (30, [mkRat (87184565677325294720) 1]), (31, [mkRat (1263009927076221798400) 1]), (32, [mkRat (2227122575429493493440) 1]), (33, [mkRat (1746694212953103139200) 1]), (34, [mkRat (528980606125287928320) 1]), (35, [mkRat (-62395472671596771840) 1]), (36, [mkRat (-50544832323966836800) 1]), (37, [mkRat (1145282338724022400) 1]), (38, [mkRat (2457066616583040) 1]), (39, [mkRat (-9525739520000) 1]), (40, [mkRat (59535872000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing40_check : equalRelCheck (constVector s13v (40)) sing40 = true := by
  decide +kernel

theorem sing40_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing40 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing40_check]
  exact const_singular_relation f hf (40)

def sing41 : ModeRel := [(28, [mkRat (-17516226533963242176) 1]), (29, [mkRat (-134756581411010377728) 1]), (30, [mkRat (-366832161070001885632) 1]), (31, [mkRat (-286185306130757550080) 1]), (32, [mkRat (580946786118163056384) 1]), (33, [mkRat (1555021978029917819520) 1]), (34, [mkRat (1446929586340713726144) 1]), (35, [mkRat (552385103294541381120) 1]), (36, [mkRat (9936683567994180480) 1]), (37, [mkRat (-32771451503470007424) 1]), (38, [mkRat (229355173825449408) 1]), (39, [mkRat (-679279090688000) 1]), (40, [mkRat (-11558915291200) 1]), (41, [mkRat (175446000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing41_check : equalRelCheck (constVector s13v (41)) sing41 = true := by
  decide +kernel

theorem sing41_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing41 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing41_check]
  exact const_singular_relation f hf (41)

end VOA.Classification.COne.OrbIcoZ
