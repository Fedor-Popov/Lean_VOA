import VOA.Classification.COne.OrbIcoZZeroRows07

/-! Kernel certificates for the actual zero-conformal-fiber mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def sing55 : ModeRel := [(42, [mkRat (4040850818368000000) 1]), (43, [mkRat (33397351916211691520) 1]), (44, [mkRat (111349352286746519040) 1]), (45, [mkRat (192056856384486903680) 1]), (46, [mkRat (180134857194708568000) 1]), (47, [mkRat (86032496283233310720) 1]), (48, [mkRat (16041025757379811200) 1]), (49, [mkRat (1040429635418870400) 1]), (50, [mkRat (1175403820192781760) 1]), (51, [mkRat (219479785966745600) 1]), (52, [mkRat (3580525374565120) 1]), (53, [mkRat (-2515711465180800) 1]), (54, [mkRat (-345254360000) 1]), (55, [mkRat (22901424128000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing55_check : equalRelCheck (constVector s13v (55)) sing55 = true := by
  decide +kernel

theorem sing55_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing55 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing55_check]
  exact const_singular_relation f hf (55)

def sing56 : ModeRel := [(43, [mkRat (3089941272125374464) 1]), (44, [mkRat (27498927001978942272) 1]), (45, [mkRat (98325447934209362048) 1]), (46, [mkRat (183634417799539907200) 1]), (47, [mkRat (192654165757587093504) 1]), (48, [mkRat (112894292274199800000) 1]), (49, [mkRat (35382169649154539904) 1]), (50, [mkRat (6816218331014507520) 1]), (51, [mkRat (1536970493367375360) 1]), (52, [mkRat (129865595608061376) 1]), (53, [mkRat (-16939391603363712) 1]), (54, [mkRat (-2720555607056000) 1]), (55, [mkRat (225055829196800) 1]), (56, [mkRat (31461696000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing56_check : equalRelCheck (constVector s13v (56)) sing56 = true := by
  decide +kernel

theorem sing56_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing56 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing56_check]
  exact const_singular_relation f hf (56)

def sing57 : ModeRel := [(44, [mkRat (2030754310244801856) 1]), (45, [mkRat (20098801820965424128) 1]), (46, [mkRat (77794183638695950400) 1]), (47, [mkRat (155908227877584998400) 1]), (48, [mkRat (176328605149577326848) 1]), (49, [mkRat (113695227052415640192) 1]), (50, [mkRat (40603695835935524544) 1]), (51, [mkRat (8202606077876805120) 1]), (52, [mkRat (1152040833837699456) 1]), (53, [mkRat (-26233616747023488) 1]), (54, [mkRat (-31190119710790720) 1]), (55, [mkRat (-1013386672295936) 1]), (56, [mkRat (508775119634880) 1]), (57, [mkRat (33736037182848) 1])]

set_option maxHeartbeats 4000000 in
theorem sing57_check : equalRelCheck (constVector s13v (57)) sing57 = true := by
  decide +kernel

theorem sing57_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing57 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing57_check]
  exact const_singular_relation f hf (57)

def sing58 : ModeRel := [(45, [mkRat (969385263418000000) 1]), (46, [mkRat (12117315792725000000) 1]), (47, [mkRat (53148598263532800000) 1]), (48, [mkRat (115811749245373718336) 1]), (49, [mkRat (139737192721909442176) 1]), (50, [mkRat (95046541882061809536) 1]), (51, [mkRat (34909136364670195200) 1]), (52, [mkRat (6243876342316658496) 1]), (53, [mkRat (315177310753545600) 1]), (54, [mkRat (-172471218882174976) 1]), (55, [mkRat (-29793575910170624) 1]), (56, [mkRat (2428563641192640) 1]), (57, [mkRat (719211412261888) 1]), (58, [mkRat (26090310454208) 1])]

set_option maxHeartbeats 4000000 in
theorem sing58_check : equalRelCheck (constVector s13v (58)) sing58 = true := by
  decide +kernel

theorem sing58_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing58 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing58_check]
  exact const_singular_relation f hf (58)

def sing60 : ModeRel := [(47, [mkRat (-801628213248000000) 1]), (48, [mkRat (-2304222314679590720) 1]), (49, [mkRat (4346326957519099520) 1]), (50, [mkRat (26495795037854419200) 1]), (51, [mkRat (43268872803739852800) 1]), (52, [mkRat (31471766227182434880) 1]), (53, [mkRat (8494024479823612800) 1]), (54, [mkRat (-1278544777334931840) 1]), (55, [mkRat (-1117605382513520640) 1]), (56, [mkRat (-180650719836216000) 1]), (57, [mkRat (23418286228856960) 1]), (58, [mkRat (8645696444369920) 1]), (59, [mkRat (329080320000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing60_check : equalRelCheck (constVector s13v (60)) sing60 = true := by
  decide +kernel

theorem sing60_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing60 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing60_check]
  exact const_singular_relation f hf (60)

def sing61 : ModeRel := [(48, [mkRat (-1382900427534481856) 1]), (49, [mkRat (-7484643698695491328) 1]), (50, [mkRat (-14602300398165033792) 1]), (51, [mkRat (-10766421843980592640) 1]), (52, [mkRat (209221741210831744) 1]), (53, [mkRat (1571296200906360960) 1]), (54, [mkRat (-3682059966602659776) 1]), (55, [mkRat (-3836238255900487680) 1]), (56, [mkRat (-1122132716383553280) 1]), (57, [mkRat (-17847965986743424) 1]), (58, [mkRat (54765996281558848) 1]), (59, [mkRat (7173165787200000) 1]), (60, [mkRat (-305034587000000) 1]), (61, [mkRat (22729850000000) 1])]

set_option maxHeartbeats 4000000 in
theorem sing61_check : equalRelCheck (constVector s13v (61)) sing61 = true := by
  decide +kernel

theorem sing61_holds {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    evalConst Wi f selfMode sing61 = 0 := by
  rw [← equalConstCheck_sound Wi f hf selfMode sing61_check]
  exact const_singular_relation f hf (61)

end VOA.Classification.COne.OrbIcoZ
