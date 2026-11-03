import VOA.Classification.COne.OrbIcoZSymbolWords25

/-! Cached finite-vector assembly for the all-mode null identity. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

theorem evalSym_nil {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) : evalSym W k a [] = 0 := rfl

def vectorChunk0 : VVec := ofRaw [(32201368288215552, 1, [13]), (-6281863658835392, 1, [12, 1]), (-4139544511687680, 1, [11, 2]), (631608657218720, 1, [11, 1, 1]), (-3384108036172800, 1, [10, 3]), (878216741754880, 1, [10, 2, 1]), (-46025529519168, 1, [10, 1, 1, 1]), (-3169018363521024, 1, [9, 4]), (709434423742240, 1, [9, 3, 1]), (303644410656768, 1, [9, 2, 2])]

def rawChunk0 : RawSym :=
  rawScale [[mkRat (32201368288215552) 1]] wordCache201 ++
  rawScale [[mkRat (-6281863658835392) 1]] wordCache200 ++
  rawScale [[mkRat (-4139544511687680) 1]] wordCache199 ++
  rawScale [[mkRat (631608657218720) 1]] wordCache198 ++
  rawScale [[mkRat (-3384108036172800) 1]] wordCache197 ++
  rawScale [[mkRat (878216741754880) 1]] wordCache196 ++
  rawScale [[mkRat (-46025529519168) 1]] wordCache195 ++
  rawScale [[mkRat (-3169018363521024) 1]] wordCache194 ++
  rawScale [[mkRat (709434423742240) 1]] wordCache193 ++
  rawScale [[mkRat (303644410656768) 1]] wordCache192

theorem vectorChunk0_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symVector vectorChunk0) = evalSym W k a (symMap rawChunk0) := by
  simp only [vectorChunk0, rawChunk0, ofRaw, List.map_cons, List.map_nil,
    symVector, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_nil,
    symMap_append, symMap_scale]
  rw [wordCache201_sound W k a, wordCache200_sound W k a, wordCache199_sound W k a, wordCache198_sound W k a, wordCache197_sound W k a, wordCache196_sound W k a, wordCache195_sound W k a, wordCache194_sound W k a, wordCache193_sound W k a, wordCache192_sound W k a]
  simp [bp, qp, add_assoc]

def vectorPartial0 : RawSym := [(0, [[(398981699105364532224:ℚ), (37772754614446360960:ℚ), (-1561303864735915520:ℚ), (-2429155285254144:ℚ)], [(-32862836243821091264:ℚ), (-3009782561926319040:ℚ), (24416856436834816:ℚ), (0:ℚ)], [(920234274727486784:ℚ), (64244587051536512:ℚ), (0:ℚ), (0:ℚ)], [(-10824499327186112:ℚ), (-414229765672512:ℚ), (0:ℚ), (0:ℚ)], [(46025529519168:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-39006799950384702720:ℚ), (-4542037099792512128:ℚ), (19254901455669760:ℚ)], [(1797901193159343776:ℚ), (151681263268197120:ℚ), (0:ℚ)], [(-27387904414158816:ℚ), (-1242689297017536:ℚ), (0:ℚ)], [(138076588557504:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-271839623520439475200:ℚ), (-32752870061159485440:ℚ), (-170040869967790080:ℚ)], [(-947331512885035488:ℚ), (-552262267205241472:ℚ), (-4858310570508288:ℚ)], [(882292316644692864:ℚ), (99012471474726208:ℚ), (0:ℚ)], [(-21289232012360288:ℚ), (-1242689297017536:ℚ), (0:ℚ)], [(138076588557504:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(253536431274194857600:ℚ), (26713697909783987200:ℚ)], [(-1276307743087400704:ℚ), (252246842004050816:ℚ)], [(-6344606415220448:ℚ), (3471164582873536:ℚ)], [(-3712748090988576:ℚ), (-414229765672512:ℚ)], [(46025529519168:ℚ), (0:ℚ)]]),
 (4, [[(9826414713525816000:ℚ), (1048150902776087040:ℚ)], [(-5006836959237206880:ℚ), (-520087263614954240:ℚ)], [(-10970004628056320:ℚ), (-8104630675192064:ℚ)], [(1013078834399008:ℚ), (0:ℚ)]]),
 (9, [[(1773945860589400780800:ℚ), (42893997225685688320:ℚ), (85020434983895040:ℚ)], [(-38531768217228857600:ℚ), (-414131300028852736:ℚ), (303644410656768:ℚ)], [(123421755246346208:ℚ), (-2026157668798016:ℚ), (0:ℚ)], [(1013078834399008:ℚ), (0:ℚ), (0:ℚ)]]),
 (10, [[(6386291328464178203520:ℚ), (-16700162607426009600:ℚ)], [(-245960299108996723872:ℚ), (-172242524025306560:ℚ)], [(2636056814237301632:ℚ), (-540652105729600:ℚ)], [(-3344543854835232:ℚ), (0:ℚ)], [(-46025529519168:ℚ), (0:ℚ)]]),
 (11, [[(4481643979676791948160:ℚ), (205839303543982080:ℚ)], [(-353908493299250281728:ℚ), (449546941045492736:ℚ)], [(6233008428101734752:ℚ), (1485505563068416:ℚ)], [(-20184619303900256:ℚ), (0:ℚ)], [(-138076588557504:ℚ), (0:ℚ)]]),
 (12, [[(-578247623394960021440:ℚ)], [(-147466932315083160544:ℚ)], [(4993370675340427456:ℚ)], [(-26283291705698784:ℚ)], [(-138076588557504:ℚ)]]),
 (13, [[(-268394919626937761280:ℚ)], [(479133069928024704:ℚ)], [(1272997306229648128:ℚ)], [(-10456295091032768:ℚ)], [(-46025529519168:ℚ)]])]

def prefixVector0 : VVec := vectorChunk0

set_option maxHeartbeats 4000000 in
-- Add ten already cached words; no singular-word recursion is recomputed.
theorem vectorPartial0_check : equalRawCheck (rawChunk0) vectorPartial0 = true := by
  decide +kernel

theorem vectorPartial0_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symVector prefixVector0) = evalSym W k a (symMap vectorPartial0) := by
  rw [prefixVector0, vectorChunk0_sound W k a]
  exact equalRawCheck_sound W k a vectorPartial0_check

end VOA.Classification.COne.OrbIcoZ
