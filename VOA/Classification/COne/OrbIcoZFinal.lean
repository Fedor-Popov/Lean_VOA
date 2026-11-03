import VOA.Classification.COne.OrbIcoZLowest
import VOA.Classification.COne.OrbIcoZConjugacy
import VOA.Classification.COne.OrbOctaZDFinal

/-! Unconditional pseudo-unitarity of every A5 orbifold and the completed B5 endpoint. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbIco

/-- Every actual A5 embedding has positive non-vacuum ordinary-module weights. -/
theorem icosahedral_orbifold_pseudoUnitary
    (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hG : Nonempty (G ≃* alternatingGroup (Fin 5))) : PseudoUnitary (orbifoldVOA G) :=
  icosahedral_pseudoUnitary_of_standard ico_pseudoUnitary_holds G hG

/-- A4, S4 and A5 positivity jointly discharge the exceptional B5 fact. -/
theorem exceptionalOrbifoldPositiveWeightsFact_holds :
    ExceptionalOrbifoldPositiveWeightsFact :=
  OrbOctaZD.exceptionalOrbifoldPositiveWeightsFact_of_icosa
    (fun G hG _ => icosahedral_orbifold_pseudoUnitary G hG)

end VOA.Classification.COne.OrbIcoZ
