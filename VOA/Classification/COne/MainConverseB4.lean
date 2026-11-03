import VOA.Classification.COne.MainConverseB5
import VOA.Classification.COne.OrbIcoVSpecializeClose

/-! The actual icosahedral symbol relations are proved. The classification
converse then retains only the full exceptional-rationality input. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne

/-- Xu's actual icosahedral Poisson relations, including every A5 embedding. -/
theorem xuIcosahedralPoissonRelations_holds : XuIcosahedralPoissonRelations :=
  OrbIco.xuIcosahedralPoissonRelations_of_symbols OrbIcoV.icoSymbolRelations_holds

/-- Every actual icosahedral orbifold is C2-cofinite, with the proved 58-dimensional bound. -/
theorem icosahedral_c2Cofinite_holds
    (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hG : Nonempty (G ≃* alternatingGroup (Fin 5))) :
    C2Cofinite (orbifoldVOA G) ∧ Module.finrank ℂ (A₂ (orbifoldVOA G))≤58 :=
  OrbIco.icosa_c2_of_symbols OrbIcoV.icoSymbolRelations_holds G hG

/-- Only exceptional-orbifold rationality remains in the classification converse. -/
theorem gannonRayhaunConverse_of_B3 (hRat : FiniteV2OrbifoldRationalOfC2Fact) :
    GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_B3_B4 xuIcosahedralPoissonRelations_holds hRat

end VOA.Classification.COne
