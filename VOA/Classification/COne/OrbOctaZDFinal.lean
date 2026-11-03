import VOA.Classification.COne.OrbOctaZDSeed144
import VOA.Classification.COne.OrbB5Main

/-! Unconditional octahedral vacuum uniqueness and pseudo-unitarity. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA OrbOctaZ OrbOctaZC OrbOcta OrbZhu Polynomial OrbC2b

/-- All four non-vacuum towers satisfy the positive factor of P25. -/
theorem q24_seeds : ∀ i : Fin 4,
    aeval (omegaL W) positivePolynomial (mk W (octaSeeds i.succ)) = 0 := by
  intro i
  fin_cases i
  · exact q24_seed_one
  · exact q24_seed_two
  · exact q24_seed_three
  · exact q24_seed_four

/-- The intrinsic octahedral zero conformal fiber is the vacuum fiber. -/
theorem OctahedralVacuumFiber_holds : OctahedralVacuumFiber :=
  vacuumFiber_of_positive_annihilators q24_seeds

/-- No strong-rationality premise is required for the standard S4 orbifold. -/
theorem octa_pseudoUnitary_holds : PseudoUnitary (orbifoldVOA octa) :=
  octa_pseudoUnitary_of_vacuumFiber OctahedralVacuumFiber_holds

/-- The five tower heights are 25, 24, 24, 24, 24. -/
theorem octa_zhu_finrank_le_121 : Module.finrank ℂ (A W) ≤ 121 :=
  finrank_le_121_of_vacuumFiber OctahedralVacuumFiber_holds

/-- B5 has only the A5 case remaining. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_icosa
    (hIcosa : ∀ G : Subgroup (Aut (V2m 1 le_rfl)),
      Nonempty (G ≃* alternatingGroup (Fin 5)) →
      StronglyRational (orbifoldVOA G) → PseudoUnitary (orbifoldVOA G)) :
    ExceptionalOrbifoldPositiveWeightsFact :=
  OrbB5.exceptionalOrbifoldPositiveWeightsFact_of_octa_icosa
    (fun _ => octa_pseudoUnitary_holds) hIcosa

end VOA.Classification.COne.OrbOctaZD
