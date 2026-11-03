/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDEBlock
import VOA.DeligneAudit.A2DivisorTop
import VOA.DeligneAudit.DeligneMLDEProduct

/-!
# A₂: the Kac–Wakimoto input replaced by the Arakawa–Kawasetsu MLDE

For `W = L_{-3/2}(sl₃)` (`h∨ = 3`, `c = -8`), the formal MLDE machinery of `DeligneMLDEBlock`
turns the weight-four trace identity

  `S(L[-2]²|0⟩) = 36 · G₄ ⋆ S(|0⟩)`      (`κ = (h∨+1)(5h∨-6) = 36`)

into `dim W_N = mldeCoeff 3 N` for every `N`.  Together with the q-series identity
`A2ProductMLDE` (`∏(1+q^r)^8` solves the same recurrence) this gives `KacWakimotoLowerBound`, with
equality.  The A₂ headline then rests on U5, U6, the trace identity and the product identity.

The trace identity follows from the algebraic statement `SqC2QuarticRelation W 36`
(`vacuumQuarticRelation_of_sqC2`).
-/

namespace VOA.DeligneAudit.A2

open VOA VOA.AffineSl3 VOA.DeligneAudit.DeligneMLDE VOA.DeligneHigherRankConditionalCapstone

/-- `c(L_{-3/2}(sl₃)) = -8 = -2(h∨+1)`. -/
theorem W_centralCharge : W.centralCharge = -2 * (((3 : ℕ) : ℂ) + 1) := by
  rw [simple_centralCharge]
  norm_num

/-- **The graded dimensions of `L_{-3/2}(sl₃)` solve the `h∨ = 3` AK recurrence**, from the
weight-four trace identity. -/
theorem isAKSolution_of_vacuumQuarticRelation (hrel : VacuumQuarticRelation W 36) :
    IsAKSolution 3 (fun N : ℕ => (Module.finrank ℂ (W.grading N) : ℂ)) :=
  DeligneMLDE.isAKSolution_of_vacuumQuarticRelation W 3 W_centralCharge
    (simple_vacuum_ne_zero _ _) hrel

/-- **`dim L_{-3/2}(sl₃)_N = mldeCoeff 3 N`**, from the trace identity. -/
theorem finrank_eq_mldeCoeff (hrel : VacuumQuarticRelation W 36) (N : ℕ) :
    (Module.finrank ℂ (W.grading N) : ℚ) = DeligneCharacter.mldeCoeff 3 N :=
  finrank_eq_mldeCoeff_of_isAKSolution W (isAKSolution_of_vacuumQuarticRelation hrel) N

/-- **Kac–Wakimoto from the AK MLDE.** -/
theorem kacWakimotoLowerBound_of_vacuumQuarticRelation (hrel : VacuumQuarticRelation W 36)
    (hprod : A2ProductMLDE) : KacWakimotoLowerBound :=
  kacWakimotoLowerBound_of_isAKSolution (isAKSolution_of_vacuumQuarticRelation hrel) hprod

/-- **The A₂ headline with the MLDE in place of Kac–Wakimoto.**  Inputs: U5 (`hU5`), U6 (`hU6`),
the weight-four trace identity (`hrel`, AK §7) and the q-series identity (`hprod`). -/
theorem classicallyFree_of_literatureMLDE (F : ℕ → PowerSeries ℚ)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hrel : VacuumQuarticRelation W 36) (hprod : A2ProductMLDE) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_literature F hU5 hU6
    (kacWakimotoLowerBound_of_vacuumQuarticRelation hrel hprod)

/-- The same from the algebraic square-bracket `C₂` relation. -/
theorem classicallyFree_of_sqC2Relation (F : ℕ → PowerSeries ℚ)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hrel : SqC2QuarticRelation W 36) (hprod : A2ProductMLDE) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_literatureMLDE F hU5 hU6 (vacuumQuarticRelation_of_sqC2 W hrel) hprod

/-! ## With the product identity proved (`a2ProductMLDE`) -/

/-- **Kac–Wakimoto from the weight-four trace identity alone** (any `κ`; it is forced). -/
theorem kacWakimotoLowerBound_of_quartic {κ : ℂ} (hrel : VacuumQuarticRelation W κ) :
    KacWakimotoLowerBound :=
  kacWakimotoLowerBound_of_isAKSolution
    (DeligneMLDE.isAKSolution_of_vacuumQuarticRelation W 3 W_centralCharge
      (simple_vacuum_ne_zero _ _) hrel) a2ProductMLDE

/-- **The A₂ headline: U5, U6 and the weight-four trace identity.** -/
theorem classicallyFree_of_fusionAndQuartic (F : ℕ → PowerSeries ℚ)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    {κ : ℂ} (hrel : VacuumQuarticRelation W κ) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_literature F hU5 hU6 (kacWakimotoLowerBound_of_quartic hrel)

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.isAKSolution_of_vacuumQuarticRelation
#print axioms VOA.DeligneAudit.A2.kacWakimotoLowerBound_of_vacuumQuarticRelation
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_literatureMLDE
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_sqC2Relation
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_fusionAndQuartic
end AxiomAudit
