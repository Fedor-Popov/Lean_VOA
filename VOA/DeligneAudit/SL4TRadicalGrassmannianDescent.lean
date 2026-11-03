import VOA.DeligneAudit.SL4TRadicalCompleteEvaluation
import VOA.DeligneAudit.SL4TRadicalGrassmannianPresentation

/-! Descent of the first Levi multiplicity evaluator through the Grassmannian relations. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open scoped TensorProduct

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- Abstract elementary generators act as the symmetric polynomials of one radical alphabet. -/
def radicalElementaryModes (d : Fin 3 → ℕ) (j : Fin 3) :
    SymPoly →ₐ[ℂ] radicalPowerSumAlgebra d :=
  aeval fun i => ⟨rename (radicalSlotEmbedding d j) (esymm (Fin (d j)) ℂ (i + 1)),
    radicalAlphabet_symmetric_mem_powerSumAlgebra d j _ (esymm_isSymmetric _ _ _)⟩

theorem radicalElementaryModes_val (d : Fin 3 → ℕ) (j : Fin 3) (P : SymPoly) :
    (radicalElementaryModes d j P : RadicalModePolynomial d) =
      rename (radicalSlotEmbedding d j) (elementarySpecialization (d j) P) := by
  have he : (radicalPowerSumAlgebra d).val.comp (radicalElementaryModes d j) =
      (rename (radicalSlotEmbedding d j)).comp (elementarySpecialization (d j)) := by
    ext i
    simp [radicalElementaryModes, elementarySpecialization]
  exact AlgHom.congr_fun he P

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

/-- The actual multiplicity relations form an ideal in the power-sum algebra. -/
def radicalMultiplicityRelationIdeal (d : Fin 3 → ℕ) : Ideal (radicalPowerSumAlgebra d) where
  carrier := {P | radicalMultiplicityEvaluation ρ w d P = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro P Q hP hQ
    change radicalMultiplicityEvaluation ρ w d (P.val + Q.val) = 0
    rw [map_add, hP, hQ, add_zero]
  smul_mem' := by
    intro P Q hQ
    exact radicalPowerSumAlgebra_preserves_relations ρ w a b c h d P P.property Q hQ

/-- The quotient ring recording exactly the first Levi multiplicity relations. -/
abbrev RadicalMultiplicityRing (d : Fin 3 → ℕ) :=
  radicalPowerSumAlgebra d ⧸ radicalMultiplicityRelationIdeal ρ w a b c h d

/-- The relation quotient has a canonical linear evaluation into the actual multiplicity. -/
def radicalRelationQuotientEvaluation (d : Fin 3 → ℕ) :
    RadicalMultiplicityRing ρ w a b c h d →ₗ[ℂ] radicalCountMultiplicity ρ w d :=
  (radicalMultiplicityRelationIdeal ρ w a b c h d).restrictScalars ℂ |>.liftQ
    ((radicalMultiplicityEvaluation ρ w d).comp (radicalPowerSumAlgebra d).val.toLinearMap)
    (fun _ hP => hP)

theorem radicalRelationQuotientEvaluation_mk (d : Fin 3 → ℕ)
    (P : radicalPowerSumAlgebra d) :
    radicalRelationQuotientEvaluation ρ w a b c h d (Ideal.Quotient.mk _ P) =
      radicalMultiplicityEvaluation ρ w d P := rfl

/-- Every merged multiplicity vector is represented in the relation quotient. -/
theorem radicalRelationQuotientEvaluation_surjective (d : Fin 3 → ℕ) :
    Function.Surjective (radicalRelationQuotientEvaluation ρ w a b c h d) := by
  intro v
  obtain ⟨P, hP⟩ := radicalSymmetricMultiplicityEvaluation_surjective ρ w d v
  exact ⟨Ideal.Quotient.mk _
    ⟨P.val, radicalSymmetricModes_le_powerSumAlgebra d P.property⟩, hP⟩

/-- Both elementary and complete tails vanish after evaluation in the multiplicity quotient. -/
theorem radicalElementaryModes_grassIdeal (d : Fin 3 → ℕ) (j : Fin 3) :
    grassIdeal (d j) (weightABC a b c j - d j) ≤
      (radicalMultiplicityRelationIdeal ρ w a b c h d).comap
        (radicalElementaryModes d j) := by
  apply sup_le
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro s hs
    change radicalMultiplicityEvaluation ρ w d (radicalElementaryModes d j (elementary s)) = 0
    rw [radicalElementaryModes_val, elementarySpecialization_elementary]
    have he : esymm (Fin (d j)) ℂ s = 0 := by
      have hc : (Finset.univ : Finset (Fin (d j))).card < s := by simpa using hs
      simp only [esymm, Finset.powersetCard_eq_empty.mpr hc, Finset.sum_empty]
    rw [he, map_zero, map_zero]
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro s hs
    change radicalMultiplicityEvaluation ρ w d (radicalElementaryModes d j (complete s)) = 0
    rw [radicalElementaryModes_val, elementarySpecialization_complete]
    exact radicalMultiplicityEvaluation_complete_eq_zero ρ w a b c h d j s hs

/-- Each Grassmannian factor acts through its elementary-generator quotient. -/
def radicalGrassmannianFactor (d : Fin 3 → ℕ) (j : Fin 3) :
    H (d j) (weightABC a b c j) →ₐ[ℂ] RadicalMultiplicityRing ρ w a b c h d :=
  Ideal.quotientMapₐ _ (radicalElementaryModes d j)
    (radicalElementaryModes_grassIdeal ρ w a b c h d j)

theorem radicalGrassmannianFactor_mk (d : Fin 3 → ℕ) (j : Fin 3) (P : SymPoly) :
    radicalGrassmannianFactor ρ w a b c h d j (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (radicalElementaryModes d j P) := rfl

/-- The tensor product of the three Grassmannian factors maps into the relation quotient. -/
def radicalGrassmannianQuotientMap (d : Fin 3 → ℕ) :
    RadicalGrassmannianRing a b c d →ₐ[ℂ] RadicalMultiplicityRing ρ w a b c h d :=
  Algebra.TensorProduct.lift (radicalGrassmannianFactor ρ w a b c h d 0)
    (Algebra.TensorProduct.lift (radicalGrassmannianFactor ρ w a b c h d 1)
      (radicalGrassmannianFactor ρ w a b c h d 2) (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)

/-- Evaluation of the three-Grassmannian source in the actual merged multiplicity. -/
def radicalGrassmannianEvaluation (d : Fin 3 → ℕ) :
    RadicalGrassmannianRing a b c d →ₗ[ℂ] radicalCountMultiplicity ρ w d :=
  (radicalRelationQuotientEvaluation ρ w a b c h d).comp
    (radicalGrassmannianQuotientMap ρ w a b c h d).toLinearMap

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalElementaryModes_val
#print axioms VOA.DeligneAudit.SL4T.radicalRelationQuotientEvaluation_mk
#print axioms VOA.DeligneAudit.SL4T.radicalRelationQuotientEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.radicalElementaryModes_grassIdeal
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianFactor_mk
