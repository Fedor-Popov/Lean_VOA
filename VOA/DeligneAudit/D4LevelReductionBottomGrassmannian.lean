import VOA.DeligneAudit.D4LevelReductionBottomEvaluation

/-! Descent of the bottom Cartan evaluation through both Grassmannian relation families. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SL4T

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)
variable (a b c : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))

/-- Exact symmetric bottom relations modulo the next Levi level. -/
abbrev bottomSymmetricRelationIdeal :=
  levelModeRelationIdeal ρ w (a + b + c) h b (2 * a + b + 1)
    (bottomModeShape a c) (bottomModeShape_colours a c)

/-- Symmetric bottom evaluation takes values in the full Cartan orbit. -/
def bottomSymmetricToCartan :
    xyzPowerSumAlgebra (bottomModeShape a c) →ₗ[ℂ] bottomCartanSpan ρ w a c :=
  (((xyzEvaluation ρ w (bottomModeShape a c)).comp
    (xyzPowerSumAlgebra (bottomModeShape a c)).val.toLinearMap)).codRestrict _
      (bottomSymmetric_evaluation_mem_cartan ρ w (a + b + c) a c h)

/-- Symmetric bottom evaluation in the actual truncated level piece. -/
def bottomSymmetricToLevel : xyzPowerSumAlgebra (bottomModeShape a c) →ₗ[ℂ]
    TruncatedLevelPiece ρ w (a + b + c) b (2 * a + b) :=
  (bottomCartanToLevel ρ w a b c h).comp (bottomSymmetricToCartan ρ w a b c h)

/-- The central rectangle relations vanish under bottom evaluation modulo higher levels. -/
theorem bottomCentral_grassIdeal :
    grassIdeal c (a + b) ≤ (bottomSymmetricRelationIdeal ρ w a b c h).comap
      ((bottomElementaryModes a c).comp (alphabetIn false)) := by
  apply sup_le
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro n hn
    change xyzEvaluation ρ w (bottomModeShape a c)
      (bottomElementaryModes a c (alphabetIn false (elementary n))) ∈
        levelFiltration ρ w (a + b + c) b (2 * a + b + 1)
    rw [bottomElementaryModes_central, elementarySpecialization_elementary]
    have he : esymm (Fin c) ℂ n = 0 := by
      have hc : (Finset.univ : Finset (Fin c)).card < n := by simpa using hn
      simp only [esymm, Finset.powersetCard_eq_empty.mpr hc, Finset.sum_empty]
    rw [he, map_zero, map_zero]
    exact Submodule.zero_mem _
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro n hn
    change xyzEvaluation ρ w (bottomModeShape a c)
      (bottomElementaryModes a c (alphabetIn false (complete n))) ∈
        levelFiltration ρ w (a + b + c) b (2 * a + b + 1)
    rw [bottomElementaryModes_central, elementarySpecialization_complete]
    by_cases hc : 1 ≤ c
    · rw [bottomCentral_complete_evaluation]
      convert bottomCentral_completeRelation ρ w (a + b + c) h a c n hc (by omega) using 1 <;>
        push_cast <;> congr 1 <;> omega
    · have hz : c = 0 := by omega
      have he : hsymm (Fin c) ℂ n = 0 := by
        rw [hz, rz_hsymm_eq_sum_vectors]
        apply Finset.sum_eq_zero
        intro e he
        have hn' := e.property
        simp only [Fin.sum_univ_zero] at hn'
        omega
      rw [he, map_zero, map_zero]
      exact Submodule.zero_mem _

/-- The adjoint rectangle relations vanish under bottom evaluation modulo higher levels. -/
theorem bottomAdjoint_grassIdeal :
    grassIdeal a (b + c) ≤ (bottomSymmetricRelationIdeal ρ w a b c h).comap
      ((bottomElementaryModes a c).comp (alphabetIn true)) := by
  apply sup_le
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro n hn
    change xyzEvaluation ρ w (bottomModeShape a c)
      (bottomElementaryModes a c (alphabetIn true (elementary n))) ∈
        levelFiltration ρ w (a + b + c) b (2 * a + b + 1)
    rw [bottomElementaryModes_adjoint, elementarySpecialization_elementary]
    have he : esymm (Fin a) ℂ n = 0 := by
      have hc : (Finset.univ : Finset (Fin a)).card < n := by simpa using hn
      simp only [esymm, Finset.powersetCard_eq_empty.mpr hc, Finset.sum_empty]
    rw [he, map_zero, map_zero]
    exact Submodule.zero_mem _
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro n hn
    change xyzEvaluation ρ w (bottomModeShape a c)
      (bottomElementaryModes a c (alphabetIn true (complete n))) ∈
        levelFiltration ρ w (a + b + c) b (2 * a + b + 1)
    rw [bottomElementaryModes_adjoint, elementarySpecialization_complete]
    by_cases ha : 1 ≤ a
    · rw [bottomAdjoint_complete_evaluation,
        bottomAdjoint_completeRelation ρ w (a + b + c) h a c n ha (by omega)]
      exact Submodule.zero_mem _
    · have hz : a = 0 := by omega
      have he : hsymm (Fin a) ℂ n = 0 := by
        rw [hz, rz_hsymm_eq_sum_vectors]
        apply Finset.sum_eq_zero
        intro e he
        have hn' := e.property
        simp only [Fin.sum_univ_zero] at hn'
        omega
      rw [he, map_zero, map_zero]
      exact Submodule.zero_mem _

/-- Both independent Grassmannian ideals lie in the actual bottom evaluation relations. -/
theorem bottomElementaryModes_biGrassIdeal :
    biGrassIdeal c (a + b) a (b + c) ≤
      (bottomSymmetricRelationIdeal ρ w a b c h).comap (bottomElementaryModes a c) := by
  apply sup_le
  · apply Ideal.map_le_iff_le_comap.mpr
    exact bottomCentral_grassIdeal ρ w a b c h
  · apply Ideal.map_le_iff_le_comap.mpr
    exact bottomAdjoint_grassIdeal ρ w a b c h

/-- The exact bottom relation ring retains all symmetric relations at once. -/
abbrev BottomRelationRing :=
  xyzPowerSumAlgebra (bottomModeShape a c) ⧸ bottomSymmetricRelationIdeal ρ w a b c h

/-- The two Grassmannian factors map into the exact bottom relation ring. -/
def bottomGrassmannianToRelations :
    BiGrass c (a + b) a (b + c) →ₐ[ℂ] BottomRelationRing ρ w a b c h :=
  Ideal.quotientMapₐ _ (bottomElementaryModes a c)
    (bottomElementaryModes_biGrassIdeal ρ w a b c h)

/-- Relations already in the next level vanish in the truncated level piece. -/
theorem bottomSymmetricRelationIdeal_le_kernel :
    (bottomSymmetricRelationIdeal ρ w a b c h).restrictScalars ℂ ≤
      LinearMap.ker (bottomSymmetricToLevel ρ w a b c h) := by
  intro P hP
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.mem_sup_left hP

/-- The exact bottom relation quotient evaluates linearly into the actual level coinvariant. -/
def bottomRelationEvaluation : BottomRelationRing ρ w a b c h →ₗ[ℂ]
    TruncatedLevelPiece ρ w (a + b + c) b (2 * a + b) :=
  (bottomSymmetricRelationIdeal ρ w a b c h).restrictScalars ℂ |>.liftQ
    (bottomSymmetricToLevel ρ w a b c h)
    (bottomSymmetricRelationIdeal_le_kernel ρ w a b c h)

/-- The two actual mode alphabets give a Grassmannian evaluation in the universal level. -/
def bottomGrassmannianEvaluation : BiGrass c (a + b) a (b + c) →ₗ[ℂ]
    TruncatedLevelPiece ρ w (a + b + c) b (2 * a + b) :=
  (bottomRelationEvaluation ρ w a b c h).comp
    (bottomGrassmannianToRelations ρ w a b c h).toLinearMap

theorem bottomGrassmannianEvaluation_mk (P : BiSymPoly) :
    bottomGrassmannianEvaluation ρ w a b c h (Ideal.Quotient.mk _ P) =
      bottomSymmetricToLevel ρ w a b c h (bottomElementaryModes a c P) := rfl

/-- The Grassmannian evaluation lands in the bottom Cartan orbit of the level piece. -/
theorem bottomGrassmannianEvaluation_range :
    LinearMap.range (bottomGrassmannianEvaluation ρ w a b c h) ≤
      LinearMap.range (bottomCartanToLevel ρ w a b c h) := by
  rintro v ⟨P, rfl⟩
  induction P using Quotient.inductionOn' with
  | h P =>
      exact ⟨bottomSymmetricToCartan ρ w a b c h (bottomElementaryModes a c P), rfl⟩

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_grassIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomAdjoint_grassIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomElementaryModes_biGrassIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomSymmetricRelationIdeal_le_kernel
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomGrassmannianEvaluation_mk
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomGrassmannianEvaluation_range
