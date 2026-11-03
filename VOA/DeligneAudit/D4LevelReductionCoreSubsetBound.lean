import VOA.DeligneAudit.D4LevelReductionCommonRootEvaluation

/-! The unconditional mixed-label bound on the subset cells of a single-adjoint core. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open Polynomial
open VOA.DeligneAudit.SectorWeyl

/-- A coefficient flag with both characteristic relations, selected for every core triple. -/
def coreCommonRootCellFlag (a b c : ℕ) : CoreCellFlag a b c :=
  (coreCellFlag_commonRoot_exists a b c).choose

/-- The selected flag retains the exact adjoint-site difference exponent. -/
theorem coreCommonRootCellFlag_relation (a b c i : ℕ)
    (hi : i < (coreCellCatalog a b c).length) :
    Polynomial.C ((coreCommonRootCellFlag a b c).generator i) *
        X ^ ((coreCellCatalog a b c)[i].2 \ (coreCellCatalog a b c)[i].1).card ∈
      ((coreCommonRootCellFlag a b c).ideal i).map Polynomial.C ⊔
        grassmannianCommonRootIdeal (a + b + c) (a + b) a :=
  (coreCellFlag_commonRoot_exists a b c).choose_spec i hi

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
variable (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreRelations Q a b c π)

include h

/-- A common-root relation gives the corresponding middle-raising cutoff in an ideal quotient. -/
theorem coreRaising_mem_of_commonRoot (I : Ideal (CoreBaseRing a b c))
    (σ : CoreBaseRing a b c) (n : ℕ)
    (hσ : Polynomial.C σ * X ^ n ∈ I.map Polynomial.C ⊔
      grassmannianCommonRootIdeal (a + b + c) (a + b) a)
    (s : ℕ) (hs : n ≤ s) : Q.op 3 s (π σ) ∈ coreIdealSpan a b c Q π I := by
  have hrel := (I.map Polynomial.C ⊔
    grassmannianCommonRootIdeal (a + b + c) (a + b) a).mul_mem_right (X ^ (s - n)) hσ
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hs] at hrel
  obtain ⟨U, hU, T, hT, heq⟩ := Submodule.mem_sup.mp hrel
  rw [← SL4T.piCurrentMap_C_mul_X_pow, ← heq, map_add,
    coreRaising_commonRootIdeal a b c Q π h T hT, add_zero]
  exact SL4T.piCurrentMap_ideal (Q.op 3) π I (coreIdealSpan a b c Q π I)
    (fun φ hφ => coreIdealSpan_contains a b c Q π I hφ)
    (fun r => coreIdealSpan_stable a b c Q π I 3 r) hU

/-- The middle raising cutoff is the number of adjoint sites outside the complement sites. -/
theorem coreCellGenerator_middle_difference (i : ℕ)
    (hi : i < (coreCellCatalog a b c).length) (s : ℕ)
    (hs : ((coreCellCatalog a b c)[i].2 \ (coreCellCatalog a b c)[i].1).card ≤ s) :
    Q.op 3 s (π ((coreCommonRootCellFlag a b c).generator i)) ∈
      coreCellFiltration a b c Q π (coreCommonRootCellFlag a b c) i :=
  coreRaising_mem_of_commonRoot a b c Q π h _ _ _
    (coreCommonRootCellFlag_relation a b c i hi) s hs

/-- Every middle raising mode vanishes on a subset cell, including mode zero. -/
theorem coreCellGenerator_middle_zero_of_subset (i : ℕ)
    (hi : i < (coreCellCatalog a b c).length)
    (hsubset : (coreCellCatalog a b c)[i].2 ⊆ (coreCellCatalog a b c)[i].1) (s : ℕ) :
    Q.op 3 s (π ((coreCommonRootCellFlag a b c).generator i)) ∈
      coreCellFiltration a b c Q π (coreCommonRootCellFlag a b c) i := by
  apply coreCellGenerator_middle_difference a b c Q π h i hi s
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsubset, Finset.card_empty]
  exact Nat.zero_le s

omit h

/-- Subset cells of every single-adjoint core satisfy the mixed-label rank bound. -/
theorem coreCell_singleAdjoint_subset_rank
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing 1 b c →ₗ[ℂ] V)
    (h : CoreRelations Q 1 b c π) (hhigh : ∀ e r, 1 + b + c ≤ r → Q.op e r = 0)
    (i : ℕ) (hi : i < (coreCellCatalog 1 b c).length)
    (hsubset : (coreCellCatalog 1 b c)[i].2 ⊆ (coreCellCatalog 1 b c)[i].1) :
    Module.finrank ℂ (coreCellPiece 1 b c Q π (coreCommonRootCellFlag 1 b c) i) ≤
      15 * 6 ^ b :=
  coreCell_subset_rank_of_middle_zero b c Q π h (coreCommonRootCellFlag 1 b c) hhigh
    i hi hsubset (coreCellGenerator_middle_zero_of_subset 1 b c Q π h i hi hsubset 0)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreCommonRootCellFlag_relation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_mem_of_commonRoot
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_middle_difference
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_middle_zero_of_subset
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCell_singleAdjoint_subset_rank
