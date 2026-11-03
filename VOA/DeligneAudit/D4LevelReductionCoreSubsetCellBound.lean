import VOA.DeligneAudit.D4LevelReductionCoreCellTruncation

/-!
The mixed-label bound on single-adjoint cells, conditional on middle zero-mode vanishing.
-/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Finite-dimensional simple highest vectors satisfy their dominant lowering powers. -/
theorem coreFinite_simple_lowering (Q : CurrentModule A3Sector.bracketTable V)
    (v : V) (j : Fin 3) (d : ℕ) (he : Q.op (A3Sector.simpleE j) 0 v = 0)
    (hh : Q.op (A3Sector.simpleH j) 0 v = (d : ℂ) • v) :
    (Q.op (A3Sector.simpleF j) 0)^[d + 1] v = 0 := by
  have hEF : ∀ x, Q.op (A3Sector.simpleE j) 0 (Q.op (A3Sector.simpleF j) 0 x) -
      Q.op (A3Sector.simpleF j) 0 (Q.op (A3Sector.simpleE j) 0 x) =
        Q.op (A3Sector.simpleH j) 0 x := by
    intro x
    rw [Q.comm]
    simp [A3Sector.simple_ef_table]
  have hHF : ∀ x, Q.op (A3Sector.simpleH j) 0 (Q.op (A3Sector.simpleF j) 0 x) -
      Q.op (A3Sector.simpleF j) 0 (Q.op (A3Sector.simpleH j) 0 x) =
        (-2 : ℂ) • Q.op (A3Sector.simpleF j) 0 x := by
    intro x
    rw [Q.comm]
    simp [A3Sector.simple_hf_table]
  obtain ⟨N, hN⟩ := coreLowering_locally_nilpotent
    (Q.op (A3Sector.simpleF j) 0) (Q.op (A3Sector.simpleH j) 0) hHF v d hh
  exact sl2_sharpen (Q.op (A3Sector.simpleE j) 0) (Q.op (A3Sector.simpleF j) 0)
    (Q.op (A3Sector.simpleH j) 0) hEF hHF v d he hh hN

/-- When the adjoint sites lie in the complement sites, the union cutoff is their larger size. -/
theorem coreCellCutoff_of_subset (a b c i : ℕ)
    (hi : i < (coreCellCatalog a b c).length)
    (hsubset : (coreCellCatalog a b c)[i].2 ⊆ (coreCellCatalog a b c)[i].1) :
    coreCellCutoff a b c i = a + b := by
  have hv := SL4T.cellCatalog_valid (a + b + c) (a + b) a
    ((coreCellCatalog a b c)[i]) (List.getElem_mem hi)
  rw [coreCellCutoff, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  change ((coreCellCatalog a b c)[i].1 ∪ (coreCellCatalog a b c)[i].2).card = _
  rw [Finset.union_eq_left.mpr hsubset]
  exact hv.2.1

variable (b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
variable (π : CoreBaseRing 1 b c →ₗ[ℂ] V) (h : CoreRelations Q 1 b c π)
variable (F : CoreCellFlag 1 b c)

include h

/-- For a single adjoint site, middle zero-mode vanishing gives all local Weyl relations. -/
theorem coreCell_singleAdjoint_localWeyl (i : ℕ)
    (hi : i < (coreCellCatalog 1 b c).length)
    (hzero : Q.op 3 0 (π (F.generator i)) ∈ coreCellFiltration 1 b c Q π F i) :
    A3Sector.LocalWeylRel (coreIdealQuotientCurrent 1 b c Q π (F.ideal i))
      ((coreCellFiltration 1 b c Q π F i).mkQ (π (F.generator i)))
      (A3Sector.weightABC 1 b 1) := by
  let R := coreIdealQuotientCurrent 1 b c Q π (F.ideal i)
  let v := (coreCellFiltration 1 b c Q π F i).mkQ (π (F.generator i))
  have he : ∀ e : Fin 15, e.val < 6 → ∀ s, R.op e s v = 0 := by
    intro e he s
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    by_cases heq : e = 3
    · subst e
      by_cases hs : s = 0
      · simpa only [hs] using hzero
      · exact coreCellGenerator_middle_raising_truncation 1 b c Q π h F i hi s (by omega)
    · rw [h.parabolic e he heq]
      exact Submodule.zero_mem _
  refine ⟨he, ?_, ?_, ?_⟩
  · exact coreCellGenerator_cartan_zero 1 b c Q π h F i hi
  · exact coreCellGenerator_weight 1 b c Q π h F i
  · intro j
    exact coreFinite_simple_lowering R v j (A3Sector.weightABC 1 b 1 j)
      (he _ (A3Sector.simpleE_raising j) 0)
      (coreCellGenerator_weight 1 b c Q π h F i j)

/-- A subset cell has the mixed-label rank bound once its middle zero mode vanishes. -/
theorem coreCell_subset_rank_of_middle_zero
    (hhigh : ∀ e r, 1 + b + c ≤ r → Q.op e r = 0)
    (i : ℕ) (hi : i < (coreCellCatalog 1 b c).length)
    (hsubset : (coreCellCatalog 1 b c)[i].2 ⊆ (coreCellCatalog 1 b c)[i].1)
    (hzero : Q.op 3 0 (π (F.generator i)) ∈ coreCellFiltration 1 b c Q π F i) :
    Module.finrank ℂ (coreCellPiece 1 b c Q π F i) ≤ 15 * 6 ^ b := by
  rw [coreCellPiece_cyclic 1 b c Q π F i hi]
  have hrel := coreCell_singleAdjoint_localWeyl b c Q π h F i hi hzero
  have ht : ∀ e s, 1 + b ≤ s →
      (coreIdealQuotientCurrent 1 b c Q π (F.ideal i)).op e s
        ((coreCellFiltration 1 b c Q π F i).mkQ (π (F.generator i))) = 0 := by
    intro e s hs
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply coreCellTruncation 1 b c Q π h hhigh F i hi e s
    rwa [coreCellCutoff_of_subset 1 b c i hi hsubset]
  have hb := (SL4T.mixedLabelTruncatedRank_iff_cyclic.mp SL4T.mixedLabelTruncatedRank)
    1 b _ _ _ hrel ht
  simpa only [pow_one] using hb.2

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreFinite_simple_lowering
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellCutoff_of_subset
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCell_singleAdjoint_localWeyl
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCell_subset_rank_of_middle_zero
