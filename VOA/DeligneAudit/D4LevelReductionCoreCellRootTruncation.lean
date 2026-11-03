import VOA.DeligneAudit.D4LevelReductionCoreHighestCharacteristic

/-! Union cutoffs for every negative root and the middle positive root on core cells. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Garland truncates a finite highest vector with zero positive Cartan modes at its weight. -/
theorem coreHighest_lowering_modes [FiniteDimensional ℂ V]
    {E H F : ℕ → Module.End ℂ V} (hS : CVsl2.SL2 E H F)
    (v : V) (d : ℕ) (hE : ∀ s, E s v = 0) (hH : H 0 v = (d : ℂ) • v)
    (hpos : ∀ s, 0 < s → H s v = 0) (s : ℕ) (hs : d ≤ s) : F s v = 0 := by
  have hEF : ∀ k, E 1 * F k - F k * E 1 = H (k + 1) := by
    intro k
    simpa only [Nat.add_comm] using hS.hEF 1 k
  have hn := coreHighest_lowering_nilpotent hS v d (hE 0) hH
  have hg := Garland.garland hEF (fun m k => hS.hHF (m + 1) k) hS.hFF
    (hE 1) (fun m => hpos (m + 1) (by omega)) 1 (by omega) hn s (by omega)
  simpa only [pow_one, Garland.Fs, PowerSeries.coeff_mk] using hg

/-- Each cell union contains both of its alphabets and is contained in the ambient sites. -/
theorem coreCellCutoff_bounds (a b c i : ℕ) (hi : i < (coreCellCatalog a b c).length) :
    a + b ≤ coreCellCutoff a b c i ∧ a ≤ coreCellCutoff a b c i ∧
      coreCellCutoff a b c i ≤ a + b + c := by
  have hv := SL4T.cellCatalog_valid (a + b + c) (a + b) a
    ((coreCellCatalog a b c)[i]) (List.getElem_mem hi)
  rw [coreCellCutoff, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  change a + b ≤ ((coreCellCatalog a b c)[i].1 ∪
    (coreCellCatalog a b c)[i].2).card ∧ _
  refine ⟨?_, ?_, ?_⟩
  · exact hv.2.1.symm.le.trans (Finset.card_le_card Finset.subset_union_left)
  · exact hv.2.2.2.symm.le.trans (Finset.card_le_card Finset.subset_union_right)
  · exact (Finset.card_le_card (Finset.union_subset hv.1 hv.2.2.1)).trans_eq
      (Finset.card_range _)

/-- A root commutator transports a cutoff through a current-stable submodule. -/
theorem coreCurrent_mem_of_bracket (Q : CurrentModule A3Sector.bracketTable V)
    (N : Submodule ℂ V) (hN : ∀ e r, N ≤ N.comap (Q.op e r))
    (e f g : Fin 15) (z : ℂ) (hz : z ≠ 0)
    (ht : ∀ k, A3Sector.bracketTable e f k = if k = g then z else 0)
    (v : V) (s : ℕ) (he : Q.op e 0 v = 0) (hf : Q.op f s v ∈ N) :
    Q.op g s v ∈ N := by
  have hc := Q.comm e f 0 s v
  simp only [ht, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Nat.zero_add, he, map_zero, sub_zero] at hc
  apply (N.smul_mem_iff hz).mp
  rw [← hc]
  exact hN e 0 hf

private theorem coreRoot_transferTable :
    (∀ k : Fin 15, A3Sector.bracketTable 0 8 k = if k = 10 then -1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 5 8 k = if k = 7 then 1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 4 8 k = if k = 6 then 1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 1 8 k = if k = 11 then -1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 0 7 k = if k = 9 then -1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 1 6 k = if k = 3 then -1 else 0) := by
  have ht :
      (∀ k : Fin 15, A3Sector.bracketInt 0 8 k = if k = 10 then -1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 5 8 k = if k = 7 then 1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 4 8 k = if k = 6 then 1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 1 8 k = if k = 11 then -1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 0 7 k = if k = 9 then -1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 1 6 k = if k = 3 then -1 else 0) := by
    decide +kernel
  unfold A3Sector.bracketTable
  exact_mod_cast ht

variable (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
variable (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreRelations Q a b c π)
variable (F : CoreCellFlag a b c)

include h

/-- The first outer lowering current has the sharper alphabet-size cutoff on every cell. -/
theorem coreCellGenerator_outer_truncation [FiniteDimensional ℂ V]
    (i : ℕ) (hi : i < (coreCellCatalog a b c).length) (s : ℕ) (hs : a ≤ s) :
    Q.op 6 s (π (F.generator i)) ∈ coreCellFiltration a b c Q π F i := by
  let R := coreIdealQuotientCurrent a b c Q π (F.ideal i)
  let v := (coreCellFiltration a b c Q π F i).mkQ (π (F.generator i))
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change R.op 6 s v = 0
  apply coreHighest_lowering_modes (coreOuter_currentRelations R) v a
  · intro r
    change (coreCellFiltration a b c Q π F i).mkQ
      (Q.op 0 r (π (F.generator i))) = 0
    rw [h.parabolic 0 (by decide) (by decide), map_zero]
  · exact coreCellGenerator_weight a b c Q π h F i 0
  · intro r hr
    exact coreCellGenerator_cartan_zero a b c Q π h F i hi 0 r hr
  · exact hs

/-- The middle raising current inherits the outer alphabet cutoff by a positive-root bracket. -/
theorem coreCellGenerator_middle_raising_truncation [FiniteDimensional ℂ V]
    (i : ℕ) (hi : i < (coreCellCatalog a b c).length) (s : ℕ) (hs : a ≤ s) :
    Q.op 3 s (π (F.generator i)) ∈ coreCellFiltration a b c Q π F i :=
  coreCurrent_mem_of_bracket Q _ (coreCellFiltration_stable a b c Q π F i)
    1 6 3 (-1) (by norm_num) coreRoot_transferTable.2.2.2.2.2
    (π (F.generator i)) s (h.parabolic 1 (by decide) (by decide) 0 _)
    (coreCellGenerator_outer_truncation a b c Q π h F i hi s hs)

/-- The highest-root cutoff propagates to all six negative roots through positive zero modes. -/
theorem coreCellGenerator_negative_truncation [FiniteDimensional ℂ V]
    (hhigh : ∀ e r, a + b + c ≤ r → Q.op e r = 0)
    (i : ℕ) (hi : i < (coreCellCatalog a b c).length)
    (e : Fin 15) (he : 6 ≤ e.val) (hlt : e.val < 12)
    (s : ℕ) (hs : coreCellCutoff a b c i ≤ s) :
    Q.op e s (π (F.generator i)) ∈ coreCellFiltration a b c Q π F i := by
  obtain ⟨hfirst, hsecond, hthird, hfourth, hfifth, _⟩ := coreRoot_transferTable
  have htop := coreCellGenerator_highest_truncation a b c Q π h hhigh F i hi s hs
  have htransfer := coreCurrent_mem_of_bracket Q _
    (coreCellFiltration_stable a b c Q π F i)
  have hseven : Q.op 7 s (π (F.generator i)) ∈ coreCellFiltration a b c Q π F i :=
    htransfer 5 8 7 1 one_ne_zero hsecond _ s
      (h.parabolic 5 (by decide) (by decide) 0 _) htop
  have heq : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 := by
    omega
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact htransfer 4 8 6 1 one_ne_zero hthird _ s
      (h.parabolic 4 (by decide) (by decide) 0 _) htop
  · exact hseven
  · exact htop
  · exact htransfer 0 7 9 (-1) (by norm_num) hfifth _ s
      (h.parabolic 0 (by decide) (by decide) 0 _) hseven
  · exact htransfer 0 8 10 (-1) (by norm_num) hfirst _ s
      (h.parabolic 0 (by decide) (by decide) 0 _) htop
  · exact htransfer 1 8 11 (-1) (by norm_num) hfourth _ s
      (h.parabolic 1 (by decide) (by decide) 0 _) htop

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_lowering_modes
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellCutoff_bounds
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCurrent_mem_of_bracket
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_outer_truncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_middle_raising_truncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_negative_truncation
