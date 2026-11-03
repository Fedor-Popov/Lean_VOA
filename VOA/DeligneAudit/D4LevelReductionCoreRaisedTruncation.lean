import VOA.DeligneAudit.D4LevelReductionCoreRaisedRelations

/-! The raised single-adjoint vector truncates one mode before its middle weight. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The first composite-root Cartan current is the sum of the three simple Cartan currents. -/
def coreFirstCompositeCartan (Q : CurrentModule A3Sector.bracketTable V) (s : ℕ) :
    Module.End ℂ V := Q.op 12 s + Q.op 13 s

private theorem coreFirstComposite_rootTable :
    (∀ k : Fin 15, A3Sector.bracketTable 1 7 k =
      (if k = 12 then 1 else 0) + (if k = 13 then 1 else 0)) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 12 7 k + A3Sector.bracketTable 13 7 k =
      if k = 7 then -2 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 12 1 k + A3Sector.bracketTable 13 1 k =
      if k = 1 then 2 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 7 7 k = 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 1 1 k = 0) := by
  have ht :
      (∀ k : Fin 15, A3Sector.bracketInt 1 7 k =
        (if k = 12 then 1 else 0) + (if k = 13 then 1 else 0)) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 12 7 k + A3Sector.bracketInt 13 7 k =
        if k = 7 then -2 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 12 1 k + A3Sector.bracketInt 13 1 k =
        if k = 1 then 2 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 7 7 k = 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 1 1 k = 0) := by decide +kernel
  unfold A3Sector.bracketTable
  exact_mod_cast ht

/-- The first composite-root currents satisfy the rank-one current relations. -/
theorem coreFirstComposite_currentRelations (Q : CurrentModule A3Sector.bracketTable V) :
    CVsl2.SL2 (Q.op 1) (coreFirstCompositeCartan Q) (Q.op 7) := by
  obtain ⟨hEF, hHF, hHE, hFF, hEE⟩ := coreFirstComposite_rootTable
  refine ⟨fun r s => ?_, fun r s => ?_, fun r s => ?_,
    fun r s => ?_, fun r s => ?_⟩
  · rw [coreCurrent_commutator]
    simp [hEF, add_smul, Finset.sum_add_distrib, coreFirstCompositeCartan]
  · simp only [coreFirstCompositeCartan, add_mul, mul_add, add_sub_add_comm]
    rw [coreCurrent_commutator, coreCurrent_commutator,
      ← Finset.sum_add_distrib]
    simp_rw [← add_smul, hHF]
    simp [ite_smul]
  · simp only [coreFirstCompositeCartan, add_mul, mul_add, add_sub_add_comm]
    rw [coreCurrent_commutator, coreCurrent_commutator,
      ← Finset.sum_add_distrib]
    simp_rw [← add_smul, hHE]
    simp [ite_smul]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hFF]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hEE]


/-- Vanishing of two root currents implies vanishing of their nonzero bracket. -/
theorem coreCurrent_zero_of_bracket (Q : CurrentModule A3Sector.bracketTable V)
    (e f g : Fin 15) (z : ℂ) (hz : z ≠ 0)
    (ht : ∀ k, A3Sector.bracketTable e f k = if k = g then z else 0)
    (v : V) (s : ℕ) (he : Q.op e 0 v = 0) (hf : Q.op f s v = 0) :
    Q.op g s v = 0 := by
  have hc := Q.comm e f 0 s v
  simp only [ht, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Nat.zero_add, he, hf, map_zero, sub_self] at hc
  exact (smul_eq_zero.mp hc.symm).resolve_left hz

private theorem coreRaised_transferTable :
    (∀ k : Fin 15, A3Sector.bracketTable 0 7 k = if k = 9 then -1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 6 9 k = if k = 7 then -1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 11 9 k = if k = 10 then 1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 11 7 k = if k = 8 then 1 else 0) := by
  have ht :
      (∀ k : Fin 15, A3Sector.bracketInt 0 7 k = if k = 9 then -1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 6 9 k = if k = 7 then -1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 11 9 k = if k = 10 then 1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 11 7 k = if k = 8 then 1 else 0) := by
    decide +kernel
  unfold A3Sector.bracketTable
  exact_mod_cast ht

variable [FiniteDimensional ℂ V]
variable (Q : CurrentModule A3Sector.bracketTable V) (v : V) (b : ℕ)
variable (h : SingleAdjointCellRelations Q v b)

include h

/-- Garland gives the composite lowering cutoff at the sum of its two simple weights. -/
theorem singleAdjoint_composite_lowering (s : ℕ) (hs : b + 1 ≤ s) : Q.op 7 s v = 0 := by
  apply coreHighest_lowering_modes (coreFirstComposite_currentRelations Q) v (b + 1)
    (fun r => h.parabolic 1 (by decide) (by decide) r)
  · have hzero := h.weight 0
    have hone := h.weight 1
    simp only [A3Sector.simpleH, A3Sector.weightABC] at hzero hone
    simp only [coreFirstCompositeCartan, LinearMap.add_apply, hzero, hone, Nat.cast_add,
      Nat.cast_one]
    module
  · intro r hr
    have hzero := h.cartan 0 r hr
    have hone := h.cartan 1 r hr
    change Q.op 12 r v = 0 at hzero
    change Q.op 13 r v = 0 at hone
    simp [coreFirstCompositeCartan, hzero, hone]
  · exact hs

/-- A positive-root bracket gives the same cutoff for the middle lowering root. -/
theorem singleAdjoint_middle_lowering (s : ℕ) (hs : b + 1 ≤ s) : Q.op 9 s v = 0 :=
  coreCurrent_zero_of_bracket Q 0 7 9 (-1) (by norm_num) coreRaised_transferTable.1 v s
    (h.parabolic 0 (by decide) (by decide) 0) (singleAdjoint_composite_lowering Q v b h s hs)

/-- The middle lowering cutoff survives applying the middle positive zero mode. -/
theorem singleAdjoint_raised_middle_lowering (s : ℕ) (hs : b + 1 ≤ s) :
    Q.op 9 s (Q.op 3 0 v) = 0 := by
  rw [coreMiddle_commutator, singleAdjoint_middle_lowering Q v b h s hs, map_zero,
    zero_add]
  have hc := h.cartan 1 s (by omega)
  simpa [coreMiddleBracket, A3Sector.simpleH] using congrArg Neg.neg hc

/-- Every current on the raised vector truncates at one less than its middle label. -/
theorem singleAdjoint_raised_truncation (e : Fin 15) (s : ℕ) (hs : b + 1 ≤ s) :
    Q.op e s (Q.op 3 0 v) = 0 := by
  let w := Q.op 3 0 v
  have hw := singleAdjoint_raised_localWeyl Q v b h
  have hfirst (r : ℕ) : Q.op 6 r w = 0 :=
    A3Sector.simple_mode_zero Q w _ hw 0 r (by simp [A3Sector.weightABC])
  have hlast (r : ℕ) : Q.op 11 r w = 0 :=
    A3Sector.simple_mode_zero Q w _ hw 2 r (by simp [A3Sector.weightABC])
  have hmiddle : Q.op 9 s w = 0 := singleAdjoint_raised_middle_lowering Q v b h s hs
  have hseven : Q.op 7 s w = 0 := coreCurrent_zero_of_bracket Q 6 9 7 (-1)
    (by norm_num) coreRaised_transferTable.2.1 w s (hfirst 0) hmiddle
  by_cases he : e.val < 6
  · exact hw.raising e he s
  by_cases hc : 12 ≤ e.val
  · have heq : e = 12 ∨ e = 13 ∨ e = 14 := by omega
    rcases heq with rfl | rfl | rfl
    · exact hw.cartan_pos 0 s (by omega)
    · exact hw.cartan_pos 1 s (by omega)
    · exact hw.cartan_pos 2 s (by omega)
  have heq : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 := by omega
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfirst s
  · exact hseven
  · exact coreCurrent_zero_of_bracket Q 11 7 8 1 one_ne_zero
      coreRaised_transferTable.2.2.2 w s (hlast 0) hseven
  · exact hmiddle
  · exact coreCurrent_zero_of_bracket Q 11 9 10 1 one_ne_zero
      coreRaised_transferTable.2.2.1 w s (hlast 0) hmiddle
  · exact hlast s

/-- The doubled-site theorem bounds the cyclic submodule of the raised vector. -/
theorem singleAdjoint_raised_rank :
    Module.finrank ℂ (UnivG.cycSubG Q (Q.op 3 0 v)) ≤ 20 * 6 ^ b := by
  have hb := (SL4T.truncatedWeyl_sl4_doubledSite_rank_le (b + 2) (by omega)).2
  have he := (SL4T.truncatedLabelModule_rank_iff_cyclic 0 (b + 2) 0
    (b + 2 - 1) (20 * 6 ^ (b + 2 - 2))).mp hb V Q (Q.op 3 0 v)
      (singleAdjoint_raised_localWeyl Q v b h)
      (fun e => singleAdjoint_raised_truncation Q v b h e _ (by omega))
  simpa using he.2

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreFirstComposite_currentRelations
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCurrent_zero_of_bracket
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_composite_lowering
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_middle_lowering
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_raised_middle_lowering
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_raised_truncation
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_raised_rank
