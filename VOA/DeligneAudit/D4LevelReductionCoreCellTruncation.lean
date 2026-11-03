import VOA.DeligneAudit.D4LevelReductionCoreCellRootTruncation

/-! Every honest-pair cell of a finite truncated core truncates at its union size. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
variable (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreRelations Q a b c π)
variable (hhigh : ∀ e r, a + b + c ≤ r → Q.op e r = 0)
variable (F : CoreCellFlag a b c)

include h hhigh

/-- All fifteen currents satisfy the exact union cutoff on every honest-pair cell generator. -/
theorem coreCellTruncation : CoreCellTruncation a b c Q π F := by
  intro i hi e s hs
  have hb := coreCellCutoff_bounds a b c i hi
  by_cases he : e.val < 6
  · by_cases heq : e = 3
    · subst e
      exact coreCellGenerator_middle_raising_truncation a b c Q π h F i hi s
        (hb.2.1.trans hs)
    · rw [h.parabolic e he heq]
      exact Submodule.zero_mem _
  · by_cases hlt : e.val < 12
    · exact coreCellGenerator_negative_truncation a b c Q π h F hhigh i hi e
        (by omega) hlt s hs
    · have hc (j : Fin 3) : Q.op (A3Sector.simpleH j) s (π (F.generator i)) ∈
          coreCellFiltration a b c Q π F i := by
        by_cases hz : s = 0
        · subst s
          have ha : a = 0 := by omega
          have hbb : b = 0 := by omega
          rw [h.weight]
          have hw : A3Sector.weightABC a b a j = 0 := by
            subst a
            subst b
            fin_cases j <;> rfl
          rw [hw, Nat.cast_zero, zero_smul]
          exact Submodule.zero_mem _
        · exact coreCellGenerator_cartan a b c Q π h F i hi j s (by omega)
      have heq : e = 12 ∨ e = 13 ∨ e = 14 := by omega
      rcases heq with rfl | rfl | rfl
      · exact hc 0
      · exact hc 1
      · exact hc 2

/-- The full current tail at the union size annihilates the entire cyclic cell piece. -/
theorem coreCellPiece_current_tail (i : ℕ) (hi : i < (coreCellCatalog a b c).length)
    (e : Fin 15) (r : ℕ) (hr : coreCellCutoff a b c i ≤ r)
    (v : V ⧸ coreCellFiltration a b c Q π F i)
    (hv : v ∈ coreCellPiece a b c Q π F i) :
    (coreIdealQuotientCurrent a b c Q π (F.ideal i)).op e r v = 0 :=
  coreCellTruncation_piece a b c Q π F (coreCellTruncation a b c Q π h hhigh F)
    i hi e r hr v hv

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellTruncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellPiece_current_tail
