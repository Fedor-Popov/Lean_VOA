import VOA.DeligneAudit.D4LevelReductionWeylTruncationStep

/-!
The truncated sl4 Weyl bound obtained by splitting any number of adjoint sites.
The argument is a consecutive-truncation induction.
-/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.A3Sector VOA.DeligneAudit.SL4T

/-- Splitting any number of adjoint sites replaces the corresponding factors fifteen by sixteen. -/
theorem truncatedWeyl_sl4_splitAdjoint_rank_le (a b j : ℕ) (hj : j ≤ a) :
    FiniteDimensional ℂ (TruncatedLabelModule a b a (a + b + j)) ∧
      Module.finrank ℂ (TruncatedLabelModule a b a (a + b + j)) ≤
        16 ^ j * 15 ^ (a - j) * 6 ^ b := by
  refine ⟨(truncatedLabelModule_finite_and_local_bound a b a (a + b + j)).1, ?_⟩
  induction j generalizing a with
  | zero =>
    simpa only [Nat.add_zero, Nat.sub_zero, pow_zero, one_mul] using
      (truncatedWeyl_sl4_mixed_rank_le a b).2
  | succ j ih =>
    have ha : 1 ≤ a := by omega
    have hleft := ih a (by omega)
    have hright := ih (a - 1) (by omega)
    have hstep := sl4TruncatedLabel_rank_step a b j ha
    have hexp : a - j = (a - (j + 1)) + 1 := by omega
    have hexp' : a - 1 - j = a - (j + 1) := by omega
    calc
      _ ≤ 16 ^ j * 15 ^ (a - j) * 6 ^ b +
          16 ^ j * 15 ^ (a - 1 - j) * 6 ^ b :=
        hstep.trans (Nat.add_le_add hleft hright)
      _ = 16 ^ (j + 1) * 15 ^ (a - (j + 1)) * 6 ^ b := by
        rw [hexp, hexp', pow_succ, pow_succ]
        ring

/-- The split-adjoint bound applies to every cyclic realization of the truncated presentation. -/
theorem truncatedWeyl_sl4_splitAdjoint_cyclic_bound (a b j : ℕ) (hj : j ≤ a)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (Q : CurrentModule bracketTable V) (v : V)
    (hw : LocalWeylRel Q v (weightABC a b a))
    (ht : ∀ e, Q.op e (a + b + j) v = 0) :
    FiniteDimensional ℂ (cycSubG Q v) ∧
      Module.finrank ℂ (cycSubG Q v) ≤ 16 ^ j * 15 ^ (a - j) * 6 ^ b :=
  (truncatedLabelModule_rank_iff_cyclic a b a (a + b + j)
    (16 ^ j * 15 ^ (a - j) * 6 ^ b)).mp
    (truncatedWeyl_sl4_splitAdjoint_rank_le a b j hj).2 _ Q v hw ht

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedWeyl_sl4_splitAdjoint_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedWeyl_sl4_splitAdjoint_cyclic_bound
