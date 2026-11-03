import VOA.DeligneAudit.D4LevelReductionWeylKernelVector

/-! The dimension recurrence for consecutive symmetric-label Weyl truncations. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.A3Sector VOA.DeligneAudit.SL4T

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Cyclic current spans map onto cyclic current spans in every invariant quotient. -/
theorem currentCyclicSpan_map_quotient (Q : CurrentModule bracketTable V)
    (N : Submodule ℂ V) (hN : ∀ e r, N ≤ N.comap (Q.op e r)) (v : V) :
    (cycSubG Q v).map N.mkQ = cycSubG (quotRepG Q N hN) (N.mkQ v) := by
  rw [cycSubG, Submodule.map_span, cycSubG]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, quot_wordOpG Q N hN v l⟩
  · rintro ⟨l, rfl⟩
    exact ⟨wordOp Q l v, ⟨l, rfl⟩, (quot_wordOpG Q N hN v l).symm⟩

variable [FiniteDimensional ℂ V]
variable (Q : CurrentModule bracketTable V) (v : V) (a b n : ℕ)
variable (hw : LocalWeylRel Q v (weightABC a b a))

include hw

/-- The local Weyl relations pass to every invariant quotient. -/
theorem sl4LocalWeyl_quotient (N : Submodule ℂ V)
    (hN : ∀ e r, N ≤ N.comap (Q.op e r)) :
    LocalWeylRel (quotRepG Q N hN) (N.mkQ v) (weightABC a b a) := by
  have he : ∀ e : Fin 15, e.val < 6 → ∀ r,
      (quotRepG Q N hN).op e r (N.mkQ v) = 0 := by
    intro e he r
    rw [quotRepG_op, hw.raising e he r, map_zero]
  have hh : ∀ i, (quotRepG Q N hN).op (simpleH i) 0 (N.mkQ v) =
      (weightABC a b a i : ℂ) • N.mkQ v := by
    intro i
    rw [quotRepG_op, hw.cartan_zero, map_smul]
  refine ⟨he, ?_, hh, ?_⟩
  · intro i r hr
    rw [quotRepG_op, hw.cartan_pos i r hr, map_zero]
  · intro i
    exact coreFinite_simple_lowering _ _ i _ (he _ (simpleE_raising i) 0) (hh i)

/-- Killing the last highest-root descendant imposes the next smaller current cutoff. -/
theorem sl4Highest_quotient_cutoff (hn : a + b ≤ n + 1) (e : Fin 15) :
    (quotRepG Q (cycSubG Q (Q.op 8 (n + 1) v))
      (cycSubG_inv Q (Q.op 8 (n + 1) v))).op e (n + 1)
        ((cycSubG Q (Q.op 8 (n + 1) v)).mkQ v) = 0 := by
  rw [quotRepG_op]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  by_cases he : e = 8
  · subst e
    exact wordOp_mem_cycSubG Q (Q.op 8 (n + 1) v) []
  · rw [sl4_nonHighest_mode_zero Q v a b hw e he (n + 1) hn]
    exact Submodule.zero_mem _

/-- The highest-root cyclic submodule and its quotient bound a consecutive truncation step. -/
theorem sl4Truncated_cyclic_rank_step (ha : 1 ≤ a) (hn : a + b ≤ n + 1)
    (ht : ∀ e s, n + 2 ≤ s → Q.op e s v = 0)
    (hquad : 2 * a + b + 1 ≤ 2 * n + 3) :
    Module.finrank ℂ (cycSubG Q v) ≤
      Module.finrank ℂ (TruncatedLabelModule a b a (n + 1)) +
        Module.finrank ℂ (TruncatedLabelModule (a - 1) b (a - 1) n) := by
  let N := cycSubG Q (Q.op 8 (n + 1) v)
  let R := quotRepG Q N (cycSubG_inv Q (Q.op 8 (n + 1) v))
  have hquot := (truncatedLabelModule_rank_iff_cyclic a b a (n + 1)
    (Module.finrank ℂ (TruncatedLabelModule a b a (n + 1)))).mp le_rfl
    _ R (N.mkQ v) (sl4LocalWeyl_quotient Q v a b hw N (cycSubG_inv Q _))
    (sl4Highest_quotient_cutoff Q v a b n hw hn)
  have hkernel := (truncatedLabelModule_rank_iff_cyclic (a - 1) b (a - 1) n
    (Module.finrank ℂ (TruncatedLabelModule (a - 1) b (a - 1) n))).mp le_rfl
    _ Q (Q.op 8 (n + 1) v) (sl4Highest_descendant_localWeyl Q v a b n hw ha hn ht)
    (sl4Highest_descendant_cutoff Q v a b n hw ha hn ht hquad)
  have hdim := finrank_le_map_add_infG N.mkQ (cycSubG Q v)
  rw [currentCyclicSpan_map_quotient Q N (cycSubG_inv Q _)] at hdim
  have hker : Module.finrank ℂ
      (cycSubG Q v ⊓ LinearMap.ker N.mkQ : Submodule ℂ V) ≤ Module.finrank ℂ N := by
    apply Submodule.finrank_mono
    rw [Submodule.ker_mkQ]
    exact inf_le_right
  exact hdim.trans (Nat.add_le_add hquot.2 (hker.trans hkernel.2))

omit hw

/-- Increasing the cutoff by one costs at most one smaller highest-root Weyl module. -/
theorem sl4TruncatedLabel_rank_step (a b j : ℕ) (ha : 1 ≤ a) :
    Module.finrank ℂ (TruncatedLabelModule a b a (a + b + (j + 1))) ≤
      Module.finrank ℂ (TruncatedLabelModule a b a (a + b + j)) +
        Module.finrank ℂ (TruncatedLabelModule (a - 1) b (a - 1) ((a - 1) + b + j)) := by
  let P := truncatedWeylSpec (weightABC a b a) (a + b + (j + 1))
  let Q := univRepG bracketTable P
  let v := wUG bracketTable P
  haveI : FiniteDimensional ℂ (TruncatedLabelModule a b a (a + b + (j + 1))) :=
    (truncatedLabelModule_finite_and_local_bound a b a (a + b + (j + 1))).1
  have hs := (truncatedWeylSpec_sat_iff Q v _ _).mp (univG_sat bracketTable P)
  have hn : a - 1 + b + j + 1 = a + b + j := by omega
  have ht : ∀ e s, (a - 1 + b + j) + 2 ≤ s → Q.op e s v = 0 := by
    intro e s hhigh
    exact hs.2 e s (by omega)
  have hb := sl4Truncated_cyclic_rank_step Q v a b (a - 1 + b + j)
    hs.1 ha (by omega) ht (by omega)
  rw [hn] at hb
  rw [presentedCurrent_cyclic, finrank_top] at hb
  exact hb

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.currentCyclicSpan_map_quotient
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4LocalWeyl_quotient
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Highest_quotient_cutoff
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Truncated_cyclic_rank_step
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4TruncatedLabel_rank_step
