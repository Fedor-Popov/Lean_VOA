import VOA.DeligneAudit.SL4TCellQuotient
import VOA.DeligneAudit.SL4TBalanced

/-! # The abstract cell lemma, in flag form -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.CVsl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- Theorem C/C': an invariant flag with highest-weight cell relations has the sum of
the balanced truncated Weyl bounds. No finite-dimensionality hypothesis is needed. -/
theorem cellFlag_bound (hS : SL2 E H F) (v : ℕ → V) (r : ℕ) (ν : ℕ → ℕ) :
    ∀ n, (∀ i < n, 1 ≤ ν i) →
      (∀ i < n, CellRelations E H F (cellFlag E H F v i) (v i) r (ν i)) →
      FiniteDimensional ℂ (cellFlag E H F v n) ∧
        Module.finrank ℂ (cellFlag E H F v n) ≤
          ∑ i ∈ Finset.range n, ((bal r (ν i)).map (· + 1)).prod := by
  intro n
  induction n with
  | zero =>
      intro _ _
      have hz := cellFlag_zero (E := E) (H := H) (F := F) v
      haveI : FiniteDimensional ℂ (cellFlag E H F v 0) := by
        rw [hz]
        infer_instance
      refine ⟨inferInstance, ?_⟩
      rw [hz]
      simp
  | succ n ih =>
      intro hν hR
      obtain ⟨fd, bd⟩ := ih (fun i hi => hν i (by omega)) (fun i hi => hR i (by omega))
      obtain ⟨fdq, bdq⟩ := cellFlag_step_bound hS v n r (ν n)
        (hν n (by omega)) (hR n (by omega))
      let P := cellFlag E H F v n
      let T := cellFlag E H F v (n + 1)
      haveI : FiniteDimensional ℂ P := fd
      have hinf : T ⊓ LinearMap.ker P.mkQ ≤ P := by
        rw [Submodule.ker_mkQ]
        exact inf_le_right
      haveI : FiniteDimensional ℂ T := by
        apply Module.Finite.iff_fg.mpr
        refine Submodule.fg_of_fg_map_of_fg_inf_ker P.mkQ ?_ ?_
        · exact Module.Finite.iff_fg.mp fdq
        · exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hinf)
      refine ⟨inferInstance, ?_⟩
      have hdim := finrank_le_map_add_inf' P.mkQ T
      have hker : Module.finrank ℂ (T ⊓ LinearMap.ker P.mkQ : Submodule ℂ V) ≤
          Module.finrank ℂ P := Submodule.finrank_mono hinf
      rw [Finset.sum_range_succ]
      change Module.finrank ℂ T ≤ _
      change Module.finrank ℂ P ≤ _ at bd
      change Module.finrank ℂ (T.map P.mkQ) ≤ _ at bdq
      omega

/-- Closed form when every cell cutoff lies between half the weight and the weight. -/
theorem cellFlag_bound_two (hS : SL2 E H F) (v : ℕ → V) (r n : ℕ) (ν : ℕ → ℕ)
    (hν : ∀ i < n, 1 ≤ ν i) (hlo : ∀ i < n, ν i ≤ r) (hhi : ∀ i < n, r ≤ 2 * ν i)
    (hR : ∀ i < n, CellRelations E H F (cellFlag E H F v i) (v i) r (ν i)) :
    FiniteDimensional ℂ (cellFlag E H F v n) ∧
      Module.finrank ℂ (cellFlag E H F v n) ≤
        ∑ i ∈ Finset.range n, 3 ^ (r - ν i) * 2 ^ (2 * ν i - r) := by
  obtain ⟨fd, bd⟩ := cellFlag_bound hS v r ν n hν hR
  refine ⟨fd, bd.trans_eq ?_⟩
  apply Finset.sum_congr rfl
  intro i hi
  have hn := Finset.mem_range.mp hi
  exact bal_prod_two (hν i hn) (hlo i hn) (hhi i hn)

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.cellFlag_bound
#print axioms VOA.DeligneAudit.SL4T.cellFlag_bound_two
