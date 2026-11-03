import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-! A reverse-echelon spanning argument for finite polynomial certificates.
The rows are actual relations modulo a submodule. No finite-dimensionality,
rank, independence, or certificate-validity assumption is hidden. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {N M : ℕ}

/-- Every non-normal column has an actual relation with a nonzero pivot and
only strictly later other columns. Reverse induction leaves the normal columns. -/
theorem echelon_span_le (P : Submodule K V) (b : Fin N → V)
    (normal : Fin M → Fin N)
    (rows : ∀ j : Fin N, j ∈ Set.range normal ∨
      ∃ c : Fin N → K, c j ≠ 0 ∧
        (∀ k : Fin N, k.val < j.val → c k = 0) ∧
        (∑ k, c k • b k) ∈ P) :
    Submodule.span K (Set.range b) ≤
      P ⊔ Submodule.span K (Set.range fun i => b (normal i)) := by
  let Q := P ⊔ Submodule.span K (Set.range fun i => b (normal i))
  have hb : ∀ r : ℕ, ∀ j : Fin N, N - j.val = r → b j ∈ Q := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro j hj
      rcases rows j with ⟨i, hi⟩ | ⟨c, hc, htri, hrow⟩
      · exact (show Submodule.span K (Set.range fun i => b (normal i)) ≤ Q from
          le_sup_right) (Submodule.subset_span ⟨i, congrArg b hi⟩)
      · have hrest : (∑ k ∈ Finset.univ.erase j, c k • b k) ∈ Q := by
          apply Submodule.sum_mem
          intro k hk
          have hne : k ≠ j := (Finset.mem_erase.mp hk).1
          by_cases hlt : k.val < j.val
          · rw [htri k hlt, zero_smul]
            exact Q.zero_mem
          · have hval : k.val ≠ j.val := fun e => hne (Fin.ext e)
            have hr : N - k.val < r := by omega
            exact Submodule.smul_mem Q (c k) (ih (N - k.val) hr k rfl)
        have hfull : (∑ k, c k • b k) ∈ Q :=
          (show P ≤ Q from le_sup_left) hrow
        have hpivot : c j • b j ∈ Q := by
          have heq : c j • b j = (∑ k, c k • b k) -
              ∑ k ∈ Finset.univ.erase j, c k • b k := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
            abel
          rw [heq]
          exact Q.sub_mem hfull hrest
        have hscale := Q.smul_mem (c j)⁻¹ hpivot
        simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hscale
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact hb (N - j.val) j rfl

end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.echelon_span_le
