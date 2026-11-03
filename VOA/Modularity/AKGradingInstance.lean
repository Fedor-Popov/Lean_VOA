/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.AKGrading
import VOA.Modularity.JInvariantAnalytic

/-!
# `AKWeightGrading`, part (A): `E46` is graded by modular weight

`ℂ⟨E₄, E₆⟩` is the internal direct sum of its modular-weight subspaces (`e46WeightSpace_isInternal`).

* Spanning: `E₄`, `E₆` and the constants are homogeneous, and the weights add under products.
* Independence: if `Σ_k f_k = 0` with `f_k` of weight `k`, fix `z ∈ ℍ` and apply the relation at
  `γ_n z`, where `γ_n = [[1,0],[n,1]]`. This gives `Σ_k (nz+1)^k f_k(z) = 0` for every `n`. So the
  polynomial `Σ_k f_k(z) X^k` has the infinitely many roots `nz+1` and vanishes. Negative weights are
  already zero at level one.

This is the coefficient field `coeffDecomposition` of `AKWeightGrading`, uniformly in `W`.
-/

open scoped MatrixGroups
open UpperHalfPlane

namespace VOA

/-- The lower unipotent `γ_n = [[1,0],[n,1]] ∈ SL₂(ℤ)`. -/
def lowerUnip (n : ℤ) : SL(2, ℤ) := ⟨!![1, 0; n, 1], by simp [Matrix.det_fin_two]⟩

theorem E46Weight.apply_lowerUnip {k : ℤ} {f : E46} (hf : E46Weight k f) (n : ℤ) (z : ℍ) :
    (f : ℍ → ℂ) (lowerUnip n • z) = ((n : ℂ) * z + 1) ^ k * (f : ℍ → ℂ) z := by
  obtain ⟨F, hF⟩ := hf
  rw [hF, slashInvariant_smul F (lowerUnip n) z]
  simp [lowerUnip]

theorem E46Weight.coe_eq_zero_of_neg {k : ℤ} {f : E46} (hf : E46Weight k f) (hk : k < 0) :
    (f : ℍ → ℂ) = 0 := by
  obtain ⟨F, hF⟩ := hf
  rw [hF]
  exact ModularFormClass.levelOne_neg_weight_eq_zero hk F

/-- **Modular forms of distinct weights are independent.** -/
theorem e46WeightSpace_iSupIndep : iSupIndep e46WeightSpace := by
  classical
  apply iSupIndep_of_dfinsupp_lsum_injective
  rw [injective_iff_map_eq_zero]
  intro v hv
  -- the relation, pointwise
  have hsum : ∀ y : ℍ, ∑ j ∈ v.support, ((v j : E46) : ℍ → ℂ) y = 0 := by
    intro y
    have h := congrArg (fun g : E46 => (g : ℍ → ℂ) y) hv
    simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
      ZeroMemClass.coe_zero] at h
    simpa [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum] using h
  have hw : ∀ j, E46Weight j (v j : E46) := fun j => (v j).2
  ext k : 1
  apply Subtype.ext
  apply Subtype.ext
  funext z
  show ((v k : E46) : ℍ → ℂ) z = 0
  rcases lt_or_ge k 0 with hk | hk
  · rw [(hw k).coe_eq_zero_of_neg hk]; rfl
  -- the polynomial `Σ_j f_j(z) X^j`
  let P : Polynomial ℂ := ∑ j ∈ v.support,
    Polynomial.C (((v j : E46) : ℍ → ℂ) z) * Polynomial.X ^ j.toNat
  have hzero_neg : ∀ j, j < 0 → ((v j : E46) : ℍ → ℂ) z = 0 := fun j hj => by
    rw [(hw j).coe_eq_zero_of_neg hj]; rfl
  have hroot : ∀ n : ℕ, P.eval ((n : ℂ) * z + 1) = 0 := by
    intro n
    have h := hsum (lowerUnip n • z)
    simp only [fun j => (hw j).apply_lowerUnip (n : ℤ) z, Int.cast_natCast] at h
    rw [← h, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rcases lt_or_ge j 0 with hj | hj
    · rw [hzero_neg j hj]; ring
    · rw [← zpow_natCast, Int.toNat_of_nonneg hj, mul_comm]
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hinf : {x | P.IsRoot x}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * z + 1) ?_ ?_
    · intro a b hab
      have : (a : ℂ) * z = (b : ℂ) * z := by simpa using hab
      exact_mod_cast mul_right_cancel₀ hz0 this
    · intro n; exact hroot n
  have hP : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinf
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff k.toNat) hP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hc
  by_cases hks : k ∈ v.support
  · rw [Finset.sum_eq_single k] at hc
    · simpa using hc
    · intro j _ hjk
      rcases lt_or_ge j 0 with hj | hj
      · rw [hzero_neg j hj, zero_mul]
      · rw [if_neg (by omega), mul_zero]
    · intro h; exact absurd hks h
  · rw [DFinsupp.notMem_support_iff.mp hks]; rfl

/-- Products of sums of homogeneous elements are sums of homogeneous elements. -/
theorem mul_mem_iSup_e46WeightSpace {x y : E46} (hx : x ∈ ⨆ k, e46WeightSpace k)
    (hy : y ∈ ⨆ k, e46WeightSpace k) : x * y ∈ ⨆ k, e46WeightSpace k := by
  induction hx using Submodule.iSup_induction' with
  | mem i x hx =>
      induction hy using Submodule.iSup_induction' with
      | mem j y hy => exact Submodule.mem_iSup_of_mem (i + j) (E46Weight.mul hx hy)
      | zero => simp
      | add y y' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
  | zero => simp
  | add x x' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'

theorem e46WeightSpace_iSup_eq_top : ⨆ k, e46WeightSpace k = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨f, hf⟩ -
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
      rcases hg with rfl | rfl
      · exact Submodule.mem_iSup_of_mem 4 e46E4_weight
      · exact Submodule.mem_iSup_of_mem 6 e46E6_weight
  | algebraMap c =>
      refine Submodule.mem_iSup_of_mem 0 ?_
      have h := E46Weight.smul c E46Weight.one
      convert h using 1
      ext; simp
  | add f g hf hg ihf ihg =>
      exact Submodule.add_mem _ ihf ihg
  | mul f g hf hg ihf ihg =>
      exact mul_mem_iSup_e46WeightSpace ihf ihg

/-- **`E46` is the internal direct sum of its modular-weight spaces.** -/
theorem e46WeightSpace_isInternal : DirectSum.IsInternal e46WeightSpace :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨e46WeightSpace_iSupIndep, e46WeightSpace_iSup_eq_top⟩

/-- The coefficient decomposition of `AKWeightGrading`. -/
@[reducible] noncomputable def e46Decomposition : DirectSum.Decomposition e46WeightSpace :=
  e46WeightSpace_isInternal.chooseDecomposition

end VOA

section AxiomAudit
#print axioms VOA.e46WeightSpace_iSupIndep
#print axioms VOA.e46WeightSpace_isInternal
end AxiomAudit
