/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroPolyTensor

/-!
# Energy bookkeeping for the polynomial structure tensor

This is step 3(B1) of the `∂_c` route (the steps are listed in `VirasoroPolyStructure`).

* `repr_polyComb`: the sorted-basis coordinates of `polyComb c Q`, for sorted `Q`, are the values
  `Q_v(c)`.
* `repr_support_energy`: a vector of energy `N` has sorted coordinates only on words of energy `N`.
* `energy_of_mem_grading`: a sorted polynomial combination lying in energy `N` at **every** `c` is
  supported on words of energy `N`.
* `energy_tensorW`: the expansion of `u₍ₖ₎w` lives in energy `e(u) + e(w) − k − 1`. In particular
  `tensorW_eq_zero` holds when that energy is negative, which gives `c`-uniform truncation.
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

theorem repr_negWord (c : ℂ) (v : {w : List ℕ // SortedWord w}) :
    (sortedBasisVir c).repr (negWordVir c v.1) = Finsupp.single v 1 := by
  rw [← sortedBasisVir_apply, Module.Basis.repr_self]

/-- The sorted coordinates of a sorted polynomial combination are its values at `c`. -/
theorem repr_polyComb (c : ℂ) {Q : PV} (hQ : Sorted Q) (v : {w : List ℕ // SortedWord w}) :
    (sortedBasisVir c).repr (polyComb c Q) v = (Q v.1).eval c := by
  classical
  rw [polyComb_eq_sum, ← Finset.sum_attach, map_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ u : Q.support, (sortedBasisVir c).repr ((Q u.1).eval c • negWordVir c u.1) v
      = (fun u : List ℕ => if u = v.1 then (Q u).eval c else 0) u.1 := by
    intro u
    rw [map_smul, repr_negWord c ⟨u.1, hQ u.1 u.2⟩, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : u.1 = v.1
    · have : (⟨u.1, hQ u.1 u.2⟩ : {w : List ℕ // SortedWord w}) = v := Subtype.ext h
      simp [h]
    · have : (⟨u.1, hQ u.1 u.2⟩ : {w : List ℕ // SortedWord w}) ≠ v := fun e => h (congrArg Subtype.val e)
      simp [this, h]
  rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_attach Q.support
    (fun u : List ℕ => if u = v.1 then (Q u).eval c else 0), Finset.sum_ite_eq']
  split_ifs with hv
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hv, eval_zero]

/-- A vector of energy `N` has sorted coordinates only on words of energy `N`. -/
theorem repr_support_energy (c : ℂ) {N : ℤ} {x : VirUniv c} (hx : x ∈ gradingVir c N) :
    ∀ v ∈ ((sortedBasisVir c).repr x).support, (energyVir v.1 : ℤ) = N := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ws, hen, rfl⟩ := hy
      obtain ⟨Q, hQ, hQe⟩ := exists_sorted_polyComb ws
      intro v hv
      have hs : Sorted Q := fun u hu => (hQ u hu).1
      rw [hQe c, Finsupp.mem_support_iff, repr_polyComb c hs] at hv
      have hvQ : v.1 ∈ Q.support := by
        rw [Finsupp.mem_support_iff]; intro h0; exact hv (by rw [h0, eval_zero])
      rw [(hQ v.1 hvQ).2, hen]
  | zero => intro v hv; simp at hv
  | add a b _ _ ha hb =>
      intro v hv
      rw [map_add] at hv
      exact (Finset.mem_union.mp (Finsupp.support_add hv)).elim (ha v) (hb v)
  | smul r a _ ha =>
      intro v hv
      rw [map_smul] at hv
      exact ha v (Finsupp.support_smul hv)

/-- A sorted polynomial combination of energy `N` at every `c` is supported in energy `N`. -/
theorem energy_of_mem_grading {P : PV} (hP : Sorted P) {N : ℤ}
    (h : ∀ c : ℂ, polyComb c P ∈ gradingVir c N) :
    ∀ u ∈ P.support, (energyVir u : ℤ) = N := by
  intro u hu
  by_contra hne
  apply Finsupp.mem_support_iff.mp hu
  refine Polynomial.funext fun c => ?_
  rw [eval_zero, ← repr_polyComb c hP ⟨u, hP u hu⟩]
  by_contra h0
  exact hne (repr_support_energy c (h c) ⟨u, hP u hu⟩ (Finsupp.mem_support_iff.mpr h0))

/-- The expansion of `u₍ₖ₎w` lives in energy `e(u) + e(w) − k − 1`. -/
theorem energy_tensorW (u : List ℕ) (k : ℤ) (w : List ℕ) :
    ∀ v ∈ (tensorW u k w).support,
      (energyVir v : ℤ) = (energyVir u : ℤ) + energyVir w - k - 1 :=
  energy_of_mem_grading (sorted_tensorW u k w) fun c => by
    rw [polyComb_tensorW]
    exact virYA_grading_mode c _ (negWord_mem_gradingVir c u) _ (negWord_mem_gradingVir c w) k

/-- `c`-uniform truncation: `u₍ₖ₎w = 0` once the target energy is negative. -/
theorem tensorW_eq_zero {u w : List ℕ} {k : ℤ}
    (hk : (energyVir u : ℤ) + energyVir w - k - 1 < 0) : tensorW u k w = 0 := by
  ext v : 1
  by_contra h
  have := energy_tensorW u k w v (Finsupp.mem_support_iff.mpr h)
  omega

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.energy_of_mem_grading
#print axioms VOA.VirPoly.energy_tensorW
#print axioms VOA.VirPoly.tensorW_eq_zero
end AxiomAudit
