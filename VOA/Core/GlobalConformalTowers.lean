/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.QuasiPrimaryDecomp
import VOA.Core.InvariantFormFHL

/-!
# Invariant forms on global conformal towers

This file packages the metric consequences of the global `sl₂` action.  If `v` is
quasi-primary of weight `m`, then its `r`-th global descendant has pairing

`(L₋₁^r u | L₋₁^r v) = r! (2m)_r (u | v)`.

It also records that distinct descendant levels of quasi-primary vectors are orthogonal for a
symmetric invariant form.  These are the global-tower reductions used in the graded-unitarity
argument; they require no PBW or Virasoro-simple-module assumptions.

## References

* T. Gannon, *Moonshine Beyond the Monster* (2006), §5.2.
-/

set_option linter.style.longLine false

open scoped BigOperators
open VOA.VertexOperatorAlgebra

namespace VOA

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The global-descendant factor `r! (2m)_r`, written as the product of the one-step `sl₂`
coefficients.  This form works uniformly for integral conformal weight `m`. -/
def globalDescendantFactor (m : ℤ) (r : ℕ) : ℂ :=
  ∏ j ∈ Finset.range r, (((j : ℂ) + 1) * (2 * (m : ℂ) + (j : ℂ)))

@[simp]
theorem globalDescendantFactor_zero (m : ℤ) : globalDescendantFactor m 0 = 1 := by
  simp [globalDescendantFactor]

/-- The product recursion for `r! (2m)_r`. -/
theorem globalDescendantFactor_succ (m : ℤ) (r : ℕ) :
    globalDescendantFactor m (r + 1) =
      (((r : ℂ) + 1) * (2 * (m : ℂ) + (r : ℂ))) * globalDescendantFactor m r := by
  rw [globalDescendantFactor, Finset.prod_range_succ]
  simp only [globalDescendantFactor]
  ring

/-- At positive integral conformal weight, the global-descendant factor is the complex coercion
of a strictly positive real number.  This is the sign-preservation input for a global conformal
tower. -/
theorem globalDescendantFactor_real_pos {m : ℤ} (hm : 0 < m) (r : ℕ) :
    ∃ a : ℝ, 0 < a ∧ globalDescendantFactor m r = (a : ℂ) := by
  let a : ℝ := ∏ j ∈ Finset.range r,
    (((j : ℝ) + 1) * (2 * (m : ℝ) + (j : ℝ)))
  refine ⟨a, ?_, ?_⟩
  · dsimp [a]
    apply Finset.prod_pos
    intro j hj
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hj' : (0 : ℝ) ≤ (j : ℝ) := by positivity
    positivity
  · simp only [a, globalDescendantFactor]
    push_cast
    rfl

/-- Iterating the global `sl₂` tower formula gives
`L₁^r L₋₁^r v = r! (2m)_r v` for a quasi-primary vector `v` of weight `m`.

This is Gannon §5.2's lowest-weight `sl₂` calculation, with the coefficient packaged as
`globalDescendantFactor`. -/
theorem L1_pow_Lneg1_pow (W : VertexOperatorAlgebra V) {m : ℤ} {v : V}
    (hv : v ∈ W.grading m) (hqpv : W.L 1 v = 0) (r : ℕ) :
    (W.L 1 ^ r) ((W.L (-1) ^ r) v) = globalDescendantFactor m r • v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Module.End.mul_apply, L1_tower W hv hqpv r, map_smul, ih, smul_smul,
      globalDescendantFactor_succ]

namespace VertexOperatorAlgebra.InvariantForm

/-- One step of the global-descendant pairing recursion.  If `v` is quasi-primary of weight `m`,
then adjoining one `L₋₁` on both sides multiplies the pairing by `(r+1)(2m+r)`.

No symmetry or nondegeneracy of the invariant form is needed. -/
theorem form_globalDescendant_succ (B : InvariantForm W) {m : ℤ} (u : V) {v : V}
    (hv : v ∈ W.grading m) (hqpv : W.L 1 v = 0) (r : ℕ) :
    B.form ((W.L (-1) ^ (r + 1)) u) ((W.L (-1) ^ (r + 1)) v) =
      (((r : ℂ) + 1) * (2 * (m : ℂ) + (r : ℂ))) •
        B.form ((W.L (-1) ^ r) u) ((W.L (-1) ^ r) v) := by
  calc
    B.form ((W.L (-1) ^ (r + 1)) u) ((W.L (-1) ^ (r + 1)) v) =
        B.form ((W.L (-1) ^ r) u) (W.L 1 ((W.L (-1) ^ (r + 1)) v)) := by
      rw [pow_succ', Module.End.mul_apply]
      simpa using B.virasoro_adj (-1) ((W.L (-1) ^ r) u)
        (W.L (-1) ((W.L (-1) ^ r) v))
    _ = (((r : ℂ) + 1) * (2 * (m : ℂ) + (r : ℂ))) •
        B.form ((W.L (-1) ^ r) u) ((W.L (-1) ^ r) v) := by
      rw [L1_tower W hv hqpv r]
      exact map_smul (B.form ((W.L (-1) ^ r) u)) _ _

/-- **Global-descendant pairing formula.**  Descending the same number of times on both sides
multiplies the base pairing by `r! (2m)_r`.

This is the metric part of the global quasi-primary reduction in Gannon §5.2.  Only the second
base vector must be quasi-primary; symmetry is not used. -/
theorem form_globalDescendant (B : InvariantForm W) {m : ℤ} (u : V) {v : V}
    (hv : v ∈ W.grading m) (hqpv : W.L 1 v = 0) (r : ℕ) :
    B.form ((W.L (-1) ^ r) u) ((W.L (-1) ^ r) v) =
      globalDescendantFactor m r • B.form u v := by
  rw [VertexOperatorAlgebra.form_Lneg1_pow B]
  rw [L1_pow_Lneg1_pow W hv hqpv r]
  exact map_smul (B.form u) _ _

/-- A quasi-primary vector is orthogonal, in the first slot, to every nonzero global descendant.
This is immediate from `L₁ ⊣ L₋₁`. -/
theorem form_quasiPrimary_Lneg1_pow_succ (B : InvariantForm W) {u : V}
    (hqpu : W.L 1 u = 0) (v : V) (r : ℕ) :
    B.form u ((W.L (-1) ^ (r + 1)) v) = 0 := by
  rw [pow_succ', Module.End.mul_apply]
  rw [← B.virasoro_adj 1, hqpu]
  simp

/-- If `u,v` are quasi-primary and the left descendant depth is strictly smaller than the right
depth, then the two descendants are orthogonal.  Symmetry is not needed in this orientation. -/
theorem form_globalTowers_eq_zero_of_lt (B : InvariantForm W) {m : ℤ} {u v : V}
    (hqu : W.L 1 u = 0) (hv : v ∈ W.grading m) (hqv : W.L 1 v = 0)
    {r s : ℕ} (hrs : r < s) :
    B.form ((W.L (-1) ^ r) u) ((W.L (-1) ^ s) v) = 0 := by
  induction r generalizing s with
  | zero =>
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
      simpa using B.form_quasiPrimary_Lneg1_pow_succ hqu v s
  | succ r ih =>
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
      have hrs' : r < s := by omega
      calc
        B.form ((W.L (-1) ^ (r + 1)) u) ((W.L (-1) ^ (s + 1)) v) =
            B.form ((W.L (-1) ^ r) u) (W.L 1 ((W.L (-1) ^ (s + 1)) v)) := by
          rw [pow_succ', Module.End.mul_apply]
          simpa using B.virasoro_adj (-1) ((W.L (-1) ^ r) u)
            ((W.L (-1) ^ (s + 1)) v)
        _ = (((s : ℂ) + 1) * (2 * (m : ℂ) + (s : ℂ))) •
            B.form ((W.L (-1) ^ r) u) ((W.L (-1) ^ s) v) := by
          rw [L1_tower W hv hqv s]
          exact map_smul (B.form ((W.L (-1) ^ r) u)) _ _
        _ = 0 := by rw [ih hrs', smul_zero]

/-- **Orthogonality of distinct global descendant levels.**  For a symmetric invariant form,
descendants of quasi-primary vectors at different depths are orthogonal.

Together with `form_globalDescendant`, this says that an orthogonal basis of a quasi-primary
multiplicity space generates mutually orthogonal global conformal towers. -/
theorem form_globalTowers_eq_zero_of_ne (B : InvariantForm W) (hB : B.IsSymmetric)
    {m n : ℤ} {u v : V} (hu : u ∈ W.grading m) (hqu : W.L 1 u = 0)
    (hv : v ∈ W.grading n) (hqv : W.L 1 v = 0) {r s : ℕ} (hrs : r ≠ s) :
    B.form ((W.L (-1) ^ r) u) ((W.L (-1) ^ s) v) = 0 := by
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · exact B.form_globalTowers_eq_zero_of_lt hqu hv hqv hrs
  · rw [hB]
    exact B.form_globalTowers_eq_zero_of_lt hqv hu hqu hsr

/-- Orthogonal quasi-primary bases generate orthogonal towers, including at equal descendant
depth. -/
theorem form_globalTowers_eq_zero (B : InvariantForm W) (hB : B.IsSymmetric)
    {m n : ℤ} {u v : V} (hu : u ∈ W.grading m) (hqu : W.L 1 u = 0)
    (hv : v ∈ W.grading n) (hqv : W.L 1 v = 0) (huv : B.form u v = 0)
    (r s : ℕ) : B.form ((W.L (-1) ^ r) u) ((W.L (-1) ^ s) v) = 0 := by
  by_cases hrs : r = s
  · subst s
    rw [B.form_globalDescendant u hv hqv r, huv, smul_zero]
  · exact B.form_globalTowers_eq_zero_of_ne hB hu hqu hv hqv hrs

end VertexOperatorAlgebra.InvariantForm

end VOA
