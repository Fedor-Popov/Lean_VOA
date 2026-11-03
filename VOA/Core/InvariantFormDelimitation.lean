/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormFHLClosure
import VOA.Core.InvariantFormTranspose

set_option linter.style.longLine false

/-!
# The conditional FHL delimitation for arbitrary invariant forms

This file proves an axiom-free **conditional obstruction** to deriving
Frenkel–Huang–Lepowsky / Li full invariance (`InvariantForm.IsFullyInvariant`, Gannon 5.1.11a)
for an *arbitrary* invariant form.  It applies to the four general-`B` reduction rows

* `Core.InvariantFormFHL`       (`isFullyInvariant_of_propagation`, residual `hstep`),
* `Core.InvariantFormDiagonal`  (`isFullyInvariant_of_diagonal`, residual `DiagonalFHL`),
* `Core.InvariantFormPStep`     (`isFullyInvariant_of_pstep`, residual `PStep`),
* `Core.InvariantFormFHLClosure`(`isFullyInvariant_of_inputs`, residuals `GoodBound`+`CreationVanish`)

as follows: under `hqp` and an explicitly supplied invariant form whose restriction to `𝒱₁` is
nonsymmetric, each universal residual is false.  The file does **not** construct that witness, so
these are conditional non-universality theorems rather than a constructed counterexample.  The
genuine FHL theorem for the constructed canonical form is complete in
`Core.InvariantFormFHL2.canonicalInvariantForm_isFullyInvariant` (under `hne` + `hqp`).

## The mechanism

An `InvariantForm` carries `virasoro_adj : (Lₙa|b) = (a|L₋ₙb)`.  Under the quasi-primarity
hypothesis `hqp`, this file proves:

* **`fullyInvariant_forces_v1_symm`** — full invariance FORCES the `𝒱₁` pairing to be **symmetric**.
  (At `wt = 1, u ∈ 𝒱₁, n = −1, a = 𝟙`, full invariance gives `(u|v) = −(𝟙|u₍1₎v)` — the `j = 1`
  term dies by `hqp` (`L₁u = 0`), `u₍−1₎𝟙 = u`; then `oneMode_symm_grading1` (`u₍1₎v = v₍1₎u`, off
  the proven skew) symmetrizes the right-hand side.)

Consequently, if callers supply `B₀`, `u₀`, and `v₀` in grade one together with
`B₀.form u₀ v₀ ≠ B₀.form v₀ u₀`, then `B₀` cannot be fully invariant and all four universal
residual predicates above fail.  Existence of such data is not derived from `dim 𝒱₁ ≥ 2` here, and
no rank-two Heisenberg witness is constructed in this repository.

## The delimitation theorems (machine-checked)

Each theorem takes `hqp`, grade-membership proofs for `u₀,v₀`, and the explicit nonsymmetry proof
`hasym`:

* **`general_fullyInvariant_not_a_theorem`** — conditionally proves
  `¬ (∀ B, B.IsFullyInvariant)`; the master statement covers `Core.InvariantFormFHL`'s `hstep`.
* **`general_diagonalFHL_not_a_theorem`** — conditionally proves
  `¬ (∀ B, DiagonalFHL B)`.
* **`general_pstep_not_a_theorem`** — conditionally proves `¬ (∀ B, PStep B)`.
* **`general_fhlClosure_not_a_theorem`** — conditionally proves
  `¬ (∀ B, GoodBound B ∧ CreationVanish B)`.

This is the machine-checked companion of `Core.InvariantFormTranspose`
(`no_structural_symmetry_of_antisymmetrize_ne`, `form_smul_skew_transpose`): the entire general-`B`
toolkit (`virasoro_adj` + `form_smul_skew`) is transpose-blind.  Given a form with nonzero
antisymmetric part, this prevents that toolkit from forcing the slot order required by full
invariance.  The current file makes no unconditional claim about existence of such a form, either
on a general simple VOA or on a specific example.

## References
* Gannon §5.1.3, eq. (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA.VertexOperatorAlgebra

open scoped BigOperators

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **(★) The weight-1 vacuum slice of full invariance.**  For `u ∈ 𝒱₁` (so `L₁u = 0` by `hqp`),
full invariance evaluated at `wt = 1, n = −1, a = 𝟙` collapses to `(u|v) = −(𝟙 | u₍1₎v)`. -/
theorem form_eq_neg_vac_oneMode (B : InvariantForm W)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hFI : B.IsFullyInvariant) {u : 𝒱} (hu : u ∈ W.grading 1) (v : 𝒱) :
    B.form u v = - B.form W.vacuum (W.smul u 1 v) := by
  have h := hFI 1 u hu (-1) W.vacuum v
  -- LHS: u₍-1₎𝟙 = u
  rw [W.smul_vacuum_neg_one] at h
  -- RHS: range (1.toNat+1) = range 2 ; expand j=0, j=1
  rw [show ((1 : ℤ).toNat + 1) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at h
  -- j=1 term dies: L₁ u = 0
  have hL1u : W.L 1 u = 0 := hqp u hu
  rw [pow_one] at h
  rw [hL1u, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, add_zero] at h
  -- j=0 term: (L₁^0 u)₍2*1-(-1)-2-0₎ v = u₍1₎ v
  rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, inv_one,
    one_smul, show (2 * (1:ℤ) - (-1) - 2 - 0) = 1 by ring, zpow_one] at h
  rw [h, neg_one_smul]

/-- **Under `hqp`, full invariance forces symmetry on `𝒱₁`** (the obstruction). Combining the two `𝒱₁`
slices of `form_eq_neg_vac_oneMode` with `oneMode_symm_grading1` (`u₍1₎v = v₍1₎u`, off the proven
skew). The `InvariantForm` structure itself does not include this symmetry; non-universality below
requires an explicit witness that fails it. -/
theorem fullyInvariant_forces_v1_symm (B : InvariantForm W)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hFI : B.IsFullyInvariant) {u v : 𝒱} (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    B.form u v = B.form v u := by
  rw [form_eq_neg_vac_oneMode B hqp hFI hu v, form_eq_neg_vac_oneMode B hqp hFI hv u]
  rw [oneMode_symm_grading1 W hu hv]

/-! ## Conditional delimitation of the general-`B` FHL residuals -/

/-- **MASTER CONDITIONAL DELIMITATION.** If `hqp` holds and an explicitly supplied invariant form
fails `𝒱₁`-symmetry at `u₀,v₀`, then `∀ B, IsFullyInvariant B` is false. This is the universal
statement the four general-`B` reductions would need. No nonsymmetric form is constructed here. -/
theorem general_fullyInvariant_not_a_theorem
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {B₀ : InvariantForm W} {u₀ v₀ : 𝒱} (hu₀ : u₀ ∈ W.grading 1) (hv₀ : v₀ ∈ W.grading 1)
    (hasym : B₀.form u₀ v₀ ≠ B₀.form v₀ u₀) :
    ¬ (∀ B : InvariantForm W, B.IsFullyInvariant) := fun hAll =>
  hasym (fullyInvariant_forces_v1_symm B₀ hqp (hAll B₀) hu₀ hv₀)

/-- **Conditional delimitation for `Core.InvariantFormDiagonal`.** Under `hqp` and the explicit
nonsymmetric witness below, `∀ B, DiagonalFHL B` is false. -/
theorem general_diagonalFHL_not_a_theorem
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {B₀ : InvariantForm W} {u₀ v₀ : 𝒱} (hu₀ : u₀ ∈ W.grading 1) (hv₀ : v₀ ∈ W.grading 1)
    (hasym : B₀.form u₀ v₀ ≠ B₀.form v₀ u₀) :
    ¬ (∀ B : InvariantForm W, DiagonalFHL B) := fun hAll =>
  general_fullyInvariant_not_a_theorem hqp hu₀ hv₀ hasym
    (fun B => isFullyInvariant_of_diagonal B (hAll B))

/-- **Conditional delimitation for `Core.InvariantFormPStep`.** Under `hqp` and the explicit
nonsymmetric witness below, `∀ B, PStep B` is false. -/
theorem general_pstep_not_a_theorem
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {B₀ : InvariantForm W} {u₀ v₀ : 𝒱} (hu₀ : u₀ ∈ W.grading 1) (hv₀ : v₀ ∈ W.grading 1)
    (hasym : B₀.form u₀ v₀ ≠ B₀.form v₀ u₀) :
    ¬ (∀ B : InvariantForm W, PStep B) := fun hAll =>
  general_fullyInvariant_not_a_theorem hqp hu₀ hv₀ hasym
    (fun B => isFullyInvariant_of_pstep B (hAll B))

/-- **Conditional delimitation for `Core.InvariantFormFHLClosure`.** Under `hqp` and the explicit
nonsymmetric witness below, `∀ B, GoodBound B ∧ CreationVanish B` is false. -/
theorem general_fhlClosure_not_a_theorem
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {B₀ : InvariantForm W} {u₀ v₀ : 𝒱} (hu₀ : u₀ ∈ W.grading 1) (hv₀ : v₀ ∈ W.grading 1)
    (hasym : B₀.form u₀ v₀ ≠ B₀.form v₀ u₀) :
    ¬ (∀ B : InvariantForm W, GoodBound B ∧ CreationVanish B) := fun hAll =>
  general_fullyInvariant_not_a_theorem hqp hu₀ hv₀ hasym
    (fun B => isFullyInvariant_of_inputs B (hAll B).1 (hAll B).2)

/-- The implication form: if every invariant form were fully invariant (equivalently, if the general
`DiagonalFHL` held), then every invariant form would be `𝒱₁`-symmetric. An explicitly supplied
nonsymmetric witness would contradict that conclusion. -/
theorem diagonalFHL_all_forces_v1_symm
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hAll : ∀ B : InvariantForm W, DiagonalFHL B) :
    ∀ (B : InvariantForm W) {u v : 𝒱}, u ∈ W.grading 1 → v ∈ W.grading 1 →
      B.form u v = B.form v u := by
  intro B u v hu hv
  exact fullyInvariant_forces_v1_symm B hqp (isFullyInvariant_of_diagonal B (hAll B)) hu hv

end VOA.VertexOperatorAlgebra
