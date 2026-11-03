/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.TraceNonvanish

/-!
# The `T`-eigenvalue hypothesis, made transparent

`Modularity.TraceIndependence.traceIndependent_of_tEigen_injective` carries the hypothesis
`Function.Injective (tEigen W h)` with `tEigen W h i = e^{2πi(hᵢ − c/24)}`.  This file replaces it
by the transparent condition on the conformal weights themselves:

  `tEigen_injective_iff : Function.Injective (tEigen W h) ↔ ∀ i j, (∃ n : ℤ, h i − h j = n) → i = j`

i.e. **the conformal weights are pairwise distinct modulo `ℤ`**.

## Scope — why this is a hypothesis and not a theorem

It is *not* derivable for a general `C₂`-cofinite rational VOA.  Conformal weights add under
tensor products, so for `𝒱 = 𝒱₁ ⊗ 𝒱₂` the irreducibles are `M₁ ⊗ M₂` and distinct pairs can have
equal — indeed equal, not merely congruent — conformal weights; the same happens for lattice VOAs
whose discriminant form has repeated values.  So the honest statement is the one above: a named,
checkable condition on the weight vector, true in the cases where Zhu's `ρ(T)` is regular.

The **general** case is not lost: `Modularity.TraceIndependence.traceIndependent_of_fibreIndependent`
already reduces `TraceIndependent` — with **no** distinctness hypothesis — to `FibreIndependent`,
independence *within one `T`-eigenvalue class*, which is exactly the top-level `A(𝒱)`-character
separation of Zhu Thm 5.3.3.  `tEigen_injective_iff` says precisely when that fibre condition is
vacuous: when every fibre is a singleton.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}

/-- Two `T`-eigenvalues agree exactly when the conformal weights differ by an integer. -/
theorem tEigen_eq_iff (h : ι → ℂ) (i j : ι) :
    tEigen W h i = tEigen W h j ↔ ∃ n : ℤ, h i - h j = (n : ℂ) := by
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_ne_zero]
  constructor
  · intro heq
    rw [tEigen, tEigen, modularTEntry, modularTEntry, Complex.exp_eq_exp_iff_exists_int] at heq
    obtain ⟨n, hn⟩ := heq
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (h i - h j - (n : ℂ)) = 0 := by
      linear_combination hn
    rcases mul_eq_zero.mp h2 with hc | hc
    · exact absurd hc hpi
    · linear_combination hc
  · rintro ⟨n, hn⟩
    rw [tEigen, tEigen, modularTEntry, modularTEntry, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n, ?_⟩
    have hij : h i = h j + (n : ℂ) := by linear_combination hn
    rw [hij]
    ring

/-- **The `T`-eigenvalue hypothesis, transparently.**  `tEigen` is injective exactly when the
conformal weights are pairwise distinct modulo `ℤ`. -/
theorem tEigen_injective_iff (h : ι → ℂ) :
    Function.Injective (tEigen W h) ↔ ∀ i j : ι, (∃ n : ℤ, h i - h j = (n : ℂ)) → i = j := by
  constructor
  · intro hinj i j hij
    exact hinj ((tEigen_eq_iff h i j).mpr hij)
  · intro hsep i j hij
    exact hsep i j ((tEigen_eq_iff h i j).mp hij)

/-- **`TraceIndependent` from pairwise distinct conformal weights mod `ℤ`.**  The same
statement as `traceIndependent_of_orderedSpanning`, with the `T`-eigenvalue hypothesis replaced
by the transparent weight condition. -/
theorem traceIndependent_of_weights_distinct_mod_int (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ i j : ι, (∃ n : ℤ, h i - h j = (n : ℂ)) → i = j)
    (hspan : ∀ i, Nonempty (OrderedSpanningData (Mfam i).isMod (h i))) :
    TraceIndependent Mfam h :=
  traceIndependent_of_orderedSpanning Mfam h hcw ((tEigen_injective_iff h).mpr hsep) hspan

end VOA
