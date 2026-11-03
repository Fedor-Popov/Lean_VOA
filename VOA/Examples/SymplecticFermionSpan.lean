/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionWords
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Symplectic fermions: the creation monomials span the Fock space

`reconstructε` builds the vertex operator by declaring its value on the states the word fields
create from the vacuum, `stWordSF l`, and extending linearly.  For that to define an operator on
*all* of `FockSF` those states must already exhaust the space; this file supplies exactly that
hypothesis (`hspan` of `reconstructε`), as `stWordSF_span`.

## Why this needs an argument

`FockSF = CliffordAlgebra QSF` sits on the *infinite-dimensional* mode space `SFModes`, so there
is no finite basis of the algebra to exhibit.  What Mathlib provides is the graded decomposition
`CliffordAlgebra.iSup_ι_range_eq_top`: the algebra is the supremum of the submodules
`(LinearMap.range (ι Q)) ^ i`, i.e. every element is a finite sum of products of `ι v` for
**arbitrary** vectors `v : SFModes`.  Two gaps separate that from the words.

* The vectors `v` are arbitrary, whereas a word is built from the coordinate generators
  `Finsupp.single p 1` only.  Since `ι` is linear and multiplication is bilinear, expanding each
  factor of a length-`i` product turns it into a finite `ℂ`-combination of products of `i`
  *coordinate* `ι`'s.  That expansion is `ι_mul_mem_stSpanSF`, by `Finsupp.induction_linear`
  on `v`.
* Those coordinate products have to be recognised as words.  `stWordSF` is defined by consing on
  the **left** (`stWordSF (p :: rest) = ι (single p 1) * stWordSF rest`), so the span is closed
  under left multiplication by a coordinate `ι` almost by definition — `ι_single_mul_mem_stSpanSF`
  — and that one closure property is the entire content of the theorem: it lets an induction on
  `i` strip the factors of `(range ι) ^ i` off one at a time, from the left.

So the shape of the proof is: closure under one coordinate creation operator (words), then under
one arbitrary `ι v` (linearity), then under `i` of them (induction), then the Mathlib supremum.
-/

namespace VOA.SympFerm

open CliffordAlgebra

/-- The `ℂ`-span of the creation monomials — the subspace `reconstructε` can see. -/
noncomputable def stSpanSF : Submodule ℂ FockSF := Submodule.span ℂ (Set.range stWordSF)

theorem stWordSF_mem (l : SFWord) : stWordSF l ∈ stSpanSF :=
  Submodule.subset_span ⟨l, rfl⟩

/-- The empty word is the vacuum `1`, so the span contains the algebra unit — the base case of
the power induction below. -/
theorem one_mem_stSpanSF : (1 : FockSF) ∈ stSpanSF := by
  have h : stWordSF [] ∈ stSpanSF := stWordSF_mem []
  rwa [stWordSF_nil] at h

/-- **Closure under one coordinate creation operator.**  This is the heart of the file: on a word
the operator `x ↦ ι (single p 1) * x` is precisely `cons p`, so it maps generators of the span to
generators; the remaining cases are just linearity of multiplication. -/
theorem ι_single_mul_mem_stSpanSF (p : ℕ × Fin 2) {x : FockSF} (hx : x ∈ stSpanSF) :
    ι QSF (Finsupp.single p (1 : ℂ)) * x ∈ stSpanSF := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      rw [← stWordSF_cons]
      exact stWordSF_mem (p :: l)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/-- **Closure under an arbitrary Clifford generator.**  Every `v : SFModes` is a finite
`ℂ`-combination of coordinate vectors `single p 1` (`Finsupp.induction_linear`), and both `ι` and
multiplication are linear, so the previous lemma propagates. -/
theorem ι_mul_mem_stSpanSF (v : SFModes) {x : FockSF} (hx : x ∈ stSpanSF) :
    ι QSF v * x ∈ stSpanSF := by
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | add f g hf hg => rw [map_add, add_mul]; exact Submodule.add_mem _ hf hg
  | single p c =>
      rw [← Finsupp.smul_single_one p c, map_smul, smul_mul_assoc]
      exact Submodule.smul_mem _ _ (ι_single_mul_mem_stSpanSF p hx)

/-- Every `i`-fold product of Clifford generators lies in the span.  Induction on `i`, peeling one
factor off the **left** (`pow_succ'`) so that `ι_mul_mem_stSpanSF` applies to it; the base case
`i = 0` is the unit, which is the empty word. -/
theorem range_ι_pow_le_stSpanSF (i : ℕ) : LinearMap.range (ι QSF) ^ i ≤ stSpanSF := by
  induction i with
  | zero => rw [pow_zero]; exact Submodule.one_le.mpr one_mem_stSpanSF
  | succ n ih =>
      rw [pow_succ']
      refine Submodule.mul_le.mpr ?_
      rintro _ ⟨v, rfl⟩ y hy
      exact ι_mul_mem_stSpanSF v (ih hy)

/-- The span of the creation monomials is everything, phrased for `stSpanSF`. -/
theorem stSpanSF_eq_top : stSpanSF = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← CliffordAlgebra.iSup_ι_range_eq_top (Q := QSF)]
  exact iSup_le range_ι_pow_le_stSpanSF

/-- **The creation monomials span the symplectic-fermion Fock space.**  This is the `hspan`
hypothesis of `reconstructε`. -/
theorem stWordSF_span : Submodule.span ℂ (Set.range stWordSF) = (⊤ : Submodule ℂ FockSF) :=
  stSpanSF_eq_top

end VOA.SympFerm
