/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Deligne's fiber functor — characters of countable-dimensional algebras

Deligne's construction of a fiber functor produces a nonzero commutative `ℂ`-algebra `R`
(`= Hom(𝟙, A)` for the frame algebra `A`) of **countable dimension**, and needs a `ℂ`-point of it.

* `isAlgebraic_of_rank_le_aleph0` — a field extension `K / ℂ` of countable dimension is algebraic
  (a transcendental `x` gives the uncountable independent family `(x - a)⁻¹`, `a ∈ ℂ`:
  Mathlib's `Transcendental.linearIndependent_sub_inv`);
* `exists_algHom_of_rank_le_aleph0` — a nontrivial commutative `ℂ`-algebra of countable
  dimension has a character `R →ₐ[ℂ] ℂ` (quotient by a maximal ideal; the residue field is
  algebraic over the algebraically closed `ℂ`, hence `ℂ`).

VOA-free.  No `sorry`, no new axioms.
-/

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open Cardinal Module

/-- A field extension of `ℂ` of countable dimension is algebraic. -/
theorem isAlgebraic_of_rank_le_aleph0 {K : Type*} [Field K] [Algebra ℂ K]
    (h : Module.rank ℂ K ≤ ℵ₀) : Algebra.IsAlgebraic ℂ K := by
  refine ⟨fun x => ?_⟩
  by_contra hx
  have hli := Transcendental.linearIndependent_sub_inv (F := ℂ) (E := K) hx
  have h1 := hli.cardinal_lift_le_rank
  rw [Cardinal.mk_complex, Cardinal.lift_continuum] at h1
  have h2 : Cardinal.lift.{0} (Module.rank ℂ K) ≤ ℵ₀ := by
    simpa using Cardinal.lift_le.{0}.2 h
  have := h1.trans (by simpa using h2)
  exact absurd this (not_le.2 Cardinal.aleph0_lt_continuum)

/-- **A nontrivial commutative `ℂ`-algebra of countable dimension has a character.** -/
theorem exists_algHom_of_rank_le_aleph0 {R : Type*} [CommRing R] [Algebra ℂ R] [Nontrivial R]
    (h : Module.rank ℂ R ≤ ℵ₀) : Nonempty (R →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hK : Module.rank ℂ (R ⧸ m) ≤ ℵ₀ :=
    (LinearMap.rank_le_of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℂ m)).trans h
  haveI := isAlgebraic_of_rank_le_aleph0 hK
  haveI : Algebra.IsIntegral ℂ (R ⧸ m) := Algebra.IsAlgebraic.isIntegral
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := R ⧸ m)
  let e : ℂ ≃ₐ[ℂ] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ m)) hb
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m)⟩

end VOA.Huang.TensorCat.DeligneFiber
