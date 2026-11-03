/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Extension
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Field automorphisms of `ℂ` detect rationality

A complex number fixed by every ring endomorphism `σ : ℂ →+* ℂ` is rational. This is the
Galois-theoretic input to the Anderson–Moore rationality argument.

The proof extends automorphisms along a transcendence basis: if `v` is a transcendence basis of
`ℂ` over a ring `R`, then `ℂ` is an algebraic closure of `R[v] ≅ MvPolynomial ι R`, so every ring
automorphism of the polynomial ring extends to `ℂ` (`exists_ringEquiv_aeval`).

* If `x` is transcendental over `ℚ`, put `x` into a transcendence basis over `ℚ` (which is
  uncountable, hence has a second element `c`) and swap `x` with `c`.
* If `x` is algebraic and irrational, its minimal polynomial has a second root `y` in the
  algebraic closure `L` of `ℚ` in `ℂ`; a `ℚ`-automorphism of `L` sends `x ↦ y`, and it acts on the
  coefficients of `MvPolynomial ι L` for a transcendence basis of `ℂ` over `L`.

## Main results

* `exists_ringHom_apply_ne` : an irrational complex number is moved by some `σ : ℂ →+* ℂ`.
* `exists_rat_eq_of_forall_ringHom` : a complex number fixed by every `σ : ℂ →+* ℂ` is rational.
-/

namespace VOA.Huang.AndersonMoore

open Polynomial

/-- Every ring automorphism of the polynomial ring on a transcendence basis of `ℂ` extends to a
ring automorphism of `ℂ`. -/
theorem exists_ringEquiv_aeval {R ι : Type*} [CommRing R] [IsDomain R] [Algebra R ℂ]
    {v : ι → ℂ} (hv : IsTranscendenceBasis R v)
    (φ : MvPolynomial ι R ≃+* MvPolynomial ι R) :
    ∃ σ : ℂ ≃+* ℂ, ∀ p, σ (MvPolynomial.aeval v p) = MvPolynomial.aeval v (φ p) := by
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let ψ : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range v) :=
    hv.1.aevalEquiv.symm.toRingEquiv.trans (φ.trans hv.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ ψ, fun p => ?_⟩
  rw [← hv.1.algebraMap_aevalEquiv, ← hv.1.algebraMap_aevalEquiv,
    IsAlgClosure.equivOfEquiv_algebraMap]
  simp [ψ]

/-- A transcendental complex number is moved by a ring automorphism of `ℂ`. -/
theorem exists_ringHom_apply_ne_of_transcendental {x : ℂ} (hx : Transcendental ℚ x) :
    ∃ σ : ℂ →+* ℂ, σ x ≠ x := by
  have hind : AlgebraicIndepOn ℚ id ({x} : Set ℂ) :=
    algebraicIndependent_unique_type_iff.mpr hx
  obtain ⟨B, hxB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hcard : Cardinal.mk ℂ = Cardinal.mk B :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hB
      (Cardinal.mk_le_aleph0) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  have hnt : Nontrivial B := by
    rw [← Cardinal.one_lt_iff_nontrivial, ← hcard, Cardinal.mk_complex]
    exact Cardinal.one_lt_aleph0.trans Cardinal.aleph0_lt_continuum
  let b : B := ⟨x, hxB rfl⟩
  obtain ⟨c, hc⟩ := exists_ne b
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_aeval hB
    (MvPolynomial.renameEquiv ℚ (Equiv.swap b c)).toRingEquiv
  refine ⟨σ, ?_⟩
  have h := hσ (MvPolynomial.X b)
  simp only [MvPolynomial.aeval_X, AlgEquiv.coe_ringEquiv,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_left] at h
  change σ x ≠ x
  rw [show x = (b : ℂ) from rfl, h]
  exact fun h' => hc (Subtype.ext h')

/-- An irrational algebraic complex number is moved by a ring automorphism of `ℂ`. -/
theorem exists_ringHom_apply_ne_of_isAlgebraic {x : ℂ} (hx : IsAlgebraic ℚ x)
    (hq : ∀ q : ℚ, (q : ℂ) ≠ x) : ∃ σ : ℂ →+* ℂ, σ x ≠ x := by
  let L := algebraicClosure ℚ ℂ
  haveI : Algebra.IsAlgebraic ℚ L := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : IsAlgClosure ℚ L := algebraicClosure.isAlgClosure ℚ ℂ
  have hxL : x ∈ L := mem_algebraicClosure_iff.mpr hx
  let x' : L := ⟨x, hxL⟩
  have hint : IsIntegral ℚ x' := Algebra.IsIntegral.isIntegral x'
  have hdeg : 2 ≤ (minpoly ℚ x').natDegree := by
    by_contra h
    have h1 : (minpoly ℚ x').natDegree = 1 :=
      le_antisymm (by omega) (minpoly.natDegree_pos hint)
    obtain ⟨q, hq'⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact hq q (by simpa [x'] using congrArg (Subtype.val) hq')
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed ℚ
  have hcard := card_rootSet_eq_natDegree (K := L) (minpoly.irreducible hint).separable
    (IsAlgClosed.splits _)
  have hx'mem : x' ∈ (minpoly ℚ x').rootSet L :=
    mem_rootSet.mpr ⟨minpoly.ne_zero hint, minpoly.aeval ℚ x'⟩
  obtain ⟨y', hy'⟩ := Fintype.exists_ne_of_one_lt_card
    (lt_of_lt_of_le one_lt_two (hcard ▸ hdeg)) (⟨x', hx'mem⟩ :
    (minpoly ℚ x').rootSet L)
  have hroot : aeval (y' : L) (minpoly ℚ x') = 0 := (mem_rootSet.mp y'.2).2
  have hK' : ∀ s : L, IsIntegral ℚ s ∧ ((minpoly ℚ s).map (algebraMap ℚ L)).Splits :=
    fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩
  obtain ⟨f, hf⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' hroot
  let τ : L ≃+* L := (AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f)).toRingEquiv
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis L ℂ
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_aeval hB (MvPolynomial.mapEquiv B τ)
  refine ⟨σ, ?_⟩
  have h := hσ (MvPolynomial.C x')
  simp only [MvPolynomial.aeval_C, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C] at h
  change σ x ≠ x
  rw [show x = algebraMap L ℂ x' from rfl, h]
  intro h'
  apply hy'
  apply Subtype.ext
  have : τ x' = x' := (algebraMap L ℂ).injective h'
  simpa [τ, hf] using this

/-- An irrational complex number is moved by some ring endomorphism (indeed automorphism)
of `ℂ`. -/
theorem exists_ringHom_apply_ne {x : ℂ} (hx : ∀ q : ℚ, (q : ℂ) ≠ x) :
    ∃ σ : ℂ →+* ℂ, σ x ≠ x := by
  by_cases h : IsAlgebraic ℚ x
  · exact exists_ringHom_apply_ne_of_isAlgebraic h hx
  · exact exists_ringHom_apply_ne_of_transcendental h

/-- A complex number fixed by every ring endomorphism of `ℂ` is rational. -/
theorem exists_rat_eq_of_forall_ringHom {x : ℂ} (h : ∀ σ : ℂ →+* ℂ, σ x = x) :
    ∃ q : ℚ, (q : ℂ) = x := by
  by_contra hq
  simp only [not_exists] at hq
  obtain ⟨σ, hσ⟩ := exists_ringHom_apply_ne hq
  exact hσ (h σ)

end VOA.Huang.AndersonMoore
