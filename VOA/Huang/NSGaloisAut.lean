/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Automorphisms of `ℂ` acting on roots of unity by a power

`exists_ringEquiv_pow_of_isCoprime`: for `N > 0` and `x` coprime to `N` there is a field
automorphism `σ` of `ℂ` with `σ z = z ^ x` for every `N`-th root of unity `z`.

Proof: the algebraic numbers `Q̄ = algebraicClosure ℚ ℂ` are normal over `ℚ`; `ζ_N` and `ζ_N^x`
have the same minimal polynomial (the cyclotomic polynomial), so some `g ∈ Gal(Q̄/ℚ)` sends one
to the other (`Normal.minpoly_eq_iff_mem_orbit`).  `g` extends to `ℂ` through a transcendence
basis of `ℂ` over `Q̄` (as in Mathlib's `IsAlgClosed.equivOfTranscendenceBasis`).
-/

noncomputable section

namespace VOA.Huang.NSGalois

open Polynomial IntermediateField

/-- The algebraic numbers inside `ℂ`. -/
abbrev QBar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- Every automorphism of the algebraic numbers in `ℂ` extends to a field automorphism of `ℂ`. -/
theorem exists_ringEquiv_extend (g : QBar ≃ₐ[ℚ] QBar) :
    ∃ σ : ℂ ≃+* ℂ, ∀ q : QBar, σ (q : ℂ) = (g q : ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis QBar ℂ
  let v : s → ℂ := (↑)
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let A := Algebra.adjoin QBar (Set.range v)
  let e : A ≃+* A :=
    hs.1.aevalEquiv.symm.toRingEquiv.trans
      ((MvPolynomial.mapEquiv s g.toRingEquiv).trans hs.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun q => ?_⟩
  have h1 : ((q : QBar) : ℂ) = algebraMap A ℂ (algebraMap QBar A q) := rfl
  rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
  have h2 : e (algebraMap QBar A q) = algebraMap QBar A (g q) := by
    change hs.1.aevalEquiv (MvPolynomial.mapEquiv s g.toRingEquiv
      (hs.1.aevalEquiv.symm (algebraMap QBar A q))) = _
    rw [AlgEquiv.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply,
      MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  rw [h2]
  rfl

/-- **An automorphism of `ℂ` acting as `z ↦ z^x` on `N`-th roots of unity**, for `x` coprime
to `N`. -/
theorem exists_ringEquiv_pow (N : ℕ) (hN : 0 < N) (x : ℤ) (hx : x.gcd N = 1) :
    ∃ σ : ℂ ≃+* ℂ, ∀ z : ℂ, z ^ N = 1 → σ z = z ^ x := by
  haveI : NeZero N := ⟨hN.ne'⟩
  set ζ := Complex.exp (2 * Real.pi * Complex.I / N) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hmem : ζ ∈ QBar := by
    rw [mem_algebraicClosure_iff]
    exact ((hζ.isIntegral hN).tower_top (A := ℚ)).isAlgebraic
  let ζ' : QBar := ⟨ζ, hmem⟩
  have hζ' : IsPrimitiveRoot ζ' N :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap QBar ℂ) hζ
      (FaithfulSMul.algebraMap_injective _ _)
  have hζx : IsPrimitiveRoot (ζ' ^ x) N := hζ'.zpow_of_gcd_eq_one x hx
  have hmin : minpoly ℚ (ζ' ^ x) = minpoly ℚ ζ' := by
    rw [← cyclotomic_eq_minpoly_rat hζ' hN, ← cyclotomic_eq_minpoly_rat hζx hN]
  haveI : IsAlgClosure ℚ QBar := algebraicClosure.isAlgClosure ℚ ℂ
  haveI : Normal ℚ QBar := IsAlgClosure.normal ℚ QBar
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := QBar)).mp hmin
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend g
  have hσζ : σ ζ = ζ ^ x := by
    have h := hσ ζ'
    change σ ζ = _ at h
    rw [h]
    have hg' : g ζ' = ζ' ^ x := hg
    rw [hg']
    push_cast
    rfl
  refine ⟨σ, fun z hz => ?_⟩
  obtain ⟨m, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, hσζ, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

end VOA.Huang.NSGalois
