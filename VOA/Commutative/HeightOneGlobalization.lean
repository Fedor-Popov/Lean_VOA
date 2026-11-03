/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Height-one globalization over a noetherian UFD

The boundary-affine carrier is finite free over a polynomial ring.  Its globalization step can
therefore be reduced coordinatewise to the scalar fact that a noetherian UFD is the intersection
of its localizations at height-one primes inside its fraction field.

Mathlib contains this intersection theorem for all maximal primes of a domain and for height-one
primes of a Dedekind domain, but not in the higher-dimensional noetherian-UFD form needed here.
This file proves the scalar form directly from reduced fractions.  The finite-free module form is
developed below it.
-/

namespace VOA.HeightOneGlobalization

open Module
open scoped nonZeroDivisors
open scoped TensorProduct

noncomputable section

/-- A prime ideal of height exactly one.  Unlike
`IsDedekindDomain.HeightOneSpectrum`, this definition does not assume that the ambient ring has
Krull dimension one. -/
@[ext]
structure HeightOnePrime (R : Type*) [CommRing R] where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
  height_eq_one : asIdeal.height = 1

attribute [instance] HeightOnePrime.isPrime

variable {R K : Type*} [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- The localization at a height-one prime, viewed inside the fraction field. -/
def heightOneLocalization (v : HeightOnePrime R) : Subalgebra R K :=
  Localization.subalgebra.ofField K v.asIdeal.primeCompl
    v.asIdeal.primeCompl_le_nonZeroDivisors

/-- A rational scalar over a noetherian UFD which is regular at every height-one prime is
integral.  This is the scalar Hartogs/intersection input needed by the finite-free carrier. -/
theorem isInteger_of_mem_heightOneLocalizations
    [UniqueFactorizationMonoid R] [IsNoetherianRing R] {x : K}
    (hx : ∀ v : HeightOnePrime R, x ∈ heightOneLocalization (K := K) v) :
    IsLocalization.IsInteger R x := by
  rw [← IsFractionRing.isUnit_den_iff (A := R)]
  by_contra hden
  obtain ⟨p, hpIrreducible, hpDen⟩ :=
    WfDvdMonoid.exists_irreducible_factor hden
      (nonZeroDivisors.ne_zero (IsFractionRing.den R x).property)
  have hpPrime : Prime p :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hpIrreducible
  have hpNonzero : p ≠ 0 := hpPrime.ne_zero
  have hpNonunit : ¬ IsUnit p := hpPrime.not_unit
  have hspanPrime : (Ideal.span {p} : Ideal R).IsPrime :=
    (Ideal.span_singleton_prime hpNonzero).mpr hpPrime
  let v : HeightOnePrime R :=
    { asIdeal := Ideal.span {p}
      isPrime := hspanPrime
      height_eq_one := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hpNonzero) hpNonunit }
  have hxv := hx v
  change ∃ (a s : R) (_ : s ∈ v.asIdeal.primeCompl),
      x = algebraMap R K a * (algebraMap R K s)⁻¹ at hxv
  obtain ⟨a, s, hs, hxs⟩ := hxv
  have hsNonzero : s ≠ 0 := by
    intro hs0
    apply hs
    rw [hs0]
    exact v.asIdeal.zero_mem
  let s' : nonZeroDivisors R := ⟨s, mem_nonZeroDivisors_iff_ne_zero.mpr hsNonzero⟩
  have hfrac :
      IsLocalization.mk' K (IsFractionRing.num R x) (IsFractionRing.den R x) =
        IsLocalization.mk' K a s' := by
    rw [IsFractionRing.mk'_num_den]
    rw [IsFractionRing.mk'_eq_div]
    simpa [div_eq_mul_inv, s'] using hxs
  have hcrossMap :
      algebraMap R K (IsFractionRing.num R x * s) =
        algebraMap R K (a * (IsFractionRing.den R x : R)) := by
    simpa [s'] using (IsLocalization.mk'_eq_iff_eq' (S := K)).mp hfrac
  have hcross :
      IsFractionRing.num R x * s = a * (IsFractionRing.den R x : R) :=
    (FaithfulSMul.algebraMap_injective R K) hcrossMap
  have hpMul : p ∣ IsFractionRing.num R x * s := by
    rw [hcross]
    exact dvd_mul_of_dvd_right hpDen a
  rcases hpPrime.dvd_mul.mp hpMul with hpNum | hpS
  · exact hpNonunit
      (((IsFractionRing.num_den_reduced R x).of_dvd_left hpNum).isUnit_of_dvd hpDen)
  · apply hs
    change s ∈ Ideal.span {p}
    exact Ideal.mem_span_singleton.mpr hpS

/-- A noetherian UFD is the intersection of its height-one localizations inside its fraction
field.  Here `bot` is the image of the base ring in the fraction field. -/
theorem iInf_heightOneLocalization_eq_bot
    [UniqueFactorizationMonoid R] [IsNoetherianRing R] :
    (⨅ v : HeightOnePrime R, heightOneLocalization (K := K) v) = ⊥ := by
  ext x
  rw [Algebra.mem_iInf, Algebra.mem_bot]
  constructor
  · intro hx
    exact isInteger_of_mem_heightOneLocalizations hx
  · rintro ⟨r, rfl⟩ v
    exact (heightOneLocalization (K := K) v).algebraMap_mem r

section CoordinateLattices

variable {ι V : Type*}

/-- Finitely supported vectors whose every coordinate lies in a prescribed scalar lattice. -/
def coordinateLattice (S : Submodule R K) : Submodule R (ι →₀ K) where
  carrier := {x | ∀ i, x i ∈ S}
  zero_mem' := fun _ => S.zero_mem
  add_mem' := fun hx hy i => S.add_mem (hx i) (hy i)
  smul_mem' := fun r x hx i => by
    rw [Finsupp.smul_apply]
    exact S.smul_mem r (hx i)

@[simp]
theorem mem_coordinateLattice {S : Submodule R K} {x : ι →₀ K} :
    x ∈ coordinateLattice S ↔ ∀ i, x i ∈ S :=
  Iff.rfl

/-- The integral coordinate lattice inside finitely supported vectors over the fraction field. -/
def integralCoordinateLattice : Submodule R (ι →₀ K) :=
  coordinateLattice (R := R) (Subalgebra.toSubmodule (⊥ : Subalgebra R K))

/-- The coordinate lattice obtained by allowing denominators outside one height-one prime. -/
def heightOneCoordinateLattice (v : HeightOnePrime R) : Submodule R (ι →₀ K) :=
  coordinateLattice (R := R) (heightOneLocalization (K := K) v).toSubmodule

/-- Finite-free globalization in coordinates: a rational vector which belongs to the localized
lattice at every height-one prime already has integral coordinates.  The index type need not be
finite; finite support is built into `Finsupp`. -/
theorem mem_integralCoordinateLattice_of_mem_heightOne
    [UniqueFactorizationMonoid R] [IsNoetherianRing R] {x : ι →₀ K}
    (hx : ∀ v : HeightOnePrime R, x ∈ heightOneCoordinateLattice (ι := ι) (K := K) v) :
    x ∈ integralCoordinateLattice (R := R) (ι := ι) (K := K) := by
  intro i
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot]
  exact isInteger_of_mem_heightOneLocalizations (R := R) (K := K) fun v => hx v i

/-- The integral coordinate lattice is exactly the intersection of its height-one localized
lattices. -/
theorem iInf_heightOneCoordinateLattice_eq_integral
    [UniqueFactorizationMonoid R] [IsNoetherianRing R] :
    (⨅ v : HeightOnePrime R, heightOneCoordinateLattice (ι := ι) (K := K) v) =
      integralCoordinateLattice (R := R) (ι := ι) (K := K) := by
  apply le_antisymm
  · intro x hx
    exact mem_integralCoordinateLattice_of_mem_heightOne fun v =>
      (Submodule.mem_iInf _).mp hx v
  · intro x hx
    apply (Submodule.mem_iInf _).mpr
    intro v i
    change ∀ i, x i ∈ Subalgebra.toSubmodule (⊥ : Subalgebra R K) at hx
    have hxi := hx i
    rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hxi
    obtain ⟨r, hr⟩ := hxi
    rw [← hr]
    exact (heightOneLocalization (K := K) v).algebraMap_mem r

/-- Pull the integral coordinate lattice back along a chosen rational coordinate equivalence.
For a finite-free module, this equivalence is supplied by a basis after extension to the fraction
field. -/
def pulledBackIntegralLattice [AddCommMonoid V] [Module R V]
    (coordinates : V ≃ₗ[R] ι →₀ K) : Submodule R V :=
  (integralCoordinateLattice (R := R) (ι := ι) (K := K)).comap coordinates.toLinearMap

/-- Pull the height-one localized coordinate lattice back along the same rational coordinate
equivalence. -/
def pulledBackHeightOneLattice [AddCommMonoid V] [Module R V]
    (coordinates : V ≃ₗ[R] ι →₀ K) (v : HeightOnePrime R) : Submodule R V :=
  (heightOneCoordinateLattice (ι := ι) (K := K) v).comap coordinates.toLinearMap

/-- Basis-independent wrapper for finite-free globalization.  Once a rational ambient module is
identified with finitely supported fraction-field coordinates, membership in the pulled-back
integral lattice is detected at all height-one primes. -/
theorem mem_pulledBackIntegralLattice_of_mem_heightOne
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    [AddCommMonoid V] [Module R V] (coordinates : V ≃ₗ[R] ι →₀ K) {x : V}
    (hx : ∀ v : HeightOnePrime R,
      x ∈ pulledBackHeightOneLattice coordinates v) :
    x ∈ pulledBackIntegralLattice coordinates := by
  change coordinates x ∈ integralCoordinateLattice (R := R) (ι := ι) (K := K)
  apply mem_integralCoordinateLattice_of_mem_heightOne
  intro v
  change coordinates x ∈ heightOneCoordinateLattice (ι := ι) (K := K) v
  exact hx v

/-- The pulled-back integral lattice is the intersection of all pulled-back height-one lattices. -/
theorem iInf_pulledBackHeightOneLattice_eq_integral
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    [AddCommMonoid V] [Module R V] (coordinates : V ≃ₗ[R] ι →₀ K) :
    (⨅ v : HeightOnePrime R, pulledBackHeightOneLattice coordinates v) =
      pulledBackIntegralLattice coordinates := by
  apply le_antisymm
  · intro x hx
    exact mem_pulledBackIntegralLattice_of_mem_heightOne coordinates fun v =>
      (Submodule.mem_iInf _).mp hx v
  · intro x hx
    apply (Submodule.mem_iInf _).mpr
    intro v
    change coordinates x ∈ heightOneCoordinateLattice (ι := ι) (K := K) v
    change coordinates x ∈ integralCoordinateLattice (R := R) (ι := ι) (K := K) at hx
    rw [← iInf_heightOneCoordinateLattice_eq_integral (ι := ι) (K := K)] at hx
    exact (Submodule.mem_iInf _).mp hx v

section BasisForm

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Fraction-field coordinates on the scalar extension of a free module. -/
def fractionCoordinates (basis : Basis ι R M) :
    K ⊗[R] M ≃ₗ[R] ι →₀ K := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight basis

/-- The original free lattice inside its fraction-field scalar extension, expressed in a chosen
basis.  This is the target lattice used in the carrier globalization argument. -/
def basisFractionIntegralLattice (basis : Basis ι R M) : Submodule R (K ⊗[R] M) :=
  pulledBackIntegralLattice (fractionCoordinates (K := K) basis)

/-- The localization of a free lattice at one height-one prime, inside its fraction-field scalar
extension. -/
def basisFractionHeightOneLattice (basis : Basis ι R M) (v : HeightOnePrime R) :
    Submodule R (K ⊗[R] M) :=
  pulledBackHeightOneLattice (fractionCoordinates (K := K) basis) v

/-- Honest finite-free height-one globalization: a rational section of the scalar extension of a
free module lies in the original lattice if it lies in the localized lattice at every
height-one prime. -/
theorem mem_basisFractionIntegralLattice_of_mem_heightOne
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (basis : Basis ι R M) {x : K ⊗[R] M}
    (hx : ∀ v : HeightOnePrime R, x ∈ basisFractionHeightOneLattice (K := K) basis v) :
    x ∈ basisFractionIntegralLattice (K := K) basis :=
  mem_pulledBackIntegralLattice_of_mem_heightOne
    (fractionCoordinates (K := K) basis) hx

/-- The free lattice is exactly the intersection of its height-one localizations inside the
fraction-field scalar extension. -/
theorem iInf_basisFractionHeightOneLattice_eq_integral
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (basis : Basis ι R M) :
    (⨅ v : HeightOnePrime R, basisFractionHeightOneLattice (K := K) basis v) =
      basisFractionIntegralLattice (K := K) basis :=
  iInf_pulledBackHeightOneLattice_eq_integral
    (fractionCoordinates (K := K) basis)

end BasisForm

end CoordinateLattices

end

end VOA.HeightOneGlobalization
