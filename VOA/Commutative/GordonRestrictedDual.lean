/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonParticleDiagonals
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The actual finite auxiliary quotient sector and its particle-polynomial dual

The sector is the span, inside the actual auxiliary arc quotient, of all products
with prescribed particle colors and total derivative degree. Its ordinary algebraic
dual injects into homogeneous separately symmetric particle polynomials. Thus the
functional model is proved from a genuine quotient, rather than specified as a field.
-/

namespace VOA.GordonRestrictedDual

open scoped BigOperators
open MvPolynomial VOA.BoundaryAuxiliary VOA.GordonFunctionalCoefficients
open VOA.GordonParticlePolynomial VOA.GordonParticleDiagonals

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A prescribed-color jet mode product in the actual auxiliary quotient. -/
def quotientMode (m : ℕ) (color : ι → Fin 3) (r : ι →₀ ℕ) : Auxiliary (R := K) m :=
  Ideal.Quotient.mk (auxiliaryIdeal (R := K) m) (∏ i, X (color i, r i))

/-- The fixed-particle, fixed-derivative sector of the actual quotient. -/
def sector (m D : ℕ) (color : ι → Fin 3) : Submodule K (Auxiliary (R := K) m) :=
  Submodule.span K (quotientMode m color '' (↑(degreeFiber (ι := ι) D) : Set (ι →₀ ℕ)))

instance sector_finite (m D : ℕ) (color : ι → Fin 3) :
    FiniteDimensional K (sector (K := K) m D color) :=
  FiniteDimensional.span_of_finite K
    ((degreeFiber (ι := ι) D).finite_toSet.image (quotientMode m color))

theorem quotientMode_mem_sector (m D : ℕ) (color : ι → Fin 3) (r : ι →₀ ℕ)
    (hr : r.degree = D) : quotientMode (K := K) m color r ∈ sector (K := K) m D color :=
  Submodule.subset_span ⟨r, (mem_degreeFiber D r).mpr hr, rfl⟩

/-- Extend a sector functional using a linear retraction. The resulting polynomial
is independent of that extension, because only prescribed-sector mode products occur. -/
def extendDual (m D : ℕ) (color : ι → Fin 3)
    (L : sector (K := K) m D color →ₗ[K] K) : Auxiliary (R := K) m →ₗ[K] K :=
  L.comp (sector (K := K) m D color).subtype.leftInverse

@[simp] theorem extendDual_apply_sector (m D : ℕ) (color : ι → Fin 3)
    (L : sector (K := K) m D color →ₗ[K] K) (x : sector (K := K) m D color) :
    extendDual m D color L x = L x := by
  unfold extendDual
  change L ((sector (K := K) m D color).subtype.leftInverse
    ((sector (K := K) m D color).subtype x)) = L x
  rw [LinearMap.leftInverse_apply_of_inj (sector (K := K) m D color).ker_subtype]

/-- The ordinary particle polynomial attached to a functional on the actual finite sector. -/
def particleMap (m D : ℕ) (color : ι → Fin 3) :
    (sector (K := K) m D color →ₗ[K] K) →ₗ[K] MvPolynomial ι K where
  toFun L := particlePolynomial D (pullbackDual m (extendDual m D color L)) color
  map_add' L M := by
    ext r
    simp only [coeff_particlePolynomial, coeff_add]
    split_ifs <;> simp [pullbackDual, extendDual]
  map_smul' c L := by
    ext r
    simp only [coeff_particlePolynomial, coeff_smul]
    split_ifs <;> simp [pullbackDual, extendDual]

/-- Exact ordinary coefficients of the realized dual polynomial. -/
theorem coeff_particleMap (m D : ℕ) (color : ι → Fin 3)
    (L : sector (K := K) m D color →ₗ[K] K) (r : ι →₀ ℕ) (hr : r.degree = D) :
    coeff r (particleMap (K := K) m D color L) =
      L ⟨quotientMode m color r, quotientMode_mem_sector m D color r hr⟩ := by
  change coeff r (particlePolynomial D _ color) = _
  rw [coeff_particlePolynomial, if_pos hr]
  change extendDual m D color L (quotientMode m color r) = _
  exact extendDual_apply_sector m D color L
    ⟨quotientMode m color r, quotientMode_mem_sector m D color r hr⟩

/-- No information from the actual finite-sector dual is lost in polynomial realization. -/
theorem particleMap_injective (m D : ℕ) (color : ι → Fin 3) :
    Function.Injective (particleMap (K := K) m D color) := by
  intro L M h
  have heq : Set.EqOn (extendDual m D color L) (extendDual m D color M)
      (quotientMode m color '' (↑(degreeFiber (ι := ι) D) : Set (ι →₀ ℕ))) := by
    rintro _ ⟨r, hr, rfl⟩
    have hc := congrArg (coeff r) h
    change coeff r (particlePolynomial D _ color) =
      coeff r (particlePolynomial D _ color) at hc
    simpa [coeff_particlePolynomial, (mem_degreeFiber D r).mp hr, pullbackDual,
      quotientMode] using hc
  ext x
  calc
    L x = extendDual m D color L x := (extendDual_apply_sector m D color L x).symm
    _ = extendDual m D color M x := LinearMap.eqOn_span heq x.property
    _ = M x := extendDual_apply_sector m D color M x

theorem particleMap_homogeneous (m D : ℕ) (color : ι → Fin 3)
    (L : sector (K := K) m D color →ₗ[K] K) :
    (particleMap (K := K) m D color L).IsHomogeneous D :=
  particlePolynomial_homogeneous _ _ _

theorem particleMap_rename (m D : ℕ) (color : ι → Fin 3)
    (L : sector (K := K) m D color →ₗ[K] K)
    (e : Equiv.Perm ι) (he : ∀ i, color (e i) = color i) :
    rename e (particleMap (K := K) m D color L) = particleMap (K := K) m D color L :=
  particlePolynomial_rename _ _ _ e he

/-- The actual functional model is the image of the proved injective polynomial realization. -/
def functionalModel (m D : ℕ) (color : ι → Fin 3) : Submodule K (MvPolynomial ι K) :=
  (particleMap (K := K) m D color).range

/-- The functional model and actual auxiliary sector have equal finite dimensions. -/
theorem finrank_functionalModel (m D : ℕ) (color : ι → Fin 3) :
    Module.finrank K (functionalModel (K := K) m D color) =
      Module.finrank K (sector (K := K) m D color) := by
  have h := (LinearEquiv.ofInjective (particleMap (K := K) m D color)
    (particleMap_injective m D color)).finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  exact h.symm

/-- Defining partial diagonals vanish for every polynomial in the actual functional model. -/
theorem functionalModel_relationDiagonal {α : Type*} [Fintype α] [DecidableEq α]
    (m D : ℕ) (a : α → Fin 3) (i : Fin 3)
    (F : MvPolynomial (α ⊕ RelationSlots m) K)
    (hF : F ∈ functionalModel m D (Sum.elim a (relationColor m i))) :
    relationDiagonalEval (α := α) m F = 0 := by
  obtain ⟨L, rfl⟩ := hF
  exact VOA.GordonParticleDiagonals.quotient_particlePolynomial_relationDiagonal _ _ _ _ _

end
end VOA.GordonRestrictedDual
