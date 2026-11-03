/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonRestrictedDual

/-! # Relabeling the genuine auxiliary quotient functional model -/

namespace VOA.GordonFunctionalRelabel
open MvPolynomial VOA.GordonRestrictedDual VOA.GordonParticlePolynomial
open VOA.GordonFunctionalCoefficients VOA.BoundaryAuxiliary

noncomputable section
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]

/-- Any functional on the actual quotient gives a polynomial in the restricted-dual model. -/
theorem particlePolynomial_mem_functionalModel (m D : ℕ) (color : ι → Fin 3)
    (L : Auxiliary (R := K) m →ₗ[K] K) :
    particlePolynomial D (pullbackDual m L) color ∈ functionalModel m D color := by
  refine ⟨L.comp (sector m D color).subtype, ?_⟩
  apply MvPolynomial.ext
  intro r
  by_cases hr : r.degree = D
  · rw [coeff_particleMap _ _ _ _ _ hr, coeff_particlePolynomial, if_pos hr]
    rfl
  · change coeff r (particlePolynomial D _ color) = _
    simp [coeff_particlePolynomial, hr]

/-- Color-preserving equivalences of particle labels transport the actual functional model. -/
theorem rename_mem_functionalModel (m D : ℕ) (color : ι → Fin 3) (other : κ → Fin 3)
    (e : ι ≃ κ) (he : ∀ i, other (e i) = color i)
    (F : MvPolynomial ι K) (hF : F ∈ functionalModel m D color) :
    rename e F ∈ functionalModel m D other := by
  obtain ⟨L, rfl⟩ := hF
  change rename e (particlePolynomial D _ color) ∈ _
  rw [particlePolynomial_rename_equiv D _ color other e he]
  exact particlePolynomial_mem_functionalModel m D other (extendDual m D color L)

/-- Relabeling is an equivalence of the actual finite functional-model spaces. -/
def functionalModelEquiv (m D : ℕ) (color : ι → Fin 3) (other : κ → Fin 3)
    (e : ι ≃ κ) (he : ∀ i, other (e i) = color i) :
    functionalModel (K := K) m D color ≃ₗ[K] functionalModel (K := K) m D other where
  toFun F := ⟨rename e F.val, rename_mem_functionalModel m D color other e he F.val F.property⟩
  invFun F := ⟨rename e.symm F.val, rename_mem_functionalModel m D other color e.symm
    (fun i ↦ by simpa using (he (e.symm i)).symm) F.val F.property⟩
  left_inv F := by apply Subtype.ext; simp [rename_rename]
  right_inv F := by apply Subtype.ext; simp [rename_rename]
  map_add' F G := by apply Subtype.ext; simp
  map_smul' c F := by apply Subtype.ext; simp

end
end VOA.GordonFunctionalRelabel
