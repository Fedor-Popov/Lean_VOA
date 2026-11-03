/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonRestrictedDual
import VOA.Commutative.GordonCommonFactors

/-! # Selected relation particles and block-residual collision factors -/

namespace VOA.GordonSelectedDiagonals

open scoped BigOperators
open MvPolynomial VOA.BoundaryAuxiliary VOA.GordonFunctionalCoefficients
open VOA.GordonParticlePolynomial VOA.GordonParticleDiagonals VOA.GordonRestrictedDual
open VOA.GordonCommonFactors

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Spectators left after selecting the particles of one actual auxiliary relation. -/
abbrev Spectators {m : ℕ} (g : RelationSlots m ↪ ι) := {j : ι // j ∉ Set.range g}

/-- Put all spectators first and the selected relation particles last. -/
def selectedEquiv {m : ℕ} (g : RelationSlots m ↪ ι) :
    Spectators g ⊕ RelationSlots m ≃ ι :=
  Equiv.ofBijective (Sum.elim Subtype.val g) (by
    constructor
    · rintro (x | x) (y | y) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact False.elim (x.property ⟨y, h.symm⟩)
      · exact False.elim (y.property ⟨x, h⟩)
      · exact congrArg Sum.inr (g.injective h)
    · intro j
      by_cases hj : j ∈ Set.range g
      · obtain ⟨i, rfl⟩ := hj
        exact ⟨Sum.inr i, rfl⟩
      · exact ⟨Sum.inl ⟨j, hj⟩, rfl⟩)

/-- Literal quotient-dual polynomials vanish whenever any correctly colored copy
of the relation particles is assigned one common coordinate. -/
theorem quotient_particlePolynomial_selected_vanish
    {A : Type*} [CommRing A] [Algebra K A]
    (m D : ℕ) (color : ι → Fin 3) (L : Auxiliary (R := K) m →ₗ[K] K)
    (i : Fin 3) (g : RelationSlots m ↪ ι)
    (hcolor : ∀ j, color (g j) = relationColor m i j)
    (assignment : ι → A) (t : A) (hcommon : ∀ j, assignment (g j) = t) :
    aeval assignment (particlePolynomial D (pullbackDual m L) color) = 0 := by
  let a : Spectators g → Fin 3 := fun j ↦ color j.val
  let c := Sum.elim a (relationColor m i)
  have hc : ∀ j, color (selectedEquiv g j) = c j := by
    rintro (j | j)
    · rfl
    · exact hcolor j
  have heq := particlePolynomial_rename_equiv D (pullbackDual m L)
    c color (selectedEquiv g) hc
  rw [← heq, aeval_rename]
  have hass : assignment ∘ selectedEquiv g =
      Sum.elim (fun j : Spectators g ↦ assignment j.val) (fun _ : RelationSlots m ↦ t) := by
    funext j
    rcases j with j | j
    · rfl
    · exact hcommon j
  rw [hass]
  exact eval_eq_zero_of_relationDiagonal m _
    (VOA.GordonParticleDiagonals.quotient_particlePolynomial_relationDiagonal m D L a i) _ _

/-- Selected relation coincidences vanish in the actual finite functional model. -/
theorem functionalModel_selected_vanish {A : Type*} [CommRing A] [Algebra K A]
    (m D : ℕ) (color : ι → Fin 3) (F : MvPolynomial ι K)
    (hF : F ∈ functionalModel m D color) (i : Fin 3) (g : RelationSlots m ↪ ι)
    (hcolor : ∀ j, color (g j) = relationColor m i j)
    (assignment : ι → A) (t : A) (hcommon : ∀ j, assignment (g j) = t) :
    aeval assignment F = 0 := by
  obtain ⟨L, rfl⟩ := hF
  exact quotient_particlePolynomial_selected_vanish m D color _ i g hcolor assignment t hcommon

/-- A block containing the e/f pairs of a size-`m` relation acquires a linear factor
against its distinguished residual particle. This is derived from actual quotient relations. -/
theorem block_residual_factor {τ : Type*} [DecidableEq τ]
    (m D : ℕ) (color : ι → Fin 3) (F : MvPolynomial ι K)
    (hF : F ∈ functionalModel m D color) (f : ι → τ) (u v : τ) (hvu : v ≠ u)
    (i : Fin 3) (g : RelationSlots m ↪ ι)
    (hcolor : ∀ j, color (g j) = relationColor m i j)
    (hresidual : f (g (Sum.inl ())) = v)
    (hpairs : ∀ j : Fin m ⊕ Fin m, f (g (Sum.inr j)) = u) :
    (X u - X v : MvPolynomial τ K) ∣ rename f F := by
  apply (collisionFactor_dvd_iff u v hvu _).mpr
  have hvan := functionalModel_selected_vanish
    (A := MvPolynomial {j : τ // j ≠ u} K) m D color F hF i g hcolor
    (fun j ↦ X (collisionIndex u v hvu (f j))) (X ⟨v, hvu⟩) ?_
  · have heq : (collisionMap (K := K) u v hvu).comp (rename f) =
        aeval (fun j ↦ X (collisionIndex u v hvu (f j))) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [collisionMap]
    exact (DFunLike.congr_fun heq F).trans hvan
  · rintro (j | j)
    · cases j
      simp only [hresidual, collisionIndex_other u v hvu v hvu]
    · simp only [hpairs, collisionIndex_self]

end
end VOA.GordonSelectedDiagonals
