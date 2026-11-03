/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BoundaryCollisionDivisibility
import VOA.Commutative.P3FunctionalModel

/-!
# Boundary/current root-label plumbing for the `p = 3` sector

This file contains only the finite type equivalences needed to identify a four-species boundary
label with a current label or an `S` label.  It makes no assertion about polynomial carriers,
freeness, or common factors.
-/

namespace VOA.P3BoundaryRootEquiv

open VOA.P3FunctionalModel
open VOA.MultispeciesParticlePolynomial
open VOA.RootedMatching

noncomputable section

/-- Current multiplicities `(a,b,c)` in the order `X,Y,Z`. -/
def p3CurrentMultiplicity (a b c : ℕ) : CurrentSpecies → ℕ
  | .X => a
  | .Y => b
  | .Z => c

@[simp] theorem p3CurrentMultiplicity_X (a b c : ℕ) :
    p3CurrentMultiplicity a b c .X = a := rfl

@[simp] theorem p3CurrentMultiplicity_Y (a b c : ℕ) :
    p3CurrentMultiplicity a b c .Y = b := rfl

@[simp] theorem p3CurrentMultiplicity_Z (a b c : ℕ) :
    p3CurrentMultiplicity a b c .Z = c := rfl

/-- Flatten a boundary label into its current label or its `S` root coordinate. -/
def p3BoundaryRootEquiv (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity a b c d) ≃
      Root (CurrentLabels (p3CurrentMultiplicity a b c)) (Fin d) where
  toFun
    | ⟨.X, i⟩ => .inl ⟨.X, i⟩
    | ⟨.Y, i⟩ => .inl ⟨.Y, i⟩
    | ⟨.Z, i⟩ => .inl ⟨.Z, i⟩
    | ⟨.S, i⟩ => .inr i
  invFun
    | .inl ⟨.X, i⟩ => ⟨.X, i⟩
    | .inl ⟨.Y, i⟩ => ⟨.Y, i⟩
    | .inl ⟨.Z, i⟩ => ⟨.Z, i⟩
    | .inr i => ⟨.S, i⟩
  left_inv x := by
    rcases x with ⟨A, i⟩
    cases A <;> rfl
  right_inv x := by
    rcases x with (⟨A, i⟩ | i)
    · cases A <;> rfl
    · rfl

@[simp] theorem p3BoundaryRootEquiv_X (a b c d : ℕ) (i : Fin a) :
    p3BoundaryRootEquiv a b c d
        (⟨BoundarySpecies.X, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) =
      .inl (⟨CurrentSpecies.X, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c)) := rfl

@[simp] theorem p3BoundaryRootEquiv_Y (a b c d : ℕ) (i : Fin b) :
    p3BoundaryRootEquiv a b c d
        (⟨BoundarySpecies.Y, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) =
      .inl (⟨CurrentSpecies.Y, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c)) := rfl

@[simp] theorem p3BoundaryRootEquiv_Z (a b c d : ℕ) (i : Fin c) :
    p3BoundaryRootEquiv a b c d
        (⟨BoundarySpecies.Z, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) =
      .inl (⟨CurrentSpecies.Z, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c)) := rfl

@[simp] theorem p3BoundaryRootEquiv_S (a b c d : ℕ) (i : Fin d) :
    p3BoundaryRootEquiv a b c d
        (⟨BoundarySpecies.S, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) =
      .inr i := rfl

@[simp] theorem p3BoundaryRootEquiv_symm_X (a b c d : ℕ) (i : Fin a) :
    (p3BoundaryRootEquiv a b c d).symm
        (.inl (⟨CurrentSpecies.X, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c))) =
      (⟨BoundarySpecies.X, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) := rfl

@[simp] theorem p3BoundaryRootEquiv_symm_Y (a b c d : ℕ) (i : Fin b) :
    (p3BoundaryRootEquiv a b c d).symm
        (.inl (⟨CurrentSpecies.Y, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c))) =
      (⟨BoundarySpecies.Y, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) := rfl

@[simp] theorem p3BoundaryRootEquiv_symm_Z (a b c d : ℕ) (i : Fin c) :
    (p3BoundaryRootEquiv a b c d).symm
        (.inl (⟨CurrentSpecies.Z, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c))) =
      (⟨BoundarySpecies.Z, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) := rfl

@[simp] theorem p3BoundaryRootEquiv_symm_S (a b c d : ℕ) (i : Fin d) :
    (p3BoundaryRootEquiv a b c d).symm (.inr i) =
      (⟨BoundarySpecies.S, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) := rfl

private def p3BoundaryLabelFiberEquiv (a b c d : ℕ) (A : BoundarySpecies) :
    Fin (boundaryMultiplicity a b c d A) ≃
      {i : SpeciesLabel (boundaryMultiplicity a b c d) // i.1 = A} where
  toFun i := ⟨⟨A, i⟩, rfl⟩
  invFun i := by
    rcases i with ⟨⟨B, j⟩, h⟩
    cases h
    exact j
  left_inv i := rfl
  right_inv i := by
    rcases i with ⟨⟨B, j⟩, h⟩
    cases h
    rfl

/-- The boundary permutation obtained by conjugating a source permutation through the root-label
equivalence. -/
def p3BoundaryLabelPermutation (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d) (currentSpecies (p3CurrentMultiplicity a b c))) :
    Equiv.Perm (SpeciesLabel (boundaryMultiplicity a b c d)) :=
  (p3BoundaryRootEquiv a b c d).trans
    ((g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c))).trans
      (p3BoundaryRootEquiv a b c d).symm)

theorem p3BoundaryLabelPermutation_apply (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d) (currentSpecies (p3CurrentMultiplicity a b c)))
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    p3BoundaryLabelPermutation a b c d g i =
      (p3BoundaryRootEquiv a b c d).symm
        (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c))
          (p3BoundaryRootEquiv a b c d i)) := rfl

theorem p3BoundaryLabelPermutation_preserves_species (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d) (currentSpecies (p3CurrentMultiplicity a b c)))
    (A : BoundarySpecies) (i : Fin (boundaryMultiplicity a b c d A)) :
    (p3BoundaryLabelPermutation a b c d g
      (⟨A, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d))).1 = A := by
  cases A with
  | X =>
      have h := g.1.2 (⟨CurrentSpecies.X, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c))
      cases hg : g.1.1 (⟨CurrentSpecies.X, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c)) with
      | mk B j =>
          have hB : B = CurrentSpecies.X := by simpa [currentSpecies, hg] using h
          subst B
          simp [p3BoundaryLabelPermutation, p3BoundaryRootEquiv, hg]
  | Y =>
      have h := g.1.2 (⟨CurrentSpecies.Y, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c))
      cases hg : g.1.1 (⟨CurrentSpecies.Y, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c)) with
      | mk B j =>
          have hB : B = CurrentSpecies.Y := by simpa [currentSpecies, hg] using h
          subst B
          simp [p3BoundaryLabelPermutation, p3BoundaryRootEquiv, hg]
  | Z =>
      have h := g.1.2 (⟨CurrentSpecies.Z, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c))
      cases hg : g.1.1 (⟨CurrentSpecies.Z, i⟩ : CurrentLabels (p3CurrentMultiplicity a b c)) with
      | mk B j =>
          have hB : B = CurrentSpecies.Z := by simpa [currentSpecies, hg] using h
          subst B
          simp [p3BoundaryLabelPermutation, p3BoundaryRootEquiv, hg]
  | S =>
      simp [p3BoundaryLabelPermutation, p3BoundaryRootEquiv]

theorem p3BoundaryLabelPermutation_fiber (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d) (currentSpecies (p3CurrentMultiplicity a b c)))
    (A : BoundarySpecies) :
    ∀ i : SpeciesLabel (boundaryMultiplicity a b c d),
      i.1 = A ↔
        (p3BoundaryLabelPermutation a b c d g i).1 = A := by
  intro i
  constructor
  · intro hi
    rcases i with ⟨B, j⟩
    cases hi
    exact p3BoundaryLabelPermutation_preserves_species a b c d g B j
  · intro hi
    rcases i with ⟨B, j⟩
    have hB := p3BoundaryLabelPermutation_preserves_species a b c d g B j
    exact hB.symm.trans hi

/-- Specieswise form of a source relabeling on the boundary label type. -/
def p3BoundarySpeciesPermutation (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d) (currentSpecies (p3CurrentMultiplicity a b c))) :
    SpeciesPermutation (boundaryMultiplicity a b c d) :=
  fun A =>
    (p3BoundaryLabelFiberEquiv a b c d A).trans
      ((Equiv.subtypeEquiv
        (p3BoundaryLabelPermutation a b c d g)
        (p3BoundaryLabelPermutation_fiber a b c d g A)).trans
        (p3BoundaryLabelFiberEquiv a b c d A).symm)

theorem p3BoundarySpeciesPermutation_label (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d) (currentSpecies (p3CurrentMultiplicity a b c)))
    (A : BoundarySpecies) (i : Fin (boundaryMultiplicity a b c d A)) :
    (⟨A, p3BoundarySpeciesPermutation a b c d g A i⟩ :
      SpeciesLabel (boundaryMultiplicity a b c d)) =
      p3BoundaryLabelPermutation a b c d g
        (⟨A, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) := by
  have hsub :
      (p3BoundaryLabelFiberEquiv a b c d A)
          (p3BoundarySpeciesPermutation a b c d g A i) =
        (Equiv.subtypeEquiv
          (p3BoundaryLabelPermutation a b c d g)
          (p3BoundaryLabelPermutation_fiber a b c d g A))
          (p3BoundaryLabelFiberEquiv a b c d A i) := by
    simpa only [p3BoundarySpeciesPermutation, Equiv.trans_apply] using
      (p3BoundaryLabelFiberEquiv a b c d A).apply_symm_apply
        ((Equiv.subtypeEquiv
          (p3BoundaryLabelPermutation a b c d g)
          (p3BoundaryLabelPermutation_fiber a b c d g A))
          (p3BoundaryLabelFiberEquiv a b c d A i))
  simpa [p3BoundarySpeciesPermutation, p3BoundaryLabelFiberEquiv] using
    congrArg Subtype.val hsub

theorem p3BoundarySpeciesPermutation_naturality (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d) (currentSpecies (p3CurrentMultiplicity a b c)))
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    p3BoundaryRootEquiv a b c d
        (speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g) i) =
      g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c))
        (p3BoundaryRootEquiv a b c d i) := by
  rcases i with ⟨A, i⟩
  simp only [speciesLabelEquiv]
  change p3BoundaryRootEquiv a b c d
      (⟨A, p3BoundarySpeciesPermutation a b c d g A i⟩ :
        SpeciesLabel (boundaryMultiplicity a b c d)) = _
  rw [p3BoundarySpeciesPermutation_label]
  change p3BoundaryRootEquiv a b c d
      ((p3BoundaryRootEquiv a b c d).symm
        (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c))
          (p3BoundaryRootEquiv a b c d ⟨A, i⟩))) = _
  exact (p3BoundaryRootEquiv a b c d).apply_symm_apply _

end

end VOA.P3BoundaryRootEquiv
