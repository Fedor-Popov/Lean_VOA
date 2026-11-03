/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2NormalOrdering
import VOA.Examples.VirasoroUniversalPairing

/-!
# Actual affine vacuum-pairing polynomials at every word length

Normal ordering constructs a polynomial in the central level for each word.
Strictly negative creation words have positive energy, so their vacuum pairing
vanishes. In an actual normalized deformation the remaining central powers act
by the dual level k+δt. Thus both coordinates of the actual pairing are computed
by one polynomial, without a deformed invariant form or determinant assumption.
-/
namespace VOA.AffineVOA.NormalOrdering
open Module (End)
open VertexOperatorAlgebra Deform TrivSqZeroExt Polynomial
open VirDeformModes.NormalOrdering (vacuumPair vacuumPair_apply vacuumPair_scalar)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

/-- The energy of a negative current word is the sum of its positive creation
indices; colour does not affect energy, and index i denotes mode −i−1. -/
def creationEnergy : List (Fin 3 × ℕ) → ℕ
  | [] => 0
  | i::w => i.2 + 1 + creationEnergy w

/-- Actual lifted creation words have the same positive energy in both
coordinates. The correction term uses exactly the given gradedness of D. -/
theorem creationWord_grading (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (j : Fin 3 → V) (hj : ∀ a, j a ∈ W.grading 1) (w : List (Fin 3 × ℕ)) :
    (creationWord (fun a n => liftedMode D (j a) n) w (W.vacuum,0)).1 ∈
        W.grading (creationEnergy w) ∧
    (creationWord (fun a n => liftedMode D (j a) n) w (W.vacuum,0)).2 ∈
        W.grading (creationEnergy w) := by
  induction w with
  | nil => exact ⟨W.vacuum_mem, Submodule.zero_mem _⟩
  | cons i w ih =>
    let x := creationWord (fun a n => liftedMode D (j a) n) w (W.vacuum,0)
    have he : (1:ℤ) + creationEnergy w - (-(i.2:ℤ)-1) - 1 =
        creationEnergy (i::w) := by simp only [creationEnergy, Nat.cast_add, Nat.cast_one]; omega
    have h1 := W.smul_mem_grading (hj i.1) ih.1 (-(i.2:ℤ)-1)
    have h2 := W.smul_mem_grading (hj i.1) ih.2 (-(i.2:ℤ)-1)
    have hd := hD 1 (creationEnergy w) (j i.1) (hj i.1) x.1 ih.1 (-(i.2:ℤ)-1)
    rw [he] at h1 h2 hd
    exact ⟨h1, Submodule.add_mem _ hd h2⟩

/-- Every nonempty negative current word is invisible to the vacuum pairing
by ordinary graded orthogonality. The empty word pairs to one. -/
theorem vacuumPair_creation (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (j : Fin 3 → V) (hj : ∀ a, j a ∈ W.grading 1)
    (B : InvariantForm W) (hB : B.Normalized) (w : List (Fin 3 × ℕ)) :
    vacuumPair B (creationWord (fun a n => liftedMode D (j a) n) w (W.vacuum,0)) =
      if w=[] then 1 else 0 := by
  cases w with
  | nil =>
    change inl (B.form W.vacuum W.vacuum) + inr (B.form W.vacuum 0) = 1
    rw [hB, map_zero]
    simp
  | cons i w =>
    obtain ⟨h1,h2⟩ := creationWord_grading D hD j hj (i::w)
    have hn : (0:ℤ) ≠ (creationEnergy (i::w):ℤ) := by
      simp only [creationEnergy, Nat.cast_add, Nat.cast_one]; omega
    rw [vacuumPair_apply, B.orthogonal_of_ne hn W.vacuum_mem h1,
      B.orthogonal_of_ne hn W.vacuum_mem h2]
    simp

/-- Discard positive-energy creation terms and retain empty-word central
powers. This finite linear map constructs the vacuum polynomial. -/
noncomputable def centralPolynomial : NormalForm →ₗ[ℂ] Polynomial ℂ :=
  Finsupp.linearCombination ℂ (fun t => if t.2=[] then X^t.1 else 0)

/-- One polynomial for each finite affine current word, independent of the
representation or level at which it will be evaluated. -/
noncomputable def wordPolynomial (w : List (Fin 3 × ℤ)) : Polynomial ℂ :=
  centralPolynomial (wordNormal w)

/-- Evaluation and vacuum pairing commute with the polynomial construction
when the currents and central operator are the actual lifted ones. -/
theorem vacuumPair_evaluate (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (j : Fin 3 → V) (hj : ∀ a, j a ∈ W.grading 1)
    (B : InvariantForm W) (hB : B.Normalized)
    (A : AffineCentralCurrentData (V × V))
    (hA : SingularNorm.J A = fun a n => liftedMode D (j a) n)
    (z : DualNumber ℂ) (hK : A.central = dualScalarAction z) (f : NormalForm) :
    vacuumPair B (evaluate A (W.vacuum,0) f) = (centralPolynomial f).aeval z := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    rw [evaluate_single, map_smul]
    have hp : A.central^t.1 = dualScalarAction (z^t.1) := by rw [hK, map_pow]
    rw [hp, hA, vacuumPair_scalar, vacuumPair_creation D hD j hj B hB]
    simp only [centralPolynomial, Finsupp.linearCombination_single, map_smul]
    split_ifs <;> simp

/-- The full actual affine word-pairing bridge. Nonnegative lifted currents
kill the pure vacuum, so the proved uniform reduction applies at every length. -/
theorem vacuumPair_word (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (j : Fin 3 → V) (hj : ∀ a, j a ∈ W.grading 1)
    (B : InvariantForm W) (hB : B.Normalized)
    (A : AffineCentralCurrentData (V × V))
    (hA : SingularNorm.J A = fun a n => liftedMode D (j a) n)
    (z : DualNumber ℂ) (hK : A.central = dualScalarAction z) (w : List (Fin 3 × ℤ)) :
    vacuumPair B (currentWord (fun a n => liftedMode D (j a) n) w (W.vacuum,0)) =
      (wordPolynomial w).aeval z := by
  have hv (a : Fin 3) (n : ℤ) (hn : 0 ≤ n) : SingularNorm.J A a n (W.vacuum,0) = 0 := by
    rw [hA]; exact liftedMode_vacuum D n hn
  rw [← hA, ← evaluate_wordNormal A (W.vacuum,0) hv]
  exact vacuumPair_evaluate D hD j hj B hB A hA z hK _

/-- Concatenation of literal mode words agrees with operator multiplication. -/
theorem currentWord_append (j : Fin 3 → ℤ → End ℂ V)
    (u v : List (Fin 3 × ℤ)) : currentWord j (u++v) = currentWord j u * currentWord j v := by
  induction u with
  | nil => simp [currentWord]
  | cons an u ih => simp only [List.cons_append, currentWord, ih, mul_assoc]

end VOA.AffineVOA.NormalOrdering
