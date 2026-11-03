/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroRigidityTangent
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# From a lifted Gram-kernel relation to the scalar rigidity obstruction

The canonical level-four and level-six Gram matrices have polynomial entries.
This file packages those very entries over ℂ[X], verifies their agreement with
the existing complex Gram matrices, and evaluates them over the dual numbers.
A kernel relation with at least one nonzero constant coefficient then forces
the determinant to vanish: that coefficient is a unit, and the adjugate identity
annihilates the determinant. The simple-root tests proved earlier force zero
central-charge motion at Lee–Yang, Ising, and M(2,7).

Ordinary relations in a finite spanning family lift through arbitrary
first-order changes of its states; applying first-order linear functionals gives
a Gram-kernel vector with its nonzero constant coefficient preserved. The actual VOA-to-polynomial bridge is proved at arbitrary levels in
VirasoroUniversalPairing. VirasoroDeterminantObstruction uses the spanning
argument here to prove actual determinant preservation and a general simple-root
rigidity criterion. The uniform minimal-model determinant/root theorem remains open. A merely nonzero dual-number kernel vector does not
suffice: it might consist entirely of nilpotent coefficients.
-/
namespace VOA.VirRigidGramLift
open Polynomial TrivSqZeroExt VirRigidTangent VirGram56 LeeYang
open scoped Matrix

/-- The canonical weight-four Gram matrix as a polynomial matrix. Its ordered
states are the two weight-four vacuum descendants used by `VirGram4.canGram4`. -/
noncomputable def gram4Polynomial : Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  !![Polynomial.C (1 / 2) * X * (X + Polynomial.C 8), Polynomial.C 3 * X;
     Polynomial.C 3 * X, Polynomial.C 5 * X]

/-- The canonical weight-six Gram matrix as a polynomial matrix, in the order
L₋₆1, L₋₄L₋₂1, L₋₃²1, L₋₂³1. Constants are complex polynomial coefficients. -/
noncomputable def gram6Polynomial : Matrix (Fin 4) (Fin 4) (Polynomial ℂ) :=
  !![Polynomial.C (35 / 2) * X, Polynomial.C 5 * X, Polynomial.C 18 * X, Polynomial.C 24 * X;
     Polynomial.C 5 * X, Polynomial.C (1 / 2) * (Polynomial.C 5 * X ^ 2 + Polynomial.C 16 * X), Polynomial.C 14 * X,
       Polynomial.C (1 / 2) * (Polynomial.C 9 * X ^ 2 + Polynomial.C 48 * X);
     Polynomial.C 18 * X, Polynomial.C 14 * X, Polynomial.C 8 * X ^ 2 + Polynomial.C 36 * X, Polynomial.C 30 * X;
     Polynomial.C 24 * X, Polynomial.C (1 / 2) * (Polynomial.C 9 * X ^ 2 + Polynomial.C 48 * X), Polynomial.C 30 * X,
       Polynomial.C (3 / 4) * X * (X + Polynomial.C 8) * (X + Polynomial.C 16)]

/-- Evaluation recovers the already constructed canonical level-four Gram matrix. -/
theorem gram4Polynomial_eval (c : ℂ) :
    (evalRingHom c).mapMatrix gram4Polynomial = VirGram4.canGram4 c := by
  rw [VirGram4.canGram4_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram4Polynomial] <;> ring

/-- Evaluation recovers the already constructed canonical level-six Gram matrix.
This checks the full matrix, rather than only matching a determinant zero set. -/
theorem gram6Polynomial_eval (c : ℂ) :
    (evalRingHom c).mapMatrix gram6Polynomial = canGram6 c := by
  rw [canGram6_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram6Polynomial] <;> ring

/-- The determinant of the polynomial matrix is the level-four obstruction
polynomial. Equality follows from agreement at every complex central charge. -/
theorem gram4Polynomial_det : gram4Polynomial.det = determinant4 := by
  apply Polynomial.funext
  intro c
  change (evalRingHom c) gram4Polynomial.det = _
  rw [RingHom.map_det, gram4Polynomial_eval, ← determinant4_eval]

/-- The same coefficient-level identification at weight six. It justifies
transporting the known determinant calculation to rings with nilpotents. -/
theorem gram6Polynomial_det : gram6Polynomial.det = determinant6 := by
  apply Polynomial.funext
  intro c
  change (evalRingHom c) gram6Polynomial.det = _
  rw [RingHom.map_det, gram6Polynomial_eval, ← determinant6_eval]

/-- A dual-number kernel relation with a nonzero constant coefficient forces
zero determinant. That coefficient is invertible, so Cramer's adjugate identity
works even though dual numbers have zero divisors. -/
theorem det_eq_zero_of_lifted_kernel {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (DualNumber ℂ)) (v : n → DualNumber ℂ)
    (hker : M *ᵥ v = 0) (i : n) (hi : (v i).fst ≠ 0) : M.det = 0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker
  exact (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hi)).mem_nonZeroDivisors

/-- Any ordinary linear relation among a finite spanning family lifts through
arbitrary first-order changes of those states. The correction to the relation
is obtained by expressing the negative first-order error in the original spanning
family. No independence of that family is assumed or needed. -/
theorem exists_lifted_state_relation {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : Type*} [Fintype n] (u u₁ : n → V)
    (hspan : Submodule.span ℂ (Set.range u) = ⊤) (r : n → ℂ)
    (hr : ∑ j, r j • u j = 0) :
    ∃ s : n → ℂ, (∑ j, r j • u j = 0) ∧
      ∑ j, (r j • u₁ j + s j • u j) = 0 := by
  have hm : -(∑ j, r j • u₁ j) ∈ Submodule.span ℂ (Set.range u) := by
    rw [hspan]
    trivial
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
  refine ⟨s, hr, ?_⟩
  rw [Finset.sum_add_distrib, hs, add_neg_cancel]

/-- The matrix obtained by applying first-order linear functionals to first-order
states. Each entry retains both the change in the state and the change in the
functional. This is the form a deformed vacuum-pairing calculation must establish. -/
noncomputable def firstOrderPairingMatrix {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : Type*} (u u₁ : n → V) (a a₁ : n → V →ₗ[ℂ] ℂ) :
    Matrix n n (DualNumber ℂ) := fun i j =>
  inl (a i (u j)) + inr (a i (u₁ j) + a₁ i (u j))

/-- A lifted relation between the states lies in the kernel of every matrix
formed by first-order linear pairings with those states. The constant relation
kills both the constant pairing and the correction to the row functionals. -/
theorem pairingMatrix_mulVec_lifted_relation {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : Type*} [Fintype n] (u u₁ : n → V) (a a₁ : n → V →ₗ[ℂ] ℂ)
    (r s : n → ℂ) (hr : ∑ j, r j • u j = 0)
    (hs : ∑ j, (r j • u₁ j + s j • u j) = 0) :
    firstOrderPairingMatrix u u₁ a a₁ *ᵥ (fun j => inl (r j) + inr (s j)) = 0 := by
  funext i
  have h0 := congrArg (a i) hr
  have h1 := congrArg (a i) hs
  have h2 := congrArg (a₁ i) hr
  simp only [map_sum, map_smul, map_add, map_zero, smul_eq_mul] at h0 h1 h2
  apply TrivSqZeroExt.ext
  · simpa [Matrix.mulVec, dotProduct, firstOrderPairingMatrix, fst_sum, mul_comm] using h0
  · have h : ∑ j, (a i (u j) * s j + (a i (u₁ j) + a₁ i (u j)) * r j) = 0 := by
      calc
        _ = (∑ j, (r j * a i (u₁ j) + s j * a i (u j))) +
            ∑ j, r j * a₁ i (u j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [h1, h2, add_zero]
    simpa [Matrix.mulVec, dotProduct, firstOrderPairingMatrix, snd_sum, smul_eq_mul, mul_comm, add_comm] using h

/-- An ordinary relation among the states and an ordinary relation among the
row functionals kill the mixed first-order pairing. The state correction is
killed by the row relation, and the functional correction by the state relation.
Unlike the determinant argument, this obstruction needs no spanning hypothesis
and no chosen correction to either relation. -/
theorem pairingMatrix_tangent_of_two_relations
    {V : Type*} [AddCommGroup V] [Module ℂ V] {n : Type*} [Fintype n]
    (u u₁ : n → V) (a a₁ : n → V →ₗ[ℂ] ℂ) (q r : n → ℂ)
    (hq : ∑ i, q i • a i = 0) (hr : ∑ j, r j • u j = 0) :
    ∑ i, ∑ j, q i * (firstOrderPairingMatrix u u₁ a a₁ i j).snd * r j = 0 := by
  have hq' (v : V) : ∑ i, q i * a i v = 0 := by
    have h := congrArg (fun f : V →ₗ[ℂ] ℂ => f v) hq
    simpa using h
  have hr' (i : n) : ∑ j, r j * a₁ i (u j) = 0 := by
    have h := congrArg (a₁ i) hr
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul] using h
  simp only [firstOrderPairingMatrix, snd_add, snd_inl, snd_inr, zero_add]
  calc
    _ = (∑ i, ∑ j, q i * a i (u₁ j) * r j) +
        ∑ i, ∑ j, q i * (r j * a₁ i (u j)) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by
      rw [Finset.sum_comm (f := fun i j => q i * a i (u₁ j) * r j)]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, hq', hr', zero_mul, mul_zero,
        Finset.sum_const_zero, add_zero]

/-- A nonzero ordinary relation in a spanning family forces the determinant of
its first-order pairing matrix to vanish. The kernel vector is constructed, not
assumed, and has the required nonzero constant coefficient. Applying this to a
canonical Virasoro matrix still requires identifying its entries with the actual
deformed pairings on the fixed graded state space. -/
theorem det_pairingMatrix_eq_zero_of_spanning_relation
    {V : Type*} [AddCommGroup V] [Module ℂ V] {n : Type*} [Fintype n] [DecidableEq n]
    (u u₁ : n → V) (a a₁ : n → V →ₗ[ℂ] ℂ)
    (hspan : Submodule.span ℂ (Set.range u) = ⊤) (r : n → ℂ)
    (hr : ∑ j, r j • u j = 0) (i : n) (hi : r i ≠ 0) :
    (firstOrderPairingMatrix u u₁ a a₁).det = 0 := by
  obtain ⟨s, _, hs⟩ := exists_lifted_state_relation u u₁ hspan r hr
  apply det_eq_zero_of_lifted_kernel _ (fun j => inl (r j) + inr (s j))
    (pairingMatrix_mulVec_lifted_relation u u₁ a a₁ r s hr hs) i
  simpa using hi

/-- Evaluate the canonical level-four matrix at a central charge and a
first-order displacement, entry by entry. -/
noncomputable def gram4Dual (c δ : ℂ) : Matrix (Fin 2) (Fin 2) (DualNumber ℂ) :=
  (aeval (inl c + inr δ : DualNumber ℂ)).toRingHom.mapMatrix gram4Polynomial

/-- The corresponding first-order evaluation at level six. -/
noncomputable def gram6Dual (c δ : ℂ) : Matrix (Fin 4) (Fin 4) (DualNumber ℂ) :=
  (aeval (inl c + inr δ : DualNumber ℂ)).toRingHom.mapMatrix gram6Polynomial

/-- A genuine lifted kernel relation in the Lee–Yang canonical matrix prevents
nonzero central-charge motion. The relation must still be supplied from the VOA. -/
theorem leeYang_tangent_eq_zero_of_kernel (δ : ℂ) (v : Fin 2 → DualNumber ℂ)
    (hker : gram4Dual leeYangC δ *ᵥ v = 0) (i : Fin 2) (hi : (v i).fst ≠ 0) : δ = 0 := by
  apply leeYang_tangent_eq_zero
  have h := det_eq_zero_of_lifted_kernel _ v hker i hi
  simpa only [gram4Dual, ← RingHom.map_det, gram4Polynomial_det] using h

/-- A lifted kernel relation with a nonzero constant coefficient gives the
same first-order obstruction for Ising, using its first singular level six. -/
theorem ising_tangent_eq_zero_of_kernel (δ : ℂ) (v : Fin 4 → DualNumber ℂ)
    (hker : gram6Dual isingC δ *ᵥ v = 0) (i : Fin 4) (hi : (v i).fst ≠ 0) : δ = 0 := by
  apply ising_tangent_eq_zero
  have h := det_eq_zero_of_lifted_kernel _ v hker i hi
  simpa only [gram6Dual, ← RingHom.map_det, gram6Polynomial_det] using h

/-- The identical kernel criterion for M(2,7), at central charge −68/7. -/
theorem m27_tangent_eq_zero_of_kernel (δ : ℂ) (v : Fin 4 → DualNumber ℂ)
    (hker : gram6Dual m27C δ *ᵥ v = 0) (i : Fin 4) (hi : (v i).fst ≠ 0) : δ = 0 := by
  apply m27_tangent_eq_zero
  have h := det_eq_zero_of_lifted_kernel _ v hker i hi
  simpa only [gram6Dual, ← RingHom.map_det, gram6Polynomial_det] using h

/-- A nonzero kernel vector alone is insufficient over dual numbers. The one
by one matrix [ε] annihilates the nonzero vector [ε], but has nonzero determinant
ε. A lifted relation must have a nonzero constant coefficient, as required above. -/
theorem nilpotent_kernel_not_det_zero :
    ∃ (M : Matrix (Fin 1) (Fin 1) (DualNumber ℂ)) (v : Fin 1 → DualNumber ℂ),
      M *ᵥ v = 0 ∧ v ≠ 0 ∧ M.det ≠ 0 := by
  let ε : DualNumber ℂ := inr 1
  refine ⟨fun _ _ => ε, fun _ => ε, ?_, ?_, ?_⟩
  · funext i
    simp [Matrix.mulVec, dotProduct, ε]
  · intro h
    have hs := congrArg (fun v : Fin 1 → DualNumber ℂ => (v 0).snd) h
    simpa [ε] using hs
  · intro h
    have hs := congrArg TrivSqZeroExt.snd h
    simpa [Matrix.det_unique, ε] using hs

end VOA.VirRigidGramLift
