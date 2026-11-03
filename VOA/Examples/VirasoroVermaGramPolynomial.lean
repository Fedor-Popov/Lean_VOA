/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaContravariant
import VOA.Examples.VirasoroVermaPolynomialWard
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The actual two-variable Verma Gram polynomial

The finite commutation algorithm acts on arbitrary polynomial word expressions.
Moving a negative word to the other side of the actual contravariant pairing
then gives a universal polynomial in central charge and highest weight.
Its specialization is the actual Gram matrix at every parameter. No Kac
factorization, nondegeneracy or prescribed singular locus is assumed.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule Module
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Extend the proved polynomial action on a word linearly to every finite
word expression over a complex coefficient algebra. -/
noncomputable def polynomialModeAction (C H : R) (m : ℤ) :
    End R (VermaPolynomialForm R) :=
  Finsupp.linearCombination R (vermaModePolynomial C H m)

/-- Acting on a single word expression gives the stated scalar multiple
of its recursively computed mode action. -/
theorem polynomialModeAction_single (C H : R) (m : ℤ) (w : List ℕ) (a : R) :
    polynomialModeAction C H m (Finsupp.single w a) =
      a • vermaModePolynomial C H m w := by
  simp [polynomialModeAction]

/-- The polynomial action on arbitrary finite expressions specializes to
the actual Verma mode action, not just to a formal commutation rule. -/
theorem evaluate_polynomialModeAction (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (m : ℤ) (f : VermaPolynomialForm R) :
    evaluatePolynomialForm C H ev (polynomialModeAction C H m f) =
      vermaMode (ev C) (ev H) m (evaluatePolynomialForm C H ev f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [evaluatePolynomialForm]
  | add f g hf hg => simp only [map_add, evaluatePolynomialForm_add, hf, hg]
  | single w a =>
    rw [polynomialModeAction_single, evaluatePolynomialForm_smul,
      evaluate_vermaModePolynomial, evaluatePolynomialForm_single, map_smul]

/-- A universal pairing with an arbitrary right word expression. Strip the
left creation word, apply each opposite positive mode on the right, then
extract the coefficient of the highest vector. -/
noncomputable def vermaPairPolynomial (C H : R) :
    List ℕ → VermaPolynomialForm R → R
  | [], f => polynomialFormCoordinate f ⟨[], sortedWord_nil⟩
  | i::w, f => vermaPairPolynomial C H w
      (polynomialModeAction C H ((i : ℤ)+1) f)

/-- Every universal word pairing evaluates to the ACTUAL normalized
contravariant form. This supplies its mathematical meaning at all charges
and weights, including singular parameters. -/
theorem vermaPairPolynomial_eval (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (w : List ℕ) (f : VermaPolynomialForm R) :
    ev (vermaPairPolynomial C H w f) =
      vermaContravariant (ev C) (ev H) (negWord (ev C) (ev H) w)
        (evaluatePolynomialForm C H ev f) := by
  induction w generalizing f with
  | nil =>
    rw [vermaPairPolynomial, polynomialFormCoordinate_eval,
      negWord_nil, vermaContravariant_highest_left]
    rfl
  | cons i w ih =>
    rw [vermaPairPolynomial, ih, evaluate_polynomialModeAction,
      negWord_cons, vermaContravariant_adj]
    rw [show (i : ℤ)+1 = -(-(i : ℤ)-1) by omega]

/-- The finite level-n Gram matrix of the constructed contravariant form,
in the genuine partition basis of the general Verma module. Parts one are
included; this is distinct from the vacuum partition Gram matrix. -/
noncomputable def vermaGramMatrix (c h : ℂ) (n : ℕ) :
    Matrix (VermaPartitions n) (VermaPartitions n) ℂ := fun i j =>
  vermaContravariant c h (negWord c h i.val) (negWord c h j.val)

/-- Construct the Gram matrix over any commutative complex algebra by the
finite word algorithm. No symbolic determinant formula is postulated. -/
noncomputable def vermaAlgebraGramMatrix (C H : R) (n : ℕ) :
    Matrix (VermaPartitions n) (VermaPartitions n) R := fun i j =>
  vermaPairPolynomial C H i.val (Finsupp.single j.val 1)

/-- Specializing the algebraic Gram matrix gives the actual Verma pairing
matrix, entry by entry. This proves the basis and normalization match. -/
theorem vermaAlgebraGramMatrix_eval (C H : R) (ev : R →ₐ[ℂ] ℂ) (n : ℕ) :
    (vermaAlgebraGramMatrix C H n).map ev.toRingHom =
      vermaGramMatrix (ev C) (ev H) n := by
  ext i j
  change ev (vermaPairPolynomial C H i.val (Finsupp.single j.val 1)) = _
  rw [vermaPairPolynomial_eval, evaluatePolynomialForm_single, map_one, one_smul]
  rfl

/-- The universal Gram matrix has two independent polynomial variables:
central charge in variable zero and highest weight in variable one. -/
noncomputable def vermaGramPolynomial (n : ℕ) :
    Matrix (VermaPartitions n) (VermaPartitions n) (MvPolynomial (Fin 2) ℂ) :=
  vermaAlgebraGramMatrix (MvPolynomial.X 0) (MvPolynomial.X 1) n

/-- Evaluating the two formal parameters recovers the actual Gram matrix
at every complex pair, with no regularity or genericity restriction. -/
theorem vermaGramPolynomial_eval (c h : ℂ) (n : ℕ) :
    (vermaGramPolynomial n).map
      (MvPolynomial.aeval (fun i : Fin 2 => if i=0 then c else h)).toRingHom =
      vermaGramMatrix c h n := by
  simpa [vermaGramPolynomial] using vermaAlgebraGramMatrix_eval
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))
    (MvPolynomial.aeval (fun i : Fin 2 => if i=0 then c else h)) n

/-- The two-variable determinant polynomial evaluates to the determinant
of the actual contravariant form, not a separately defined candidate. -/
theorem vermaGramPolynomial_det_eval (c h : ℂ) (n : ℕ) [DecidableEq (VermaPartitions n)] :
    MvPolynomial.aeval (fun i : Fin 2 => if i=0 then c else h)
      (vermaGramPolynomial n).det = (vermaGramMatrix c h n).det := by
  change (MvPolynomial.aeval (fun i : Fin 2 => if i=0 then c else h)).toRingHom
    (vermaGramPolynomial n).det = _
  rw [RingHom.map_det]
  exact congrArg Matrix.det (vermaGramPolynomial_eval c h n)

/-- The actual Gram matrix is symmetric because the constructed form is
symmetric, even at parameters where the matrix is singular. -/
theorem vermaGramMatrix_symm (c h : ℂ) (n : ℕ) :
    (vermaGramMatrix c h n).transpose = vermaGramMatrix c h n := by
  ext i j
  exact vermaContravariant_symm c h _ _

/-- Matrix-vector multiplication is pairing each actual partition word
with the state assembled from the vector of coefficients. -/
theorem vermaGramMatrix_mulVec (c h : ℂ) (n : ℕ)
    (a : VermaPartitions n → ℂ) (i : VermaPartitions n) :
    (vermaGramMatrix c h n).mulVec a i =
      vermaContravariant c h (negWord c h i.val) (vermaLevelState c h n a) := by
  classical
  simp [Matrix.mulVec, dotProduct, vermaGramMatrix, vermaLevelState, mul_comm]

/-- A positive-level singular state gives an actual Gram kernel vector.
This conclusion uses the constructed radical theorem, not a Kac formula. -/
theorem vermaGramMatrix_singular_kernel (c h : ℂ) (n : ℕ) (hn : 0 < n)
    (a : VermaPartitions n → ℂ)
    (h1 : vermaMode c h 1 (vermaLevelState c h n a) = 0)
    (h2 : vermaMode c h 2 (vermaLevelState c h n a) = 0) :
    (vermaGramMatrix c h n).mulVec a = 0 := by
  have hr := vermaContravariant_singular_radical c h n hn _
    (vermaLevelState_mem c h n a) h1 h2
  funext i
  rw [vermaGramMatrix_mulVec, vermaContravariant_symm, hr]
  rfl


/-- A nonzero coefficient vector satisfying the positive singular equations
forces the actual Verma determinant to vanish at that parameter. -/
theorem vermaGramMatrix_det_zero_of_singular (c h : ℂ) (n : ℕ)
    [DecidableEq (VermaPartitions n)] (hn : 0 < n)
    (a : VermaPartitions n → ℂ) (hne : a ≠ 0)
    (h1 : vermaMode c h 1 (vermaLevelState c h n a) = 0)
    (h2 : vermaMode c h 2 (vermaLevelState c h n a) = 0) :
    (vermaGramMatrix c h n).det = 0 := by
  by_contra hd
  have hu : IsUnit (vermaGramMatrix c h n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  apply hne
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [vermaGramMatrix_singular_kernel c h n hn a h1 h2, Matrix.mulVec_zero]

/-- Every actual homogeneous Verma state has partition coefficients whose
assembled state is exactly the original vector. This uses the proved basis. -/
theorem exists_vermaLevelState (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n) :
    ∃ a : VermaPartitions n → ℂ, vermaLevelState c h n a = v := by
  let a : VermaPartitions n → ℂ := fun i =>
    (vermaLevelBasis c h n).repr ⟨v, hv⟩ i
  refine ⟨a, ?_⟩
  have he := congrArg (fun x : sortedSpan c h n => (x : Verma c h))
    ((vermaLevelBasis c h n).sum_repr ⟨v, hv⟩)
  simpa only [vermaLevelState, a, Submodule.coe_sum, Submodule.coe_smul,
    vermaLevelBasis, Module.Basis.mk_apply, vermaLevelWord] using he

/-- A nonzero actual Verma Gram determinant excludes positive-level
singular states. No genericity assumption replaces the displayed determinant
condition; proving it at minimal charges is separate representation theory. -/
theorem vermaGramMatrix_nonsingular_no_singular (c h : ℂ) (n : ℕ)
    [DecidableEq (VermaPartitions n)] (hn : 0 < n)
    (hd : (vermaGramMatrix c h n).det ≠ 0)
    (v : Verma c h) (hv : v ∈ sortedSpan c h n)
    (h1 : vermaMode c h 1 v = 0) (h2 : vermaMode c h 2 v = 0) : v = 0 := by
  obtain ⟨a, rfl⟩ := exists_vermaLevelState c h n v hv
  by_cases ha : a = 0
  · exact (vermaLevelState_eq_zero_iff c h n a).mpr ha
  · exact False.elim (hd (vermaGramMatrix_det_zero_of_singular c h n hn a ha h1 h2))


/-- At a fixed homogeneous level the finite Gram kernel is exactly the
radical of the whole form on the assembled state. Other levels vanish by
proved orthogonality, so no missing tests outside this matrix are assumed. -/
theorem vermaGramMatrix_kernel_iff_radical (c h : ℂ) (n : ℕ)
    (a : VermaPartitions n → ℂ) :
    (vermaGramMatrix c h n).mulVec a = 0 ↔
      vermaContravariant c h (vermaLevelState c h n a) = 0 := by
  constructor
  · intro hk
    apply (vermaSortedBasis c h).ext
    intro w
    simp only [vermaSortedBasis_apply, LinearMap.zero_apply]
    by_cases he : energyHW w.val = n
    · have hw := congrFun hk (⟨w.val, w.property, he⟩ : VermaPartitions n)
      rw [vermaGramMatrix_mulVec, vermaContravariant_symm] at hw
      exact hw
    · exact vermaContravariant_orthogonal c h n (energyHW w.val) _ _
        (vermaLevelState_mem c h n a)
        (negWord_mem_sortedSpan_of_sorted c h w.property rfl) (Ne.symm he)
  · intro hr
    funext i
    rw [vermaGramMatrix_mulVec, vermaContravariant_symm, hr]
    rfl

/-- A nondegenerate level matrix has no radical vector in its homogeneous
component. This includes level zero and does not require singular equations. -/
theorem verma_radical_zero_of_det_ne_zero (c h : ℂ) (n : ℕ)
    [DecidableEq (VermaPartitions n)] (hd : (vermaGramMatrix c h n).det ≠ 0)
    (v : Verma c h) (hv : v ∈ sortedSpan c h n)
    (hr : vermaContravariant c h v = 0) : v = 0 := by
  obtain ⟨a, rfl⟩ := exists_vermaLevelState c h n v hv
  apply (vermaLevelState_eq_zero_iff c h n a).mpr
  have hu : IsUnit (vermaGramMatrix c h n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [(vermaGramMatrix_kernel_iff_radical c h n a).mpr hr, Matrix.mulVec_zero]

/-- If all earlier level determinants are nonzero, a radical vector at
level n is killed by every positive mode. Modes above n vanish by weight;
the others land in a nondegenerate earlier component of the same radical. -/
theorem verma_radical_first_level_singular (c h : ℂ) (n : ℕ)
    [∀ k : ℕ, DecidableEq (VermaPartitions k)]
    (hlower : ∀ k < n, (vermaGramMatrix c h k).det ≠ 0)
    (v : Verma c h) (hv : v ∈ sortedSpan c h n)
    (hr : vermaContravariant c h v = 0) (m : ℤ) (hm : 0 < m) :
    vermaMode c h m v = 0 := by
  by_cases hi : (n : ℤ) < m
  · exact verma_mode_above_level c h n v hv m hi
  · let k := ((n : ℤ)-m).toNat
    have hk : (n : ℤ)-m = (k : ℤ) := by dsimp [k]; omega
    have hkn : k < n := by omega
    exact verma_radical_zero_of_det_ne_zero c h k (hlower k hkn) _
      (verma_mode_mem_level c h n k v hv m hk)
      (vermaContravariant_radical_mode c h m v hr)

/-- A first degenerate actual Verma Gram level produces a genuine nonzero
singular state at that level. The determinant hypotheses are explicit ordinary
conditions; no Kac root formula is assumed or claimed here. -/
theorem verma_singular_of_first_gram_root (c h : ℂ) (n : ℕ)
    [∀ k : ℕ, DecidableEq (VermaPartitions k)]
    (hroot : (vermaGramMatrix c h n).det = 0)
    (hlower : ∀ k < n, (vermaGramMatrix c h k).det ≠ 0) :
    ∃ v : Verma c h, v ≠ 0 ∧ v ∈ sortedSpan c h n ∧
      ∀ m : ℤ, 0 < m → vermaMode c h m v = 0 := by
  obtain ⟨a, hne, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨vermaLevelState c h n a, ?_, vermaLevelState_mem c h n a, ?_⟩
  · intro hz
    exact hne ((vermaLevelState_eq_zero_iff c h n a).mp hz)
  · exact verma_radical_first_level_singular c h n hlower _
      (vermaLevelState_mem c h n a) ((vermaGramMatrix_kernel_iff_radical c h n a).mp ha)

end VOA.InverseDS.VirasoroVerma
