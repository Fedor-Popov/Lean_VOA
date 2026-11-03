/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumDeterminantBlock
import VOA.Examples.VirasoroVermaHighestProjection

/-!
# The first variation of the translated Verma form

The translation submodule is radical at highest weight zero. Consequently
first derivatives of the coefficients of a right-hand word expression do
not contribute when paired with a translated state. Only its value at zero
matters. This permits the first-order restricted pairing to descend to the
actual weight-one Verma module and inherit opposite-mode adjoints.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule Polynomial Module
open scoped Classical

/-- The actual word pairing polynomial with a fixed translated left word. -/
noncomputable def translationPairPolynomial (c : ℂ) (u w : List ℕ) : ℂ[X] :=
  vermaPairPolynomial (Polynomial.C c) X (u ++ [0]) (Finsupp.single w 1)

/-- Evaluation of this polynomial is the actual translated word pairing. -/
theorem translationPairPolynomial_eval (c h : ℂ) (u w : List ℕ) :
    (translationPairPolynomial c u w).eval h =
      vermaContravariant c h (negWord c h (u ++ [0])) (negWord c h w) := by
  have he := vermaPairPolynomial_eval (Polynomial.C c) X (Polynomial.aeval h)
    (u ++ [0]) (Finsupp.single w 1)
  simp only [evaluatePolynomialForm_single, map_one, one_smul] at he
  dsimp +instances only [Polynomial.aeval_def] at he
  rw [Polynomial.eval₂_C, Polynomial.eval₂_X] at he
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using he

/-- Every translated pairing has zero constant coefficient, since the
actual translation embedding is in the canonical radical at weight zero. -/
theorem translationPairPolynomial_zero (c : ℂ) (u w : List ℕ) :
    (translationPairPolynomial c u w).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, translationPairPolynomial_eval,
    ← translationEmbedding_negWord, translationEmbedding_mem_verma_radical,
    LinearMap.zero_apply]

/-- Read the first translated pairing coefficient on each actual PBW basis
vector and extend linearly. Uniform straightening will identify this with
coefficient extraction on arbitrary, possibly unsorted, negative words. -/
noncomputable def translationTangentRow (c : ℂ) (u : List ℕ) :
    Module.Dual ℂ (Verma c 0) :=
  (vermaSortedBasis c 0).constr ℂ
    (fun w => (translationPairPolynomial c u w.val).coeff 1)

/-- The first-order row on an ordered word is its defining coefficient. -/
theorem translationTangentRow_sorted (c : ℂ) (u w : List ℕ) (hw : SortedWord w) :
    translationTangentRow c u (negWord c 0 w) =
      (translationPairPolynomial c u w).coeff 1 := by
  rw [← vermaSortedBasis_apply c 0 ⟨w,hw⟩]
  exact (vermaSortedBasis c 0).constr_basis ℂ _ ⟨w,hw⟩

/-- The same coefficient identity holds on every negative word. Straightening
has constant coefficients independent of charge and weight, so differentiation
introduces no additional basis-change terms. -/
theorem translationTangentRow_word (c : ℂ) (u w : List ℕ) :
    translationTangentRow c u (negWord c 0 w) =
      (translationPairPolynomial c u w).coeff 1 := by
  let a := (vermaSortedBasis c 0).repr (negWord c 0 w)
  have hp : translationPairPolynomial c u w =
      ∑ j ∈ a.support, Polynomial.C (a j) * translationPairPolynomial c u j.val := by
    apply Polynomial.funext
    intro h
    simp only [eval_finsetSum, eval_mul, eval_C, translationPairPolynomial_eval]
    have hc : (vermaSortedBasis c h).repr (negWord c h w) = a :=
      verma_negWord_coordinates_independent c h c 0 w
    have he := (vermaSortedBasis c h).linearCombination_repr (negWord c h w)
    rw [hc] at he
    rw [← he]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      vermaSortedBasis_apply, smul_eq_mul]
  rw [hp, finsetSum_coeff]
  have he := congrArg (translationTangentRow c u)
    ((vermaSortedBasis c 0).linearCombination_repr (negWord c 0 w))
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    vermaSortedBasis_apply, smul_eq_mul] at he
  have hj (j : {w : List ℕ // SortedWord w}) :=
    translationTangentRow_sorted c u j.val j.property
  simp_rw [hj] at he
  simpa only [coeff_C_mul] using he.symm

/-- The universal pairing is additive in its polynomial right expression. -/
theorem vermaPairPolynomial_add_right (c : ℂ) (u : List ℕ)
    (f g : VermaPolynomialForm ℂ[X]) :
    vermaPairPolynomial (Polynomial.C c) X u (f+g) =
      vermaPairPolynomial (Polynomial.C c) X u f + vermaPairPolynomial (Polynomial.C c) X u g := by
  apply Polynomial.funext
  intro h
  change (Polynomial.aeval h) _ = (Polynomial.aeval h) _
  rw [map_add, vermaPairPolynomial_eval, vermaPairPolynomial_eval,
    vermaPairPolynomial_eval, evaluatePolynomialForm_add, map_add]

/-- Universal pairing respects multiplication of the right expression by
a scalar polynomial. This retains its parameter dependence exactly. -/
theorem vermaPairPolynomial_smul_right (c : ℂ) (u : List ℕ)
    (a : ℂ[X]) (f : VermaPolynomialForm ℂ[X]) :
    vermaPairPolynomial (Polynomial.C c) X u (a • f) = a * vermaPairPolynomial (Polynomial.C c) X u f := by
  apply Polynomial.funext
  intro h
  change (Polynomial.aeval h) _ = (Polynomial.aeval h) _
  rw [map_mul, vermaPairPolynomial_eval, vermaPairPolynomial_eval,
    evaluatePolynomialForm_smul, map_smul, smul_eq_mul]

/-- Evaluate polynomial coefficients in a fixed, explicitly typed Verma
module. This avoids inserting parameter casts into the tangent identities. -/
noncomputable def vermaWeightEvaluate (c h : ℂ) (f : VermaPolynomialForm ℂ[X]) :
    Verma c h := f.sum (fun w a => a.eval h • negWord c h w)

/-- Evaluation of a single polynomial word term. -/
theorem vermaWeightEvaluate_single (c h : ℂ) (w : List ℕ) (a : ℂ[X]) :
    vermaWeightEvaluate c h (Finsupp.single w a) = a.eval h • negWord c h w := by
  simp [vermaWeightEvaluate]

/-- Evaluation respects addition of word expressions. -/
theorem vermaWeightEvaluate_add (c h : ℂ) (f g : VermaPolynomialForm ℂ[X]) :
    vermaWeightEvaluate c h (f+g) = vermaWeightEvaluate c h f + vermaWeightEvaluate c h g := by
  exact Finsupp.sum_add_index (by simp) (by intros; simp [eval_add, add_smul])

/-- The fixed-type evaluation interprets the formal mode action as the
actual Verma mode, with charge c and highest weight h. -/
theorem vermaWeightEvaluate_mode (c h : ℂ) (m : ℤ) (f : VermaPolynomialForm ℂ[X]) :
    vermaWeightEvaluate c h (polynomialModeAction (Polynomial.C c) X m f) =
      vermaMode c h m (vermaWeightEvaluate c h f) := by
  have he := evaluate_polynomialModeAction (Polynomial.C c) X (Polynomial.aeval h) m f
  dsimp +instances only [evaluatePolynomialForm, Polynomial.aeval_def] at he
  rw [Polynomial.eval₂_C, Polynomial.eval₂_X] at he
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using he

/-- The first-order pairing with a translated left word depends only on
the actual value of a polynomial right expression at weight zero. Its
coefficient derivatives multiply a radical pairing and therefore vanish. -/
theorem translationTangentRow_evaluate (c : ℂ) (u : List ℕ)
    (f : VermaPolynomialForm ℂ[X]) :
    (vermaPairPolynomial (Polynomial.C c) X (u ++ [0]) f).coeff 1 =
      translationTangentRow c u
        (vermaWeightEvaluate c 0 f) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    have he : vermaPairPolynomial (Polynomial.C c) X (u ++ [0]) 0 = 0 := by
      have hh := vermaPairPolynomial_smul_right c (u ++ [0]) 0 0
      simpa using hh
    simp [he, vermaWeightEvaluate]
  | add f g hf hg =>
    rw [vermaPairPolynomial_add_right, coeff_add, vermaWeightEvaluate_add, map_add, hf, hg]
  | single w a =>
    have he : Finsupp.single w a = a • (Finsupp.single w (1 : ℂ[X])) := by simp
    rw [he, vermaPairPolynomial_smul_right]
    change (a * translationPairPolynomial c u w).coeff 1 = _
    rw [Polynomial.mul_coeff_one]
    rw [← he, vermaWeightEvaluate_single, map_smul, translationTangentRow_word]
    simp [translationPairPolynomial_zero, ← coeff_zero_eq_eval_zero, smul_eq_mul]

end VOA.InverseDS.VirasoroVerma
