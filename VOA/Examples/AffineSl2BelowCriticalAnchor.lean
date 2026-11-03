/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalRigidity
import VOA.Examples.AffineSl2BelowCriticalMatrixAnchor
import VOA.Examples.AffineSl2JointContractionDiagonal

/-!
# The large-negative-level anchor, and unconditional below-critical graded unitarity

This file **proves** the last named input `LayerSignAnchor compactRealFamily`, and hence the
below-critical graded unitarity of `V^k(sl₂)` for the ordinary current-PBW flag with **no
hypotheses** (`universal_gradedUnitary_belowCritical_unconditional`).

The level-polynomial Gram entries `gramPoly E i j = B(θ b_i, b_j)` satisfy

* `gramPoly_natDegree_le` — degree at most the shorter PBW length (each central factor consumes a
  creation mode, and the Gram polynomial is symmetric);
* `gramPoly_coeff_top` — at equal lengths the top coefficient is `δ_ij d_i` with `d_i > 0`: only a
  complete matching of each annihilator with its opposite-colour creator contributes, the colour
  multisets must agree, and the product of positive depths, Killing coefficients and multiplicities
  is a positive real (`AffineSl2ContractionMultiset`).

`MatrixRigidity.matrixLayerSign_eventually` then gives the graded-unitary layer signs at every
sufficiently negative level.
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2PBWWakimotoReduction
open AffineVOA.HighestModule AffineVOA.NormalOrdering
open Matrix MatrixRigidity Polynomial

noncomputable section

local notation "Ltr" => AffineVOA.NormalOrdering.Letter

/-! ## The Gram polynomials as vacuum pairing polynomials -/

theorem adjointColour_eq_swap (a : Fin 3) : adjointColour a = Equiv.swap (0 : Fin 3) 1 a := by
  fin_cases a <;> rfl

/-- The annihilator word of a flipped PBW monomial. -/
theorem adjointIndices_flip_litWord (mu : CurrentIndex) :
    adjointIndices (flipCurrentWord (litWord mu)) =
      (flipWord (orderedPBWColorWord mu)).reverse.map (fun a => (a.1, (a.2 : ℤ) + 1)) := by
  simp only [adjointIndices, flipCurrentWord, litWord, flipWord, List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp [add_comm]

theorem gramPoly_eq_wordPolynomial (E : ℤ) (i j : EIdx E) :
    gramPoly E i j = wordPolynomial ((flipWord (orderedPBWColorWord i.val)).reverse.map
      (fun a => (a.1, (a.2 : ℤ) + 1)) ++
        (orderedPBWColorWord j.val).map (fun a => (a.1, -(a.2 : ℤ) - 1))) := by
  rw [gramPoly, wordGramPolynomial, smul_smul, adjointIndices_flip_litWord]
  have hlen : (flipCurrentWord (litWord i.val)).length = (litWord i.val).length := by
    simp [flipCurrentWord]
  rw [hlen, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_smul]
  rfl

theorem annihilator_nonneg (mu : CurrentIndex) :
    ∀ m ∈ (flipWord (orderedPBWColorWord mu)).reverse.map (fun a => (a.1, (a.2 : ℤ) + 1)),
      0 ≤ m.2 := by
  intro m hm
  simp only [List.mem_map] at hm
  obtain ⟨a, -, rfl⟩ := hm
  dsimp
  omega

variable {k : ℂ} (hk : k + 2 ≠ 0)

/-- The Gram polynomial evaluates to the Chevalley-twisted pairing at every noncritical nonzero
level. -/
theorem gramPoly_eval (hk0 : k ≠ 0) {E : ℤ} (i j : EIdx E) :
    (gramPoly E i j).eval k = (universalForm k hk).form
      (vacuumChevalley k (currentPBWBasis k hk i.val)) (currentPBWBasis k hk j.val) := by
  rw [gramPoly, Polynomial.eval_smul, smul_eq_mul,
    wordGramPolynomial_universal k hk hk0, ← litWord_state hk i.val, ← litWord_state hk j.val]
  change _ = (universalForm k hk).form
    (vacuumChevalley k (NormalOrdering.currentWord (J k) (litWord i.val) (vacuumA k))) _
  rw [vacuumChevalley_word, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rfl

/-- The Gram polynomials are symmetric. -/
theorem gramPoly_symm {E : ℤ} (i j : EIdx E) : gramPoly E i j = gramPoly E j i := by
  apply polynomial_eq_of_nonzero_noncritical
  intro k hk0 hk
  rw [gramPoly_eval hk hk0, gramPoly_eval hk hk0, vacuumChevalley_form_symm k hk]

/-- **Degree at most the shorter length.** -/
theorem gramPoly_natDegree_le {E : ℤ} (i j : EIdx E) :
    (gramPoly E i j).natDegree ≤ min (eLen E i) (eLen E j) := by
  have hcol : ∀ i j : EIdx E, (gramPoly E i j).natDegree ≤ eLen E j := by
    intro i j
    rw [gramPoly_eq_wordPolynomial]
    exact centralPolynomial_natDegree_le
      (wordNormal_prefix_mem _ _ (annihilator_nonneg i.val))
  exact le_min (by rw [gramPoly_symm]; exact hcol j i) (hcol i j)

/-! ## The top coefficient -/

/-- The real complete-matching weight. -/
def realDiag : List Ltr → ℝ
  | [] => 1
  | a :: u => ((u.count a : ℝ) + 1) * (((a.2 : ℝ) + 1) * (if a.1 = 2 then 2 else 1)) * realDiag u

theorem realDiag_pos : ∀ u : List Ltr, 0 < realDiag u
  | [] => one_pos
  | a :: u => by
      have := realDiag_pos u
      simp only [realDiag]
      have h1 : (0 : ℝ) < (u.count a : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (a.2 : ℝ) + 1 := by positivity
      have h3 : (0 : ℝ) < if a.1 = 2 then 2 else 1 := by split_ifs <;> norm_num
      positivity

theorem diagonalContraction_eq_realDiag :
    ∀ u : List Ltr, diagonalContraction u = ((realDiag u : ℝ) : ℂ)
  | [] => by simp [diagonalContraction, realDiag]
  | a :: u => by
      simp only [diagonalContraction, realDiag, contractionWeight,
        diagonalContraction_eq_realDiag u]
      push_cast
      split_ifs <;> push_cast <;> ring

/-- The positive diagonal weights. -/
def topWeight {E : ℤ} (i : EIdx E) : ℝ := realDiag (flipWord (orderedPBWColorWord i.val))

theorem flipWord_map_opposite (w : List Ltr) :
    ((flipWord w : List Ltr) : Multiset Ltr).map oppositeLetter = (w : Multiset Ltr) := by
  rw [Multiset.map_coe, flipWord, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro a _
  simp [oppositeLetter, adjointColour_eq_swap]

/-- **The top coefficient at equal lengths is `δ_ij d_i`.** -/
theorem gramPoly_coeff_top {E : ℤ} (i j : EIdx E) (hlen : eLen E i = eLen E j) :
    (gramPoly E i j).coeff (eLen E i) = if i = j then ((topWeight i : ℝ) : ℂ) else 0 := by
  have hl : ((flipWord (orderedPBWColorWord i.val)).reverse.map
      (fun a => (a.1, (a.2 : ℤ) + 1))).length = (orderedPBWColorWord j.val).length := by
    simp only [List.length_map, List.length_reverse, flipWord]
    exact hlen
  rw [gramPoly_eq_wordPolynomial, show eLen E i = (orderedPBWColorWord j.val).length from hlen,
    equal_length_pairing_top_contractions _ _ (annihilator_nonneg i.val) hl]
  split_ifs with hij
  · subst hij
    rw [contractions_vacuum_diagonal _ _ (flipWord_map_opposite _).symm, coeff_smul,
      diagonalContraction_eq_realDiag]
    have : (flipWord (orderedPBWColorWord i.val)).length = (orderedPBWColorWord i.val).length := by
      simp [flipWord]
    rw [this, coeff_X_pow_self, smul_eq_mul, mul_one]
    rfl
  · rw [contractions_vacuum_zero]
    · simp
    · rw [flipWord_map_opposite]
      intro h
      exact hij (Subtype.ext (orderedPBW_multiset_injective h.symm))

/-! ## The anchor -/

/-- **The named anchor input is a theorem.** -/
theorem layerSignAnchor_compact : LayerSignAnchor compactRealFamily := by
  intro E
  have hherm : ∀ x : ℝ, x < -2 → (Matrix.map (gramPoly E) (Polynomial.eval (x : ℂ))).IsHermitian := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have heq : Matrix.map (gramPoly E) (Polynomial.eval (x : ℂ)) =
        gram (noncritical_of_lt hx) (compactRealFamily x hx) E := by
      ext i j
      rw [map_apply]
      exact (gram_eq_eval (noncritical_of_lt hx) (conj_ofReal x) hx0 E i j).symm
    rw [heq]
    exact gram_isHermitian (noncritical_of_lt hx) (conj_ofReal x) E
  obtain ⟨K, hK⟩ := matrixLayerSign_eventually (ℓ := eLen E)
    (gramPoly E : Matrix (EIdx E) (EIdx E) ℂ[X]) (fun i => topWeight i)
    (fun i => realDiag_pos _) gramPoly_natDegree_le gramPoly_coeff_top (-2) hherm
  refine ⟨K, fun x hx hxK => ?_⟩
  refine (layerPositive_iff_matrixLayerSign (noncritical_of_lt hx)
    (compactRealFamily_isCompact x hx)).mpr fun r => ?_
  have hx0 : (x : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have heq : gram (noncritical_of_lt hx) (compactRealFamily x hx) E =
      Matrix.map (gramPoly E) (Polynomial.eval (x : ℂ)) := by
    ext i j
    rw [map_apply]
    exact gram_eq_eval (noncritical_of_lt hx) (conj_ofReal x) hx0 E i j
  rw [heq]
  exact hK x hxK r

/-- **Below-critical graded unitarity of the universal affine `sl₂` vacuum VOA for the
ordinary current-PBW flag — unconditional.**

For every real `k < -2`, `V^k(sl₂)` with its normalized canonical invariant form, the
constructed compact real structure (`compactRealFamily`) and the ordinary current-length flag
(`ordinaryFlag`) is graded-unitary: at every conformal weight the form is nondegenerate on every
flag step (ABLR clause (iv)) and the `σ`-twisted Hermitian form is positive definite on every
layer (clause (vi)); clause (v) is then `layerDecomposition`.

No hypothesis beyond `k < -2`. -/
theorem universal_gradedUnitary_belowCritical_unconditional (k : ℝ) (hk : k < -2) :
    GradedUnitary (universalForm (k : ℂ) (noncritical_of_lt hk)) (compactRealFamily k hk)
      (ordinaryFlag (k : ℂ) (noncritical_of_lt hk)) :=
  universal_gradedUnitary_belowCritical_of_anchor layerSignAnchor_compact k hk

end

end AffineSl2BelowCritical

end VOA
