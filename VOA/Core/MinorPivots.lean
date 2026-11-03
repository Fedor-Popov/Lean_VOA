/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.Order
import VOA.Core.FlagMinors
import VOA.Core.HermitianSchur

/-!
# Leading-minor pivots: congruence invariance, the Jacobi quotient identity,
# the converse Sylvester criterion, and layer definiteness

Pure linear algebra; no vertex algebras appear.  This file supplies the
"positivity/pivot half" that `Core.FlagMinors` deliberately deferred, plus a
frame-invariance lemma for Gram matrices.

## Contents

* `leadingPrincipal_mul_right_of_blockTriangular`, `..._left_of_transpose` —
  cutting the leading corner commutes with multiplication by a triangular
  factor on the correct side.
* `det_leadingPrincipal_unitriangular_congr` — **frame invariance**:
  congruence by an upper-unitriangular matrix preserves every leading
  principal minor.  This is why the cumulative minors tested in the one-shape
  metric calculation are invariants of the physical frame class, independent
  of the still-unidentified energy-lowering part of the reflection.
* `schurOfLeading` — the Schur complement of a leading block inside a larger
  leading block.
* `det_leadingPrincipal_eq_mul_det_schurOfLeading` — **the Jacobi quotient
  identity** `D_{l+j} = D_l · det(Schur block)`.
* `posDef_of_det_leadingPrincipal_pos` — **the converse Sylvester
  criterion** over `ℝ`: all leading principal minors positive implies
  positive definite.  (Mathlib has only the easy direction.)
* `schurOfLeading_posDef_of_sign_ratios` /
  `schurOfLeading_negDef_of_sign_ratios` — **the layer lemma**: if every
  consecutive minor ratio in the range `(l, l+j]` has sign `ε`, the layer
  Schur complement is `ε`-definite.  Together with
  `FlagMinors.nondegenerate_flag_iff_minors` this machine-checks the finite
  endgame of the polarized bi-Rees reduction: prescribed cumulative minor
  signs force the exact-layer forms to be definite of the predicted signs.

All statements are for matrices over a field (over `ℝ` where order enters);
`Fin`-index arithmetic is handled through `Fin.castLE` and
`finSumFinEquiv`, never through subtraction.
-/

namespace VOA

namespace FlagMinors

open Matrix

section Congruence

variable {K : Type*} [Field K] {m : ℕ}

/-- Cutting the leading corner commutes with multiplication when the **right**
factor is upper triangular: entries of `A * B` in the leading corner only see
leading-corner entries of both factors. -/
theorem leadingPrincipal_mul_right_of_blockTriangular
    (A B : Matrix (Fin m) (Fin m) K) (hB : B.BlockTriangular id)
    {k : ℕ} (hk : k ≤ m) :
    leadingPrincipal (A * B) hk
      = leadingPrincipal A hk * leadingPrincipal B hk := by
  ext i j
  simp only [leadingPrincipal_apply, Matrix.mul_apply]
  symm
  have hmap : ∑ l : Fin k,
      A (Fin.castLE hk i) (Fin.castLE hk l) * B (Fin.castLE hk l) (Fin.castLE hk j)
      = ∑ l ∈ Finset.univ.map (Fin.castLEEmb hk),
          A (Fin.castLE hk i) l * B l (Fin.castLE hk j) := by
    rw [Finset.sum_map]
    simp [Fin.coe_castLEEmb]
  rw [hmap]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  have hlk : ¬ (l : ℕ) < k := by
    intro hcon
    exact hl (Finset.mem_map.mpr
      ⟨⟨(l : ℕ), hcon⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hBz : B l (Fin.castLE hk j) = 0 := by
    apply hB
    show (Fin.castLE hk j : Fin m) < l
    have hj : (j : ℕ) < k := j.isLt
    exact Fin.lt_def.mpr (by simp only [Fin.coe_castLE]; omega)
  rw [hBz, mul_zero]

/-- Cutting the leading corner commutes with transposition. -/
theorem leadingPrincipal_transpose (M : Matrix (Fin m) (Fin m) K)
    {k : ℕ} (hk : k ≤ m) :
    leadingPrincipal Mᵀ hk = (leadingPrincipal M hk)ᵀ := rfl

/-- Cutting the leading corner commutes with multiplication when the **left**
factor is lower triangular (its transpose upper triangular). -/
theorem leadingPrincipal_mul_left_of_transpose_blockTriangular
    (A B : Matrix (Fin m) (Fin m) K) (hA : Aᵀ.BlockTriangular id)
    {k : ℕ} (hk : k ≤ m) :
    leadingPrincipal (A * B) hk
      = leadingPrincipal A hk * leadingPrincipal B hk := by
  have h := leadingPrincipal_mul_right_of_blockTriangular Bᵀ Aᵀ hA hk
  calc leadingPrincipal (A * B) hk
      = ((leadingPrincipal ((A * B)ᵀ) hk))ᵀ := by
        rw [leadingPrincipal_transpose, Matrix.transpose_transpose]
    _ = ((leadingPrincipal (Bᵀ * Aᵀ) hk))ᵀ := by rw [Matrix.transpose_mul]
    _ = ((leadingPrincipal Bᵀ hk) * (leadingPrincipal Aᵀ hk))ᵀ := by rw [h]
    _ = leadingPrincipal A hk * leadingPrincipal B hk := by
        rw [Matrix.transpose_mul, leadingPrincipal_transpose,
          leadingPrincipal_transpose, Matrix.transpose_transpose,
          Matrix.transpose_transpose]

/-- The leading corner of an upper-triangular matrix is upper triangular. -/
theorem blockTriangular_leadingPrincipal
    {U : Matrix (Fin m) (Fin m) K} (hU : U.BlockTriangular id)
    {k : ℕ} (hk : k ≤ m) :
    (leadingPrincipal U hk).BlockTriangular id := by
  intro i j hij
  apply hU
  show (Fin.castLE hk j : Fin m) < Fin.castLE hk i
  have := Fin.lt_def.mp hij
  exact Fin.lt_def.mpr (by simpa using this)

/-- The leading corner of a unit-diagonal upper-triangular matrix has
determinant one. -/
theorem det_leadingPrincipal_eq_one_of_unitriangular
    {U : Matrix (Fin m) (Fin m) K} (hU : U.BlockTriangular id)
    (hdiag : ∀ i, U i i = 1) {k : ℕ} (hk : k ≤ m) :
    (leadingPrincipal U hk).det = 1 := by
  rw [Matrix.det_of_upperTriangular (blockTriangular_leadingPrincipal hU hk)]
  simp [leadingPrincipal_apply, hdiag]

/-- **Frame invariance of leading principal minors.**  Congruence by an
upper-unitriangular matrix preserves every leading principal minor. -/
theorem det_leadingPrincipal_unitriangular_congr
    (B : Matrix (Fin m) (Fin m) K) {U : Matrix (Fin m) (Fin m) K}
    (hU : U.BlockTriangular id) (hdiag : ∀ i, U i i = 1)
    {k : ℕ} (hk : k ≤ m) :
    (leadingPrincipal (Uᵀ * B * U) hk).det = (leadingPrincipal B hk).det := by
  have hUT : (Uᵀ)ᵀ.BlockTriangular id := by
    rw [Matrix.transpose_transpose]; exact hU
  rw [Matrix.mul_assoc,
    leadingPrincipal_mul_left_of_transpose_blockTriangular _ _ hUT hk,
    leadingPrincipal_mul_right_of_blockTriangular _ _ hU hk,
    Matrix.det_mul, Matrix.det_mul]
  have h1 : (leadingPrincipal Uᵀ hk).det = 1 := by
    rw [leadingPrincipal_transpose, Matrix.det_transpose]
    exact det_leadingPrincipal_eq_one_of_unitriangular hU hdiag hk
  rw [h1, det_leadingPrincipal_eq_one_of_unitriangular hU hdiag hk,
    one_mul, mul_one]

end Congruence

section Pivot

variable {K : Type*} [Field K] {m : ℕ}

/-- The embedding of the `j` "tail" indices `l, l+1, …, l+j-1` into `Fin m`. -/
def tailEmb (l j : ℕ) (hlj : l + j ≤ m) (i : Fin j) : Fin m :=
  Fin.castLE hlj (Fin.natAdd l i)

@[simp] theorem tailEmb_val (l j : ℕ) (hlj : l + j ≤ m) (i : Fin j) :
    (tailEmb l j hlj i : ℕ) = l + i := rfl

/-- The Schur complement of the leading `l`-block inside the leading
`(l+j)`-block. -/
noncomputable def schurOfLeading (M : Matrix (Fin m) (Fin m) K) (l j : ℕ)
    (hlj : l + j ≤ m) : Matrix (Fin j) (Fin j) K :=
  M.submatrix (tailEmb l j hlj) (tailEmb l j hlj)
    - M.submatrix (tailEmb l j hlj)
        (Fin.castLE (le_trans (Nat.le_add_right l j) hlj))
      * (leadingPrincipal M (le_trans (Nat.le_add_right l j) hlj))⁻¹
      * M.submatrix (Fin.castLE (le_trans (Nat.le_add_right l j) hlj))
          (tailEmb l j hlj)

/-- Unfolding `schurOfLeading` with an arbitrary proof of `l ≤ m`
(proof irrelevance, stated once so later proofs can rewrite). -/
theorem schurOfLeading_def (M : Matrix (Fin m) (Fin m) K) (l j : ℕ)
    (hlj : l + j ≤ m) (hl : l ≤ m) :
    schurOfLeading M l j hlj
      = M.submatrix (tailEmb l j hlj) (tailEmb l j hlj)
        - M.submatrix (tailEmb l j hlj) (Fin.castLE hl)
          * (leadingPrincipal M hl)⁻¹
          * M.submatrix (Fin.castLE hl) (tailEmb l j hlj) := rfl

/-- The leading `(l+j)`-block, reindexed by `finSumFinEquiv`, is the block
matrix of the leading `l`-block, the two off-diagonal strips, and the tail
block. -/
theorem leadingPrincipal_submatrix_finSumFinEquiv
    (M : Matrix (Fin m) (Fin m) K) (l j : ℕ) (hlj : l + j ≤ m)
    (hl : l ≤ m) :
    (leadingPrincipal M hlj).submatrix finSumFinEquiv finSumFinEquiv
      = Matrix.fromBlocks (leadingPrincipal M hl)
          (M.submatrix (Fin.castLE hl) (tailEmb l j hlj))
          (M.submatrix (tailEmb l j hlj) (Fin.castLE hl))
          (M.submatrix (tailEmb l j hlj) (tailEmb l j hlj)) := by
  ext i j'
  cases i <;> cases j' <;>
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, leadingPrincipal_apply] <;>
    exact congrArg₂ M (Fin.ext (by simp)) (Fin.ext (by simp))

/-- **The Jacobi quotient identity**: when the leading `l`-minor is
nonzero, `D_{l+j} = D_l · det (Schur complement of the leading `l`-block
inside the leading `(l+j)`-block)`. -/
theorem det_leadingPrincipal_eq_mul_det_schurOfLeading
    (M : Matrix (Fin m) (Fin m) K) (l j : ℕ) (hlj : l + j ≤ m)
    (hl : l ≤ m) (hdet : IsUnit (leadingPrincipal M hl).det) :
    (leadingPrincipal M hlj).det
      = (leadingPrincipal M hl).det * (schurOfLeading M l j hlj).det := by
  letI := Matrix.invertibleOfIsUnitDet _ hdet
  have hre := leadingPrincipal_submatrix_finSumFinEquiv M l j hlj hl
  have hdet2 : (leadingPrincipal M hlj).det
      = ((leadingPrincipal M hlj).submatrix finSumFinEquiv finSumFinEquiv).det :=
    (Matrix.det_submatrix_equiv_self finSumFinEquiv _).symm
  rw [hdet2, hre, Matrix.det_fromBlocks₁₁, schurOfLeading_def M l j hlj hl,
    Matrix.invOf_eq_nonsing_inv]

end Pivot

section Sylvester

open scoped ComplexOrder

variable {m : ℕ}

/-- Every leading principal block of a positive-definite real matrix is
positive definite. -/
theorem posDef_leadingPrincipal {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.PosDef) {k : ℕ} (hk : k ≤ m) :
    (leadingPrincipal M hk).PosDef :=
  hM.submatrix (Fin.castLE_injective hk)

/-- A real symmetric `1 × 1` matrix with a positive determinant is positive
definite. -/
theorem posDef_fin_one_of_det_pos {S : Matrix (Fin 1) (Fin 1) ℝ}
    (hH : S.IsHermitian) (hdet : 0 < S.det) : S.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro x hx
  have hx0 : x 0 ≠ 0 := by
    intro h
    exact hx (funext fun i => by fin_cases i; exact h)
  have h00 : 0 < S 0 0 := by rw [← Matrix.det_fin_one S]; exact hdet
  have hexp : star x ⬝ᵥ (S *ᵥ x) = S 0 0 * x 0 ^ 2 := by
    simp [dotProduct, Matrix.mulVec]
    ring
  rw [hexp]
  have hxx : 0 < x 0 ^ 2 := by
    rcases lt_or_gt_of_ne hx0 with h | h <;> nlinarith
  exact mul_pos h00 hxx

/-- Real symmetry gives entry symmetry. -/
theorem isHermitian_entry_symm {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.IsHermitian) (a b : Fin m) : M a b = M b a := by
  have := congrFun (congrFun hM.eq b) a
  simpa [Matrix.conjTranspose_apply] using this

/-- The layer Schur complement of a real symmetric matrix is symmetric. -/
theorem isHermitian_schurOfLeading {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.IsHermitian) (l j : ℕ) (hlj : l + j ≤ m) :
    (schurOfLeading M l j hlj).IsHermitian := by
  have hl : l ≤ m := le_trans (Nat.le_add_right l j) hlj
  rw [schurOfLeading_def M l j hlj hl]
  have hAinvH : ((leadingPrincipal M hl)⁻¹).IsHermitian :=
    (IsHermitian.submatrix hM _).inv
  apply Matrix.IsHermitian.sub
  · exact IsHermitian.submatrix hM _
  · have hC : M.submatrix (tailEmb l j hlj) (Fin.castLE hl)
        = (M.submatrix (Fin.castLE hl) (tailEmb l j hlj))ᴴ := by
      ext a b
      simp [Matrix.conjTranspose_apply, Matrix.submatrix_apply,
        isHermitian_entry_symm hM]
    rw [hC]
    set Bb := M.submatrix (Fin.castLE hl) (tailEmb l j hlj)
    calc (Bbᴴ * (leadingPrincipal M hl)⁻¹ * Bb)ᴴ
        = Bbᴴ * ((leadingPrincipal M hl)⁻¹)ᴴ * Bb := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Bbᴴ * (leadingPrincipal M hl)⁻¹ * Bb := by rw [hAinvH.eq]

/-- **The converse Sylvester criterion** over `ℝ`: a symmetric matrix all
of whose leading principal minors are positive is positive definite.  Only
the easy direction (`PosDef → minors positive`) is in Mathlib. -/
theorem posDef_of_det_leadingPrincipal_pos :
    ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ), M.IsHermitian →
      (∀ k (hk : k ≤ m), 0 < k → 0 < (leadingPrincipal M hk).det) →
      M.PosDef := by
  intro m
  induction m with
  | zero =>
      intro M hM _
      apply Matrix.PosDef.of_dotProduct_mulVec_pos hM
      intro x hx
      exact absurd (funext fun i => i.elim0) hx
  | succ n ih =>
      intro M hM hminors
      set e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      have hl : n ≤ n + 1 := Nat.le_succ n
      have hA : (leadingPrincipal M hl).PosDef := by
        apply ih
        · exact IsHermitian.submatrix hM _
        · intro k hk hk0
          exact hminors k (le_trans hk hl) hk0
      have hAdet : IsUnit (leadingPrincipal M hl).det :=
        isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
      -- block decomposition of M itself (l = n, j = 1)
      have hre := leadingPrincipal_submatrix_finSumFinEquiv
        M n 1 (le_refl (n + 1)) hl
      set Bblk := M.submatrix (Fin.castLE hl) (tailEmb n 1 (le_refl (n + 1)))
        with hBblk_def
      set Cblk := M.submatrix (tailEmb n 1 (le_refl (n + 1))) (Fin.castLE hl)
        with hCblk_def
      set Dblk := M.submatrix (tailEmb n 1 (le_refl (n + 1)))
        (tailEmb n 1 (le_refl (n + 1))) with hDblk_def
      have hLPtop : leadingPrincipal M (le_refl (n + 1)) = M := rfl
      have hMe : M.submatrix e e
          = Matrix.fromBlocks (leadingPrincipal M hl) Bblk Cblk Dblk := by
        rw [← hLPtop]
        exact hre
      have hC : Cblk = Bblkᴴ := by
        ext a b
        simp [hBblk_def, hCblk_def, Matrix.conjTranspose_apply,
          Matrix.submatrix_apply, isHermitian_entry_symm hM]
      -- positivity of the Schur complement from the quotient identity
      have hquot := det_leadingPrincipal_eq_mul_det_schurOfLeading
        M n 1 (le_refl (n + 1)) hl hAdet
      have hDetM : 0 < (leadingPrincipal M (le_refl (n + 1))).det :=
        hminors (n + 1) (le_refl _) (Nat.succ_pos n)
      have hSchurDet : 0 < (schurOfLeading M n 1 (le_refl (n + 1))).det := by
        have h1 : 0 < (leadingPrincipal M hl).det
            * (schurOfLeading M n 1 (le_refl (n + 1))).det := by
          rw [← hquot]; exact hDetM
        nlinarith [hA.det_pos, h1]
      have hSchurPos : (schurOfLeading M n 1 (le_refl (n + 1))).PosDef :=
        posDef_fin_one_of_det_pos
          (isHermitian_schurOfLeading hM n 1 (le_refl (n + 1))) hSchurDet
      -- assemble: fromBlocks PosDef from Schur PosDef, then transport back
      have hSchurEq : schurOfLeading M n 1 (le_refl (n + 1))
          = Dblk - Bblkᴴ * (leadingPrincipal M hl)⁻¹ * Bblk := by
        rw [schurOfLeading_def M n 1 (le_refl (n + 1)) hl, ← hC]
      have hblocks :
          (Matrix.fromBlocks (leadingPrincipal M hl) Bblk Bblkᴴ Dblk).PosDef := by
        rw [VOA.fromBlocks_posDef_iff_schur₁₁ Bblk Dblk hA]
        rw [← hSchurEq]
        exact hSchurPos
      have hMe' : M.submatrix e e
          = Matrix.fromBlocks (leadingPrincipal M hl) Bblk Bblkᴴ Dblk := by
        rw [hMe, hC]
      have hMsub : (M.submatrix e e).PosDef := by
        rw [hMe']; exact hblocks
      have := hMsub.submatrix (Equiv.injective e.symm)
      have hsub2 : (M.submatrix e e).submatrix e.symm e.symm = M := by
        ext a b
        simp [Matrix.submatrix_apply]
      rwa [hsub2] at this

end Sylvester

section Layers

open scoped ComplexOrder

variable {m : ℕ}

/-- Leading corners of the layer Schur complement are layer Schur complements:
`(Schur of leading l in leading (l+j))` cut to its first `i` rows and columns
is `Schur of leading l in leading (l+i)`. -/
theorem leadingPrincipal_schurOfLeading
    {K : Type*} [Field K] (M : Matrix (Fin m) (Fin m) K) (l i j : ℕ)
    (hij : i ≤ j) (hlj : l + j ≤ m) (hli : l + i ≤ m) :
    leadingPrincipal (schurOfLeading M l j hlj) hij
      = schurOfLeading M l i hli := by
  have hl : l ≤ m := le_trans (Nat.le_add_right l j) hlj
  rw [schurOfLeading_def M l j hlj hl, schurOfLeading_def M l i hli hl]
  ext a b
  have hemb : ∀ (c : Fin i), tailEmb l j hlj (Fin.castLE hij c)
      = tailEmb l i hli c := fun c => Fin.ext (by simp)
  simp only [leadingPrincipal_apply, Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.mul_apply]
  rw [hemb a, hemb b]

/-- The determinant of the layer Schur complement is the minor quotient. -/
theorem det_schurOfLeading_eq_div
    (M : Matrix (Fin m) (Fin m) ℝ) (l j : ℕ) (hlj : l + j ≤ m) (hl : l ≤ m)
    (hdet : (leadingPrincipal M hl).det ≠ 0) :
    (schurOfLeading M l j hlj).det
      = (leadingPrincipal M hlj).det / (leadingPrincipal M hl).det := by
  have hquot := det_leadingPrincipal_eq_mul_det_schurOfLeading
    M l j hlj hl (isUnit_iff_ne_zero.mpr hdet)
  field_simp
  linarith [hquot]

/-- **The layer lemma (positive case).**  If the leading `l`-minor is
nonzero (e.g. `l = 0`) and every relative minor in the range `(l, l+j]` is
positive, the layer Schur complement is positive definite.  Only `D_l ≠ 0` is
needed (the ratios carry the sign information); an earlier version assumed
`0 < D_l` (register entry 90). -/
theorem schurOfLeading_posDef_of_sign_ratios
    (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsHermitian) (l j : ℕ)
    (hlj : l + j ≤ m) (hl : l ≤ m)
    (hDl : (leadingPrincipal M hl).det ≠ 0)
    (hratios : ∀ i (hi0 : 0 < i) (hli : l + i ≤ m), i ≤ j →
      0 < (leadingPrincipal M hli).det / (leadingPrincipal M hl).det) :
    (schurOfLeading M l j hlj).PosDef := by
  apply posDef_of_det_leadingPrincipal_pos
  · exact isHermitian_schurOfLeading hM l j hlj
  · intro i hi hi0
    have hli : l + i ≤ m := le_trans (by omega) hlj
    rw [leadingPrincipal_schurOfLeading M l i j hi hlj hli,
      det_schurOfLeading_eq_div M l i hli hl hDl]
    exact hratios i hi0 hli hi

/-- **The layer lemma (negative case).**  If the leading `l`-minor is
nonzero and every relative minor in the range `(l, l+j]` has the alternating
sign `(-1)^i`, the layer Schur complement is negative definite (its negation is
positive definite).  Only `D_l ≠ 0` is needed; an earlier version assumed
`0 < D_l` (register entry 90). -/
theorem schurOfLeading_negDef_of_sign_ratios
    (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsHermitian) (l j : ℕ)
    (hlj : l + j ≤ m) (hl : l ≤ m)
    (hDl : (leadingPrincipal M hl).det ≠ 0)
    (hratios : ∀ i (hi0 : 0 < i) (hli : l + i ≤ m), i ≤ j →
      0 < (-1 : ℝ) ^ i
        * ((leadingPrincipal M hli).det / (leadingPrincipal M hl).det)) :
    (-(schurOfLeading M l j hlj)).PosDef := by
  apply posDef_of_det_leadingPrincipal_pos
  · simpa using (isHermitian_schurOfLeading hM l j hlj).neg
  · intro i hi hi0
    have hli : l + i ≤ m := le_trans (by omega) hlj
    have hneg : leadingPrincipal (-(schurOfLeading M l j hlj)) hi
        = -(leadingPrincipal (schurOfLeading M l j hlj) hi) := rfl
    rw [hneg, Matrix.det_neg,
      leadingPrincipal_schurOfLeading M l i j hi hlj hli,
      det_schurOfLeading_eq_div M l i hli hl hDl]
    have hrat := hratios i hi0 hli hi
    rw [Fintype.card_fin]
    exact hrat.trans_eq (by ring)

end Layers

end FlagMinors

end VOA
