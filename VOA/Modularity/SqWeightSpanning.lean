/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ChangeCoord

/-!
# The `L[0]`-grading spans: `SqWeightSpansTop`  (TASK A)

The last input to `DirectSum.IsInternal (sqWeightSpace W)`: the square-bracket weight spaces span.
(Independence is already free — `sqWeightSpace_iSupIndep`.)

## The argument

Write `T := L[0] = L₀ + N` with `N` **strictly grade-lowering**: for `x ∈ 𝒱ⱼ`,
`T x − j·x ∈ 𝒱^{≤j−1}` (`Lsq_zero_sub_smul_mem_gradeLE`, from `Lsq_zero_apply` +
`sqBracketCoeff_zero_diag = 1` + `sqBracketCoeff_zero_of_neg` + `L_mem_grading`).

⚠ `L₀ + N` with `N` nilpotent is **not** diagonalizable in general (`L₀ = 0`, `N` a Jordan block).
What makes it true here is that `L₀` acts by **distinct** scalars on distinct grades.  We exploit that
directly, avoiding any normal-form conjugation:

* **Surjectivity below the diagonal** (`sub_smul_surj`): for `e < d`, the operator `T − d` maps
  `𝒱^{≤e}` **onto** `𝒱^{≤e}`.  Induction on `e`: split `w = w_e + w'` (`gradeLE_split`), solve the top
  piece with `y₀ := (e−d)⁻¹·w_e` — legitimate precisely because `e − d ≠ 0` — and absorb the
  strictly-lower remainder by the inductive hypothesis.  No finite-dimensionality needed.
* **Spanning** (`gradeLE_le_iSup_sqWeightSpace`): induction on `d`.  For `x ∈ 𝒱_d`, put
  `w := T x − d·x ∈ 𝒱^{≤d−1}`; by surjectivity pick `y ∈ 𝒱^{≤d−1}` with `(T−d)y = w`.  Then
  `(T−d)(x−y) = 0`, so `x − y` is a genuine `L[0]`-**eigenvector** of eigenvalue `d`, while
  `y ∈ 𝒱^{≤d−1}` is covered by the inductive hypothesis.  Hence `x ∈ ⨆ k, 𝒱_{[k]}`.

Both inductions run over `ℕ` via `e = n − 1`, bottoming out at `𝒱^{≤−1} = ⊥` (VOA4 `positivity`).

## Status
`SqWeightSpansTop` is proved, hence so is `DirectSum.IsInternal (sqWeightSpace W)`
(`sqWeightSpace_isInternal`).  Axiom-clean, `pbw`-free.

## References
* Gannon §5.3.5 (5.3.17a, 5.3.18a); Zhu, J. AMS 9 (1996) §4.
-/

namespace VOA

open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Splitting off the top grade -/

/-- `𝒱^{≤e} = 𝒱_e ⊔ 𝒱^{≤e−1}`. -/
theorem gradeLE_split (W : VertexOperatorAlgebra 𝒱) (e : ℤ) :
    gradeLE W e = W.grading e ⊔ gradeLE W (e - 1) := by
  refine le_antisymm (iSup_le fun j => ?_) (sup_le ?_ (gradeLE_mono W (by omega)))
  · rcases eq_or_lt_of_le j.2 with h | h
    · rw [h]; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup_of_le (⟨(j : ℤ), by omega⟩ : {j : ℤ // j ≤ e - 1}) le_rfl)
  · intro x hx
    exact mem_gradeLE_of_mem_grading W le_rfl hx

/-! ## Strict triangularity of `L[0]` -/

/-- **`L[0]` is `L₀` plus a strictly grade-lowering operator**: for `x ∈ 𝒱ⱼ`,
`L[0]x − j·x ∈ 𝒱^{≤j−1}`.  (The `a = 0` term of `L[0] = Σ_a d[0,a]L_a` is `d[0,0]·L₀x = j·x`; the
`a < 0` terms vanish; each `a ≥ 1` term lands in `𝒱_{j−a} ⊆ 𝒱^{≤j−1}`.) -/
theorem Lsq_zero_sub_smul_mem_gradeLE (W : VertexOperatorAlgebra 𝒱) {j : ℤ} {x : 𝒱}
    (hx : x ∈ W.grading j) : Lsq W 0 x - (j : ℂ) • x ∈ gradeLE W (j - 1) := by
  classical
  have hfin : (Function.support fun a : ℤ =>
      sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.L a x).Finite := dL_support_finite W 0 x
  have hsub : (Function.support fun a : ℤ => sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.L a x)
      ⊆ ↑(insert (0 : ℤ) hfin.toFinset) := by
    intro a ha
    simp only [Finset.coe_insert, Set.mem_insert_iff]
    exact Or.inr ((Set.Finite.mem_toFinset hfin).mpr ha)
  rw [Lsq_zero_apply, finsum_eq_finsetSum_of_support_subset _ hsub,
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self (0 : ℤ) hfin.toFinset),
    show sqBracketCoeffZ 2 (0 + 1) ((0 : ℤ) + 1) • W.L 0 x = (j : ℂ) • x from by
      rw [sqBracketCoeff_zero_diag, one_smul, W.L_zero_grading x hx],
    add_sub_cancel_left]
  refine Submodule.sum_mem _ (fun a ha => ?_)
  have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
  by_cases hneg : a < 0
  · rw [sqBracketCoeff_zero_of_neg hneg, zero_smul]
    exact Submodule.zero_mem _
  · push_neg at hneg
    exact Submodule.smul_mem _ _
      (mem_gradeLE_of_mem_grading W (by omega) (L_mem_grading W hx a))

/-! ## `T − d` is surjective on the strictly-lower filtration -/

/-- **Surjectivity below the diagonal**: for every `e < d`, `L[0] − d` maps `𝒱^{≤e}` **onto**
`𝒱^{≤e}`.  Induction on `e` (as `n − 1`): the top piece is solved by dividing by `e − d ≠ 0` — this is
exactly where "`L₀` has distinct eigenvalues on distinct grades" enters — and the strictly-lower
remainder is absorbed by the inductive hypothesis. -/
theorem sub_smul_surj (W : VertexOperatorAlgebra 𝒱) (d : ℤ) :
    ∀ (n : ℕ) (w : 𝒱), w ∈ gradeLE W ((n : ℤ) - 1) → ((n : ℤ) - 1 < d) →
      ∃ y ∈ gradeLE W ((n : ℤ) - 1), Lsq W 0 y - (d : ℂ) • y = w := by
  intro n
  induction n with
  | zero =>
      intro w hw _
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by norm_num, gradeLE_eq_bot W (by norm_num)] at hw
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [(Submodule.mem_bot ℂ).mp hw, map_zero, smul_zero, sub_zero]
  | succ m ih =>
      intro w hw hlt
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) from by push_cast; ring] at hw hlt ⊢
      rw [gradeLE_split W (m : ℤ)] at hw
      obtain ⟨wm, hwm, w', hw', rfl⟩ := Submodule.mem_sup.mp hw
      have hc : ((m : ℤ) : ℂ) - ((d : ℤ) : ℂ) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast fun h => absurd h (by omega : (m : ℤ) ≠ d)
      set y₀ : 𝒱 := (((m : ℤ) : ℂ) - ((d : ℤ) : ℂ))⁻¹ • wm with hy₀def
      have hy₀mem : y₀ ∈ W.grading (m : ℤ) := Submodule.smul_mem _ _ hwm
      have hy₀c : (((m : ℤ) : ℂ) - ((d : ℤ) : ℂ)) • y₀ = wm := by
        rw [hy₀def, smul_smul, mul_inv_cancel₀ hc, one_smul]
      -- the strictly-lower remainder produced by `y₀`
      have hrem : Lsq W 0 y₀ - ((m : ℤ) : ℂ) • y₀ ∈ gradeLE W ((m : ℤ) - 1) :=
        Lsq_zero_sub_smul_mem_gradeLE W hy₀mem
      have hy₀eq : Lsq W 0 y₀ - ((d : ℤ) : ℂ) • y₀
          = wm + (Lsq W 0 y₀ - ((m : ℤ) : ℂ) • y₀) := by
        rw [← hy₀c, sub_smul]
        abel
      obtain ⟨y₁, hy₁mem, hy₁eq⟩ :=
        ih (w' - (Lsq W 0 y₀ - ((m : ℤ) : ℂ) • y₀)) (Submodule.sub_mem _ hw' hrem) (by omega)
      refine ⟨y₀ + y₁, ?_, ?_⟩
      · exact Submodule.add_mem _ (mem_gradeLE_of_mem_grading W le_rfl hy₀mem)
          (gradeLE_mono W (by omega) hy₁mem)
      · rw [map_add, smul_add,
          show Lsq W 0 y₀ + Lsq W 0 y₁ - (((d : ℤ) : ℂ) • y₀ + ((d : ℤ) : ℂ) • y₁)
            = (Lsq W 0 y₀ - ((d : ℤ) : ℂ) • y₀) + (Lsq W 0 y₁ - ((d : ℤ) : ℂ) • y₁) from by abel,
          hy₀eq, hy₁eq]
        abel

/-! ## Spanning -/

/-- **Each filtration step is covered by the `L[0]`-eigenspaces.**  For `x ∈ 𝒱_d`, subtracting the
solution `y` of `(T−d)y = (T−d)x` (which exists in `𝒱^{≤d−1}` by `sub_smul_surj`) produces a genuine
eigenvector `x − y`. -/
theorem gradeLE_le_iSup_sqWeightSpace (W : VertexOperatorAlgebra 𝒱) :
    ∀ (n : ℕ), gradeLE W ((n : ℤ) - 1) ≤ ⨆ k : ℂ, sqWeightSpace W k := by
  intro n
  induction n with
  | zero =>
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by norm_num, gradeLE_eq_bot W (by norm_num)]
      exact bot_le
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) from by push_cast; ring, gradeLE_split W (m : ℤ)]
      refine sup_le (fun x hx => ?_) ih
      -- `x ∈ 𝒱_m`; solve away the strictly-lower part
      have hw : Lsq W 0 x - ((m : ℤ) : ℂ) • x ∈ gradeLE W ((m : ℤ) - 1) :=
        Lsq_zero_sub_smul_mem_gradeLE W hx
      obtain ⟨y, hymem, hyeq⟩ :=
        sub_smul_surj W (m : ℤ) m (Lsq W 0 x - ((m : ℤ) : ℂ) • x)
          (by rw [show ((m : ℕ) : ℤ) - 1 = (m : ℤ) - 1 from by push_cast; ring]; exact hw)
          (by push_cast; omega)
      have hymem' : y ∈ gradeLE W ((m : ℤ) - 1) := by
        rw [show ((m : ℕ) : ℤ) - 1 = (m : ℤ) - 1 from by push_cast; ring] at hymem
        exact hymem
      -- `x − y` is a genuine eigenvector of eigenvalue `m`
      have heig : x - y ∈ sqWeightSpace W ((m : ℤ) : ℂ) := by
        rw [mem_sqWeightSpace_iff, map_sub, smul_sub]
        have : Lsq W 0 y - ((m : ℤ) : ℂ) • y = Lsq W 0 x - ((m : ℤ) : ℂ) • x := hyeq
        linear_combination (norm := abel) -this
      have hx' : x = (x - y) + y := by abel
      rw [hx']
      exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem ((m : ℤ) : ℂ) heig) (ih hymem')

/-- **`SqWeightSpansTop`.**  The square-bracket weight spaces span `𝒱`. -/
theorem sqWeightSpansTop_holds (W : VertexOperatorAlgebra 𝒱) : SqWeightSpansTop W := by
  refine eq_top_iff.mpr (fun x _ => ?_)
  obtain ⟨d, hd⟩ := exists_mem_gradeLE W x
  exact gradeLE_le_iSup_sqWeightSpace W (d + 1).toNat
    (gradeLE_mono W (show d ≤ (((d + 1).toNat : ℤ)) - 1 by omega) hd)

/-- **THE `L[0]`-GRADING** (Gannon 5.3.17a): `𝒱` is the internal direct sum of its square-bracket
weight spaces.  Independence is free (eigenspaces); spanning is `sqWeightSpansTop_holds`.

This is the grading Zhu's Theorem 5.3.8 is quantified over — the exponent `n` in `(cτ+d)ⁿ` is the
**square-bracket** weight. -/
theorem sqWeightSpace_isInternal (W : VertexOperatorAlgebra 𝒱) :
    DirectSum.IsInternal (sqWeightSpace W) :=
  sqWeightSpace_isInternal_of_spansTop W (sqWeightSpansTop_holds W)

end VOA
