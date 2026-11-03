/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.Simple
import Mathlib.Algebra.Lie.Classical

/-!
# `sl_n(ℂ)` is simple

Mathlib defines `LieAlgebra.SpecialLinear.sl n R` but (as of v4.30) proves no simplicity.  This file
proves `LieAlgebra.IsSimple ℂ (sl n ℂ)` for every finite index type with at least two elements, by the
root-vector argument that the lattice Lie algebras will also need:

* `lie_E_lie_E`: `⁅E_ij, ⁅E_ij, v⁆⁆ = -2 v_ji E_ij` (extracts an off-diagonal entry);
* `lie_E_diag`: on a diagonal `v`, `⁅E_ij, v⁆ = (v_jj - v_ii) E_ij`;
* from one `E_ij` in an ideal, all `E_kl` (`E_mem_all`), hence the whole algebra.

Consequently `universalAffineVOA` / `standardAffineVOA` apply to `sl_n` for every `n ≥ 2`.
-/

namespace VOA.AffineGeneral.SlSimple

open LieAlgebra LieAlgebra.SpecialLinear

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The root vector `E_ij` (`i ≠ j`). -/
abbrev E (i j : n) (h : i ≠ j) : sl n ℂ := single i j h 1

theorem val_E (i j : n) (h : i ≠ j) : (E i j h).val = Matrix.single i j 1 := rfl

theorem val_lie (a b : sl n ℂ) : ⁅a, b⁆.val = a.val * b.val - b.val * a.val := sl_bracket _ _ _ _

theorem val_smul (c : ℂ) (a : sl n ℂ) : (c • a).val = c • a.val := rfl

/-- `⁅E_ij, ⁅E_ij, v⁆⁆ = -2 v_ji E_ij`. -/
theorem lie_E_lie_E (i j : n) (h : i ≠ j) (v : sl n ℂ) :
    ⁅E i j h, ⁅E i j h, v⁆⁆ = (-2 * v.val j i) • E i j h := by
  apply Subtype.ext
  rw [val_lie, val_lie, val_smul, val_E]
  have hSS : (Matrix.single i j (1 : ℂ)) * Matrix.single i j 1 = 0 := by
    simp [Matrix.single_mul_single_of_ne, h.symm]
  have hSvS : Matrix.single i j (1 : ℂ) * v.val * Matrix.single i j 1 = Matrix.single i j (v.val j i) := by
    rw [Matrix.single_mul_mul_single]; simp
  rw [mul_sub, sub_mul, ← mul_assoc, hSS, zero_mul, mul_assoc v.val, hSS, mul_zero, ← mul_assoc,
    hSvS]
  rw [show Matrix.single i j (v.val j i) = (v.val j i) • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  module

/-- On a diagonal `v`, `⁅E_ij, v⁆ = (v_jj - v_ii) E_ij`. -/
theorem lie_E_diag (i j : n) (h : i ≠ j) (v : sl n ℂ) (hv : ∀ a b, a ≠ b → v.val a b = 0) :
    ⁅E i j h, v⁆ = (v.val j j - v.val i i) • E i j h := by
  apply Subtype.ext
  rw [val_lie, val_smul, val_E]
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = j
  · rw [ha, hb]
    simp [Matrix.sub_apply, Matrix.smul_apply]
  · rw [ha]
    simp [Matrix.sub_apply, Matrix.smul_apply, hb, Ne.symm hb, hv j b (Ne.symm hb), Matrix.single_apply]
  · rw [hb]
    simp [Matrix.sub_apply, Matrix.smul_apply, ha, Ne.symm ha, hv a i ha, Matrix.single_apply]
  · simp [Matrix.sub_apply, Matrix.smul_apply, ha, hb, Ne.symm ha, Ne.symm hb, Matrix.single_apply]

/-- `⁅E_ij, E_jl⁆ = E_il` for `l ≠ i`. -/
theorem lie_E_E_row (i j l : n) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    ⁅E i j hij, E j l hjl⁆ = E i l hil := by
  apply Subtype.ext
  rw [val_lie, val_E, val_E, val_E, Matrix.single_mul_single_same, one_mul]
  simp [Matrix.single_mul_single_of_ne, Ne.symm hil]

/-- `⁅E_ij, E_ji⁆ = E_ii - E_jj`, and `⁅E_ji, E_ii - E_jj⁆ = 2 E_ji`. -/
theorem lie_E_E_back (i j : n) (hij : i ≠ j) :
    ⁅E j i hij.symm, ⁅E i j hij, E j i hij.symm⁆⁆ = (2 : ℂ) • E j i hij.symm := by
  apply Subtype.ext
  rw [val_lie, val_lie, val_smul, val_E, val_E]
  simp [mul_sub, sub_mul, Matrix.single_mul_single_of_ne, hij, hij.symm, two_smul]

variable (I : LieIdeal ℂ (sl n ℂ))

theorem mem_right {x : sl n ℂ} (y : sl n ℂ) (hx : x ∈ I) : ⁅y, x⁆ ∈ I := I.lie_mem hx

theorem mem_left {x : sl n ℂ} (y : sl n ℂ) (hx : x ∈ I) : ⁅x, y⁆ ∈ I := by
  rw [← lie_skew]; exact I.neg_mem (I.lie_mem hx)

theorem E_mem_flip {i j : n} (hij : i ≠ j) (hE : E i j hij ∈ I) : E j i hij.symm ∈ I := by
  have hH : ⁅E i j hij, E j i hij.symm⁆ ∈ I := mem_left I _ hE
  have h2 : ⁅E j i hij.symm, ⁅E i j hij, E j i hij.symm⁆⁆ ∈ I := mem_right I _ hH
  rw [lie_E_E_back] at h2
  have := I.smul_mem (2⁻¹ : ℂ) h2
  rwa [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul] at this

theorem E_mem_row {i j : n} (hij : i ≠ j) (hE : E i j hij ∈ I) (l : n) (hjl : j ≠ l)
    (hil : i ≠ l) : E i l hil ∈ I := by
  rw [← lie_E_E_row i j l hij hjl hil]
  exact mem_left I _ hE

theorem E_mem_col {i j : n} (hij : i ≠ j) (hE : E i j hij ∈ I) (k : n) (hki : k ≠ i)
    (hkj : k ≠ j) : E k j hkj ∈ I := by
  rw [← lie_E_E_row k i j hki hij hkj]
  exact mem_right I _ hE

/-- One root vector in an ideal gives all of them. -/
theorem E_mem_all {i j : n} (hij : i ≠ j) (hE : E i j hij ∈ I) (k l : n) (hkl : k ≠ l) :
    E k l hkl ∈ I := by
  have hE' := E_mem_flip I hij hE
  by_cases hki : k = i
  · subst hki
    by_cases hlj : l = j
    · subst hlj; exact hE
    · exact E_mem_row I hij hE l (Ne.symm hlj) hkl
  by_cases hkj : k = j
  · subst hkj
    by_cases hli : l = i
    · subst hli; exact hE'
    · exact E_mem_row I hij.symm hE' l (Ne.symm hli) hkl
  by_cases hlj : l = j
  · subst hlj; exact E_mem_col I hij hE k hki hkl
  by_cases hli : l = i
  · subst hli; exact E_mem_col I hij.symm hE' k hkj hkl
  exact E_mem_row I hkj (E_mem_col I hij hE k hki hkj) l (Ne.symm hlj) hkl

theorem trace_val (v : sl n ℂ) : Matrix.trace v.val = 0 := v.property

/-- A nonzero element of an ideal produces a root vector in it. -/
theorem exists_E_mem {v : sl n ℂ} (hv0 : v ≠ 0) (hv : v ∈ I) :
    ∃ i j, ∃ h : i ≠ j, E i j h ∈ I := by
  by_cases hoff : ∃ i j, i ≠ j ∧ v.val j i ≠ 0
  · obtain ⟨i, j, hij, hne⟩ := hoff
    refine ⟨i, j, hij, ?_⟩
    have h1 := mem_right I (E i j hij) (mem_right I (E i j hij) hv)
    rw [lie_E_lie_E] at h1
    have hc : (-2 * v.val j i) ≠ 0 := mul_ne_zero (by norm_num) hne
    have := I.smul_mem (-2 * v.val j i)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · push_neg at hoff
    have hdiag : ∀ a b, a ≠ b → v.val a b = 0 := fun a b hab => hoff b a (Ne.symm hab)
    -- some two diagonal entries differ
    have hex : ∃ i j, v.val i i ≠ v.val j j := by
      by_contra hall
      push_neg at hall
      apply hv0
      apply Subtype.ext
      ext a b
      by_cases hab : a = b
      · subst hab
        have ht := trace_val v
        rw [Matrix.trace] at ht
        simp only [Matrix.diag_apply] at ht
        have hsum : (∑ c, v.val c c) = (Fintype.card n : ℂ) * v.val a a := by
          rw [Finset.sum_congr rfl (fun c _ => hall c a), Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
        rw [hsum] at ht
        have hcard : (Fintype.card n : ℂ) ≠ 0 := by
          exact_mod_cast (Fintype.card_pos_iff.mpr ⟨a⟩).ne'
        simpa using (mul_eq_zero.mp ht).resolve_left hcard
      · simp [hdiag a b hab]
    obtain ⟨i, j, hne⟩ := hex
    have hij : i ≠ j := fun h => hne (by rw [h])
    refine ⟨i, j, hij, ?_⟩
    have h1 := mem_right I (E i j hij) hv
    rw [lie_E_diag i j hij v hdiag] at h1
    have hc : (v.val j j - v.val i i) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have := I.smul_mem (v.val j j - v.val i i)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- The Cartan differences `E_aa - E_bb` lie in any ideal containing all root vectors. -/
theorem H_mem (hall : ∀ k l (h : k ≠ l), E k l h ∈ I) (a b : n) :
    singleSubSingle a b (1 : ℂ) ∈ I := by
  by_cases hab : a = b
  · subst hab
    have : singleSubSingle a a (1 : ℂ) = 0 := by apply Subtype.ext; simp
    rw [this]; exact I.zero_mem
  · have h := mem_left I (E b a (Ne.symm hab)) (hall a b hab)
    have heq : ⁅E a b hab, E b a (Ne.symm hab)⁆ = singleSubSingle a b (1 : ℂ) := by
      apply Subtype.ext
      rw [val_lie, val_E, val_E, val_singleSubSingle]
      simp
    rwa [heq] at h

/-- The off-diagonal root-vector part of `v`. -/
def offE (v : sl n ℂ) (a b : n) : sl n ℂ := if h : a = b then 0 else v.val a b • E a b h

theorem offE_apply (v : sl n ℂ) (a b x y : n) :
    (offE v a b).val x y = if a = b then 0 else v.val a b * (if x = a ∧ y = b then 1 else 0) := by
  unfold offE
  by_cases h : a = b
  · simp [h]
  · rw [dif_neg h, if_neg h, val_smul, val_E, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hx : x = a <;> by_cases hy : y = b <;> simp_all [eq_comm]

theorem sum_offE_apply (v : sl n ℂ) (x y : n) :
    (∑ a, ∑ b, (offE v a b).val x y) = if x = y then 0 else v.val x y := by
  simp only [offE_apply]
  rw [Finset.sum_eq_single x, Finset.sum_eq_single y]
  · by_cases hxy : x = y <;> simp [hxy]
  · intro b _ hb; split_ifs <;> simp_all
  · intro h; exact absurd (Finset.mem_univ y) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs <;> simp_all
  · intro h; exact absurd (Finset.mem_univ x) h

theorem sum_diag_apply (v : sl n ℂ) (i0 x y : n) :
    (∑ a, (v.val a a • singleSubSingle a i0 (1 : ℂ)).val x y) = if x = y then v.val x x else 0 := by
  have ht := trace_val v
  rw [Matrix.trace] at ht
  simp only [Matrix.diag_apply] at ht
  simp only [val_smul, val_singleSubSingle, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = i0
    · subst hx; simp [ht]
    · simp [Ne.symm hx]
  · have h1 : ∀ c : n, ¬(c = x ∧ c = y) := fun c h => hxy (h.1.symm.trans h.2)
    have h2 : ¬(i0 = x ∧ i0 = y) := fun h => hxy (h.1.symm.trans h.2)
    simp [h1, h2, hxy]

/-- Every traceless matrix is a combination of root vectors and Cartan differences. -/
theorem decompose (i0 : n) (v : sl n ℂ) :
    v = (∑ a, ∑ b, offE v a b) + ∑ a, v.val a a • singleSubSingle a i0 (1 : ℂ) := by
  apply Subtype.ext
  ext x y
  change v.val x y = ((∑ a, ∑ b, offE v a b).val + (∑ a, v.val a a • singleSubSingle a i0 (1 : ℂ)).val) x y
  rw [Matrix.add_apply, AddSubmonoidClass.coe_finset_sum, AddSubmonoidClass.coe_finset_sum,
    Matrix.sum_apply, Matrix.sum_apply]
  simp only [AddSubmonoidClass.coe_finset_sum, Matrix.sum_apply]
  rw [sum_offE_apply, sum_diag_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

theorem eq_top_of_E_mem (i0 : n) (hall : ∀ k l (h : k ≠ l), E k l h ∈ I) : I = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [decompose i0 v]
  refine I.add_mem (I.sum_mem fun a _ => I.sum_mem fun b _ => ?_)
    (I.sum_mem fun a _ => I.smul_mem _ (H_mem I hall a i0))
  unfold offE
  split_ifs with h
  · exact I.zero_mem
  · exact I.smul_mem _ (hall a b h)

/-- **`sl_n(ℂ)` is a simple Lie algebra** (for `n` with at least two elements). -/
instance instIsSimple [Nontrivial n] : LieAlgebra.IsSimple ℂ (sl n ℂ) where
  eq_bot_or_eq_top I := by
    by_cases h : I = ⊥
    · exact Or.inl h
    · right
      have hex : ∃ v ∈ I, v ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply h
        ext v
        constructor
        · intro hv; exact (LieSubmodule.mem_bot v).mpr (hcon v hv)
        · intro hv; rw [(LieSubmodule.mem_bot v).mp hv]; exact I.zero_mem
      obtain ⟨v, hv, hv0⟩ := hex
      obtain ⟨i, j, hij, hE⟩ := exists_E_mem I hv0 hv
      exact eq_top_of_E_mem I i (fun k l hkl => E_mem_all I hij hE k l hkl)
  non_abelian := by
    obtain ⟨i, j, hij⟩ := exists_pair_ne n
    intro hab
    have h0 : ⁅E i j hij, E j i hij.symm⁆ = 0 := hab.trivial _ _
    have h1 := congrArg (fun m : sl n ℂ => m.val i i) h0
    simp only [val_lie, val_E] at h1
    simp [hij, hij.symm] at h1

/-- **`V^k(sl_m)` with `κ = Killing/(2m)`** (so `h = m`, by `standardData_h`), for `k ≠ -m`.
This is the standard normalization because `h∨(sl_m) = m`, a classical fact not proved here.
The hypothesis `hm : (m : ℂ) ≠ 0` is redundant given `[Nontrivial (Fin m)]`. -/
def slAffineVOA (m : ℕ) [Nontrivial (Fin m)] (k : ℂ) (hk : k + (m : ℂ) ≠ 0) (hm : (m : ℂ) ≠ 0) :
    VertexOperatorAlgebra (Vacuum (standardData (sl (Fin m) ℂ) (m : ℂ) hm) k) :=
  standardAffineVOA (sl (Fin m) ℂ) (m : ℂ) hm k hk

end

end VOA.AffineGeneral.SlSimple
