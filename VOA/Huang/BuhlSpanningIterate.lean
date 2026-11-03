/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.BuhlSpanningWords

/-!
# Buhl's spanning theorem for modules, layer 2: the repeated-letter expansion

For `x ∈ 𝒱` put `x^{(0)} = x`, `x^{(j+1)} = x₍₋₁₎x^{(j)}` (`vPow`).  Iterating the module iterate
formula at `ℓ = −1`,

  `(x₍₋₁₎v)₍ₜ₎z = Σ_{i ≥ 0} x₍₋₁₋ᵢ₎ v₍ₜ₊ᵢ₎ z + Σ_{i ≥ 0} v₍ₜ₋₁₋ᵢ₎ x₍ᵢ₎ z`,

expresses `x^{(j)}₍ₜ₎z` as a combination of products of `j + 1` modes of `x` (in various orders)
whose mode indices sum to `t − j`.  `vPow_mode_sub_mem_Sp`: the **balanced** product
`x₍ₙ₎^{j+1} z` occurs exactly once, with coefficient `1`, when `t = (j+1)n + j`; every other
product has a mode multiset different from `{n^{j+1}}`.

This is the module form of the Gaberdiel–Neitzke / Buhl repeated-mode relation: when
`x^{(j)} ∈ C₂(𝒱)`, the balanced product is a combination of unbalanced ones up to lower grade.

No `sorry`, no axioms beyond Lean's three.
-/

namespace VOA.Huang.BuhlSpanning

open VOA VOA.Huang.FusionC2 VOA.Huang.ModuleC2
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `x^{(0)} = x`, `x^{(j+1)} = x₍₋₁₎ x^{(j)}`. -/
noncomputable def vPow (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) : ℕ → 𝒱
  | 0 => x
  | j + 1 => W.smul x (-1) (vPow W x j)

theorem vPow_mem_grading {x : 𝒱} {p : ℤ} (hx : x ∈ W.grading p) :
    ∀ j : ℕ, vPow W x j ∈ W.grading (((j : ℤ) + 1) * p) := by
  intro j
  induction j with
  | zero => simpa [vPow] using hx
  | succ j ih =>
      have := W.smul_mem_grading hx ih (-1)
      convert this using 2; push_cast; ring

variable (A : WeakModule W M) (x : 𝒱)

/-- The product `x₍c₁₎ ⋯ x₍c_r₎` (head outermost), as a linear map. -/
noncomputable def wordX : List ℤ → (M →ₗ[ℂ] M)
  | [] => LinearMap.id
  | a :: c => mode (A.YM x) a ∘ₗ wordX c

@[simp] theorem wordX_nil : wordX A x [] = LinearMap.id := rfl

@[simp] theorem wordX_cons (a : ℤ) (c : List ℤ) (z : M) :
    wordX A x (a :: c) z = mode (A.YM x) a (wordX A x c z) := rfl

theorem wordX_append (c d : List ℤ) (z : M) :
    wordX A x (c ++ d) z = wordX A x c (wordX A x d z) := by
  induction c with
  | nil => rfl
  | cons a c ih => simp [ih]

/-- The span of the **unbalanced** products: `j + 1` modes summing to `t − j`, not all `n`. -/
noncomputable def Sp (n : ℤ) (j : ℕ) (t : ℤ) (z : M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ c : List ℤ, c.length = j + 1 ∧ c.sum = t - j ∧
    c ≠ List.replicate (j + 1) n ∧ y = wordX A x c z}

variable {A x}

theorem wordX_mem_Sp {n : ℤ} {j : ℕ} {t : ℤ} {z : M} (c : List ℤ) (hlen : c.length = j + 1)
    (hsum : c.sum = t - j) (hne : c ≠ List.replicate (j + 1) n) : wordX A x c z ∈ Sp A x n j t z :=
  Submodule.subset_span ⟨c, hlen, hsum, hne, rfl⟩

/-- Prepending a mode `a`: `x₍ₐ₎ · Sp j t' ⊆ Sp (j+1) (a + t' + 1)`. -/
theorem Sp_prepend {n : ℤ} {j : ℕ} {t' : ℤ} {z : M} (a : ℤ) {y : M} (hy : y ∈ Sp A x n j t' z) :
    mode (A.YM x) a y ∈ Sp A x n (j + 1) (a + t' + 1) z := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨c, hlen, hsum, hne, rfl⟩ := hw
      have h := wordX_mem_Sp (A := A) (x := x) (n := n) (j := j + 1) (t := a + t' + 1) (z := z)
        (a :: c) (by simp [hlen]) (by simp [hsum]; ring) (by
          intro h
          rw [List.replicate_succ] at h
          exact hne (List.cons.inj h).2)
      simpa using h
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu

/-- Appending a mode `i` at the inside: `Sp j t' (x₍ᵢ₎z) ⊆ Sp (j+1) (t' + i + 1) z`. -/
theorem Sp_append {n : ℤ} {j : ℕ} {t' : ℤ} {z : M} (i : ℤ) :
    Sp A x n j t' (mode (A.YM x) i z) ≤ Sp A x n (j + 1) (t' + i + 1) z := by
  rw [Sp, Submodule.span_le]
  rintro _ ⟨c, hlen, hsum, hne, rfl⟩
  have h := wordX_mem_Sp (A := A) (x := x) (n := n) (j := j + 1) (t := t' + i + 1) (z := z)
    (c ++ [i]) (by simp [hlen]) (by simp [hsum]; ring) (by
      intro h
      rw [List.replicate_succ'] at h
      exact hne (List.append_inj_left' h (by simp)))
  rw [wordX_append] at h
  simpa using h

/-- The iterate coefficient at `ℓ = −1` is `1` for `i ≥ 0`. -/
theorem coeff_neg_one {i : ℤ} (hi : 0 ≤ i) : negOnePow i * cbz (-1) i = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) := ⟨i.toNat, by omega⟩
  rw [cbz_apply_nonneg _ hi, Int.toNat_natCast, gBinom_neg_one,
    VertexOperatorAlgebra.negOnePow_eq_zpow, zpow_natCast,
    ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **The repeated-letter expansion.**  `x^{(j)}₍ₜ₎z` equals `x₍ₙ₎^{j+1}z` (if
`t = (j+1)n + j`, else `0`) plus a combination of unbalanced products. -/
theorem vPow_mode_sub_mem_Sp (n : ℤ) : ∀ (j : ℕ) (t : ℤ) (z : M),
    mode (A.YM (vPow W x j)) t z
      - (if t = ((j : ℤ) + 1) * n + j then wordX A x (List.replicate (j + 1) n) z else 0)
      ∈ Sp A x n j t z := by
  intro j
  induction j with
  | zero =>
      intro t z
      by_cases ht : t = ((0 : ℕ) + 1 : ℤ) * n + (0 : ℕ)
      · rw [if_pos ht]
        have : t = n := by simpa using ht
        subst this
        simp [vPow]
      · rw [if_neg ht, sub_zero]
        have hne : t ≠ n := by intro h; apply ht; simp [h]
        have h := wordX_mem_Sp (A := A) (x := x) (n := n) (j := 0) (t := t) (z := z) [t]
          (by simp) (by simp) (by simpa using hne)
        simpa [vPow] using h
  | succ j IH =>
      intro t z
      classical
      set v := vPow W x j with hv
      have hiter := module_iterate0 A x v z (-1) t
      have hfin := VOA.Huang.ModuleC2.iterate_support_finite A x v z (-1) t
      set F : ℤ → M := fun i => (negOnePow i * cbz (-1) i) •
        (mode (A.YM x) (-1 - i) (mode (A.YM v) (t + i) z)
          - negOnePow (-1) • mode (A.YM v) (-1 + t - i) (mode (A.YM x) i z)) with hF
      set istar : ℤ := if n < 0 then -1 - n else n with histar
      have histar0 : 0 ≤ istar := by rw [histar]; split_ifs <;> omega
      set S : Finset ℤ := insert istar hfin.toFinset with hS
      have hsub : Function.support F ⊆ (S : Set ℤ) := by
        intro i hi; rw [hS, Finset.coe_insert]
        exact Set.mem_insert_of_mem _ (hfin.mem_toFinset.mpr hi)
      set special : M := if t = (((j + 1 : ℕ) : ℤ) + 1) * n + ((j + 1 : ℕ) : ℤ)
        then wordX A x (List.replicate (j + 1 + 1) n) z else 0 with hspecial
      have hvpow : vPow W x (j + 1) = W.smul x (-1) v := rfl
      rw [hvpow, hiter]
      change (∑ᶠ i, F i) - special ∈ _
      rw [finsum_eq_sum_of_support_subset F hsub]
      have hsum_ite : ∑ i ∈ S, (if i = istar then special else 0) = special := by
        rw [Finset.sum_ite_eq' S istar (fun _ => special), if_pos (Finset.mem_insert_self _ _)]
      rw [← hsum_ite, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rcases lt_or_ge i 0 with hi | hi
      · have hne : i ≠ istar := by omega
        rw [if_neg hne, sub_zero]
        simp only [hF, cbz_apply_neg _ hi, mul_zero, zero_smul]
        exact Submodule.zero_mem _
      -- `i ≥ 0`: split into the two families
      have hFi : F i = mode (A.YM x) (-1 - i) (mode (A.YM v) (t + i) z)
          + mode (A.YM v) (-1 + t - i) (mode (A.YM x) i z) := by
        simp only [hF, coeff_neg_one hi, one_smul]
        rw [show negOnePow (-1) = -1 by simp [negOnePow]]
        rw [neg_one_smul, sub_neg_eq_add]
      -- the inductive hypotheses, transported
      have hX := Sp_prepend (A := A) (x := x) (-1 - i) (IH (t + i) z)
      rw [map_sub, show (-1 - i) + (t + i) + 1 = t by ring] at hX
      have hY := Sp_append (A := A) (x := x) (n := n) (j := j) (t' := -1 + t - i) (z := z) i
        (IH (-1 + t - i) (mode (A.YM x) i z))
      rw [show (-1 + t - i) + i + 1 = t by ring] at hY
      set X0 := mode (A.YM x) (-1 - i) (if t + i = ((j : ℤ) + 1) * n + j then
        wordX A x (List.replicate (j + 1) n) z else 0) with hX0
      set Y0 := (if -1 + t - i = ((j : ℤ) + 1) * n + j then
        wordX A x (List.replicate (j + 1) n) (mode (A.YM x) i z) else 0) with hY0
      have hrest : X0 + Y0 - (if i = istar then special else 0) ∈ Sp A x n (j + 1) t z := by
        have hrep : ∀ k : ℕ, List.replicate (k + 1) n = n :: List.replicate k n :=
          fun k => List.replicate_succ ..
        by_cases hc1 : t + i = ((j : ℤ) + 1) * n + j
        · -- the outer family is active
          have hy0 : Y0 = 0 := by
            rw [hY0, if_neg]; intro h; omega
          rw [hy0, add_zero, hX0, if_pos hc1]
          by_cases hn : -1 - i = n
          · -- the balanced word
            have hist : i = istar := by rw [histar, if_pos (by omega)]; omega
            have htt : t = (((j + 1 : ℕ) : ℤ) + 1) * n + ((j + 1 : ℕ) : ℤ) := by
              push_cast; linear_combination hc1 + hn
            rw [if_pos hist, hspecial, if_pos htt, hn]
            have : mode (A.YM x) n (wordX A x (List.replicate (j + 1) n) z)
                = wordX A x (List.replicate (j + 1 + 1) n) z := by
              rw [hrep (j + 1), wordX_cons]
            rw [this, sub_self]; exact Submodule.zero_mem _
          · have hist : ¬ (i = istar ∧ t = (((j + 1 : ℕ) : ℤ) + 1) * n + ((j + 1 : ℕ) : ℤ)) := by
              rintro ⟨h1, h2⟩
              rw [histar] at h1
              split_ifs at h1 with hneg
              · exact hn (by omega)
              · push_cast at h2
                have h3 : 2 * n + 1 = 0 := by linear_combination hc1 - h2 - h1
                omega
            have hs0 : (if i = istar then special else 0) = 0 := by
              by_cases h1 : i = istar
              · rw [if_pos h1, hspecial, if_neg (fun h2 => hist ⟨h1, h2⟩)]
              · rw [if_neg h1]
            rw [hs0, sub_zero]
            have h := wordX_mem_Sp (A := A) (x := x) (n := n) (j := j + 1) (t := t) (z := z)
              ((-1 - i) :: List.replicate (j + 1) n) (by simp) (by
                simp only [List.sum_cons, List.sum_replicate, nsmul_eq_mul]
                push_cast; linear_combination -hc1) (by
                  intro h; rw [hrep (j + 1)] at h; exact hn (List.cons.inj h).1)
            simpa using h
        · have hx0 : X0 = 0 := by rw [hX0, if_neg hc1, map_zero]
          rw [hx0, zero_add]
          by_cases hc2 : -1 + t - i = ((j : ℤ) + 1) * n + j
          · rw [hY0, if_pos hc2]
            by_cases hn : i = n
            · have hist : i = istar := by
                rw [histar, if_neg (by omega)]; exact hn
              have htt : t = (((j + 1 : ℕ) : ℤ) + 1) * n + ((j + 1 : ℕ) : ℤ) := by
                push_cast; linear_combination hc2 + hn
              have hw : wordX A x (List.replicate (j + 1) n) (mode (A.YM x) n z)
                  = wordX A x (List.replicate (j + 1 + 1) n) z := by
                rw [List.replicate_succ' (n := j + 1), wordX_append]; rfl
              rw [if_pos hist, hspecial, if_pos htt, hn, hw, sub_self]
              exact Submodule.zero_mem _
            · have hist : ¬ (i = istar ∧
                  t = (((j + 1 : ℕ) : ℤ) + 1) * n + ((j + 1 : ℕ) : ℤ)) := by
                rintro ⟨h1, h2⟩
                rw [histar] at h1
                split_ifs at h1 with hneg
                · apply hc1; push_cast at h2; linear_combination h2 + h1
                · exact hn h1
              have hs0 : (if i = istar then special else 0) = 0 := by
                by_cases h1 : i = istar
                · rw [if_pos h1, hspecial, if_neg (fun h2 => hist ⟨h1, h2⟩)]
                · rw [if_neg h1]
              rw [hs0, sub_zero]
              have h := wordX_mem_Sp (A := A) (x := x) (n := n) (j := j + 1) (t := t) (z := z)
                (List.replicate (j + 1) n ++ [i]) (by simp) (by
                  simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul, List.sum_cons,
                    List.sum_nil, add_zero]
                  push_cast; linear_combination -hc2) (by
                    intro h
                    rw [show List.replicate (j + 1 + 1) n = List.replicate (j + 1) n ++ [n] from
                      List.replicate_succ' ..] at h
                    exact hn (by simpa using List.append_inj_right' h (by simp)))
              rw [wordX_append] at h
              simpa using h
          · have hy0 : Y0 = 0 := by rw [hY0, if_neg hc2]
            rw [hy0]
            have hist : ¬ (i = istar ∧ t = (((j + 1 : ℕ) : ℤ) + 1) * n + ((j + 1 : ℕ) : ℤ)) := by
              rintro ⟨h1, h2⟩
              rw [histar] at h1
              push_cast at h2
              split_ifs at h1 with hneg
              · exact hc1 (by linear_combination h2 + h1)
              · exact hc2 (by linear_combination h2 - h1)
            have hs0 : (if i = istar then special else 0) = 0 := by
              by_cases h1 : i = istar
              · rw [if_pos h1, hspecial, if_neg (fun h2 => hist ⟨h1, h2⟩)]
              · rw [if_neg h1]
            rw [hs0, sub_zero]; exact Submodule.zero_mem _
      have htot := Submodule.add_mem _ (Submodule.add_mem _ hX hY) hrest
      rw [hFi]
      convert htot using 1
      rw [hX0, hY0]
      abel

end VOA.Huang.BuhlSpanning
