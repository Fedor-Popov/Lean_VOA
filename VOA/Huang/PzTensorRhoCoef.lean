/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorRho
import VOA.Huang.AssocAssociator

/-!
# Coefficient identities for the reversed Jacobi identity of `ρ`

Pure combinatorics of `ℤ`-indexed finite sums with generalized binomial coefficients, used in
`PzTensorRhoJacobi`:

* `finsum_comm_box` — Fubini for `ℤ × ℤ`-indexed families supported in a box;
* `coef_lemma` — `Σ_i (−1)^i C(ℓ,i) C(n+i,s) ρ_i`
  `= Σ_t C(n,s−t)(−1)^t C(ℓ,t) Σ_k (−1)^k C(ℓ−t,k) ρ_{t+k}`
  (trinomial + Vandermonde; `ρ` eventually zero);
* `mix_lemma` — `(−1)^ℓ Σ_r Σ_t C(X,r−t)(−1)^t C(ℓ,t) Σ_j C(ℓ−t,j)(−1)^{ℓ−t−j} F(r,j)
  = Σ_j (−1)^j C(ℓ,j) Σ_r C(ℓ+X−j,r) F(r,j)`;
* `iter_lemma` — `Σ_r Σ_s C(m,r) C(n,s) Σ_i C(r,i) g(i, r+s−i)`
  `= Σ_i C(m,i) Σ_s C(m+n−i,s) g(i,s)`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorRho

open VOA
open scoped BigOperators

/-! ## Finite-support tools -/

theorem hfs_of {X : Type*} [Zero X] (f : ℤ → X) (lo hi : ℤ)
    (h : ∀ i, (i < lo ∨ hi < i) → f i = 0) : Function.HasFiniteSupport f :=
  fin_of_bound f lo hi fun i hi' => by
    by_contra hc
    exact hi' (h i (by omega))

theorem finsum_eq_Icc' {X : Type*} [AddCommMonoid X] (f : ℤ → X) (lo hi : ℤ)
    (h : ∀ i, (i < lo ∨ hi < i) → f i = 0) : ∑ᶠ i, f i = ∑ i ∈ Finset.Icc lo hi, f i :=
  finsum_eq_Icc f lo hi fun i hi' => by
    by_contra hc
    exact hi' (h i (by omega))

/-- **Fubini in a box.** -/
theorem finsum_comm_box {X : Type*} [AddCommMonoid X] (f : ℤ → ℤ → X) (lo₁ hi₁ lo₂ hi₂ : ℤ)
    (h : ∀ i j, (i < lo₁ ∨ hi₁ < i ∨ j < lo₂ ∨ hi₂ < j) → f i j = 0) :
    ∑ᶠ i, ∑ᶠ j, f i j = ∑ᶠ j, ∑ᶠ i, f i j := by
  have e1 : ∀ i, ∑ᶠ j, f i j = ∑ j ∈ Finset.Icc lo₂ hi₂, f i j := fun i =>
    finsum_eq_Icc' _ _ _ fun j hj => h i j (by omega)
  have e2 : ∀ j, ∑ᶠ i, f i j = ∑ i ∈ Finset.Icc lo₁ hi₁, f i j := fun j =>
    finsum_eq_Icc' _ _ _ fun i hi => h i j (by omega)
  simp only [e1, e2]
  rw [finsum_eq_Icc' _ lo₁ hi₁ (fun i hi => Finset.sum_eq_zero fun j _ => h i j (by omega)),
    finsum_eq_Icc' _ lo₂ hi₂ (fun j hj => Finset.sum_eq_zero fun i _ => h i j (by omega)),
    Finset.sum_comm]

/-- The sign is even: `(−1)^{2ℓ − j} = (−1)^j`. -/
theorem negOnePow_two_sub (ℓ j : ℤ) : negOnePow (2 * ℓ - j) = negOnePow j := by
  have h1 : negOnePow (2 * ℓ - j) * negOnePow j = negOnePow (2 * ℓ) := by
    rw [← negOnePow_add]; ring_nf
  have h2 : negOnePow (2 * ℓ) = 1 := by
    unfold negOnePow; rw [if_pos (even_two_mul ℓ)]
  have h3 := negOnePow_mul_self j
  calc negOnePow (2 * ℓ - j) = negOnePow (2 * ℓ - j) * (negOnePow j * negOnePow j) := by
        rw [h3, mul_one]
    _ = (negOnePow (2 * ℓ - j) * negOnePow j) * negOnePow j := by ring
    _ = negOnePow j := by rw [h1, h2, one_mul]

/-- Vandermonde in finsum form. -/
theorem vand (m n k : ℤ) : ∑ᶠ i : ℤ, cbz m i * cbz n (k - i) = cbz (m + n) k :=
  cbz_vandermonde m n k

/-- `C(r,i) = 0` for `0 ≤ r < i`. -/
theorem cbz_nat_lt {r i : ℤ} (hr : 0 ≤ r) (hri : r < i) : cbz r i = 0 := by
  obtain ⟨rN, rfl⟩ : ∃ k : ℕ, r = k := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
  obtain ⟨iN, rfl⟩ : ∃ k : ℕ, i = k := ⟨i.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  rw [cbz_apply_nonneg _ (by omega), Int.toNat_natCast,
    VertexOperatorAlgebra.gBinom_natCast_eq_zero (by omega)]

/-- The trinomial revision `C(ℓ,t) C(ℓ−t,i−t) = C(ℓ,i) C(i,t)` for all integers `t`, `i ≥ 0`. -/
theorem trinom (ℓ : ℤ) {i : ℤ} (hi : 0 ≤ i) (t : ℤ) :
    cbz ℓ t * cbz (ℓ - t) (i - t) = cbz ℓ i * cbz i t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [cbz_neg ht, cbz_neg ht]; ring
  · exact (AssocAssociator.cbz_trinomial ℓ hi ht).symm

/-- The swap `C(ℓ,t) C(ℓ−t,j) = C(ℓ,j) C(ℓ−j,t)` for all integers. -/
theorem swap (ℓ t j : ℤ) : cbz ℓ t * cbz (ℓ - t) j = cbz ℓ j * cbz (ℓ - j) t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [cbz_neg ht, cbz_neg ht]; ring
  rcases lt_or_ge j 0 with hj | hj
  · rw [cbz_neg hj, cbz_neg hj]; ring
  obtain ⟨t, rfl⟩ : ∃ n : ℕ, t = n := ⟨t.toNat, (Int.toNat_of_nonneg ht).symm⟩
  obtain ⟨j, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
  exact AssocAssociator.cbz_swap ℓ t j

/-! ## `coef_lemma` -/

/-- The coefficient identity behind the localization of the outside sums. -/
theorem coef_lemma (ℓ n s : ℤ) (ρ : ℤ → ℂ) (I : ℤ) (hρ : ∀ i, I ≤ i → ρ i = 0) :
    ∑ᶠ i, (negOnePow i * cbz ℓ i) * cbz (n + i) s * ρ i
      = ∑ᶠ t, cbz n (s - t) * (negOnePow t * cbz ℓ t)
          * ∑ᶠ k, (negOnePow k * cbz (ℓ - t) k) * ρ (t + k) := by
  -- shift the inner sum to the absolute index `i = t + k`
  have hin : ∀ t : ℤ, cbz n (s - t) * (negOnePow t * cbz ℓ t)
      * ∑ᶠ k, (negOnePow k * cbz (ℓ - t) k) * ρ (t + k)
      = ∑ᶠ i, cbz n (s - t) * (negOnePow t * cbz ℓ t)
          * ((negOnePow (i - t) * cbz (ℓ - t) (i - t)) * ρ i) := by
    intro t
    rw [mul_finsum, ← finsum_shift _ (-t)]
    refine finsum_congr fun i => ?_
    rw [show i + -t = i - t by ring, show t + (i - t) = i by ring]
  rw [finsum_congr hin]
  rw [finsum_comm_box _ 0 (max I 0) 0 (max I 0) (fun t i hti => by
    rcases hti with h | h | h | h
    · rw [cbz_neg h]; ring
    · rcases lt_or_ge i t with hit | hit
      · rw [cbz_neg (show i - t < 0 by omega)]; ring
      · rw [hρ i (by omega)]; ring
    · rcases lt_or_ge t 0 with ht | ht
      · rw [cbz_neg ht]; ring
      · rw [cbz_neg (show i - t < 0 by omega)]; ring
    · rw [hρ i (by omega)]; ring)]
  refine finsum_congr fun i => ?_
  rcases lt_or_ge i 0 with hi | hi
  · rw [cbz_neg hi]
    simp only [mul_zero, zero_mul]
    refine (finsum_eq_zero_of_forall_eq_zero fun t => ?_).symm
    rcases lt_or_ge t 0 with ht | ht
    · rw [cbz_neg ht]; ring
    · rw [cbz_neg (show i - t < 0 by omega)]; ring
  · have hterm : ∀ t : ℤ, cbz n (s - t) * (negOnePow t * cbz ℓ t)
        * ((negOnePow (i - t) * cbz (ℓ - t) (i - t)) * ρ i)
        = (negOnePow i * cbz ℓ i * ρ i) * (cbz i t * cbz n (s - t)) := by
      intro t
      have hs : negOnePow t * negOnePow (i - t) = negOnePow i := by
        rw [← negOnePow_add]; ring_nf
      have ht := trinom ℓ hi t
      linear_combination (cbz n (s - t) * ρ i * negOnePow i) * ht
        + (cbz n (s - t) * cbz ℓ t * cbz (ℓ - t) (i - t) * ρ i) * hs
    rw [finsum_congr hterm, ← mul_finsum, vand, add_comm i n]
    ring

/-! ## `mix_lemma` -/

/-- The mixed-term coefficient identity. -/
theorem mix_lemma (ℓ X : ℤ) (F : ℤ → ℤ → ℂ) (R J : ℤ)
    (hF : ∀ r j, (R ≤ r ∨ J ≤ j) → F r j = 0) :
    negOnePow ℓ * ∑ᶠ r, ∑ᶠ t, cbz X (r - t) * (negOnePow t * cbz ℓ t)
        * ∑ᶠ j, (cbz (ℓ - t) j * negOnePow (ℓ - t - j)) * F r j
      = ∑ᶠ j, (negOnePow j * cbz ℓ j) * ∑ᶠ r, cbz (ℓ + X - j) r * F r j := by
  -- push everything into one triple sum indexed by `(r, j, t)`
  have hL : negOnePow ℓ * ∑ᶠ r, ∑ᶠ t, cbz X (r - t) * (negOnePow t * cbz ℓ t)
        * ∑ᶠ j, (cbz (ℓ - t) j * negOnePow (ℓ - t - j)) * F r j
      = ∑ᶠ r, ∑ᶠ j, ∑ᶠ t, negOnePow ℓ * (cbz X (r - t) * (negOnePow t * cbz ℓ t)
          * ((cbz (ℓ - t) j * negOnePow (ℓ - t - j)) * F r j)) := by
    rw [mul_finsum]
    refine finsum_congr fun r => ?_
    rw [mul_finsum]
    simp only [mul_finsum]
    rw [finsum_comm_box _ 0 (max R 0) 0 (max J 0) (fun t j htj => by
      rcases htj with h | h | h | h
      · rw [cbz_neg h]; ring
      · rcases lt_or_ge r t with hrt | hrt
        · rw [cbz_neg (show r - t < 0 by omega)]; ring
        · rw [hF r j (Or.inl (by omega))]; ring
      · rw [cbz_neg h]; ring
      · rw [hF r j (Or.inr (by omega))]; ring)]
  rw [hL, finsum_comm_box _ 0 (max R 0) 0 (max J 0) (fun r j hrj => by
    refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
    rcases hrj with h | h | h | h
    · rcases lt_or_ge t 0 with ht | ht
      · rw [cbz_neg ht]; ring
      · rw [cbz_neg (show r - t < 0 by omega)]; ring
    · rw [hF r j (Or.inl (by omega))]; ring
    · rw [cbz_neg h]; ring
    · rw [hF r j (Or.inr (by omega))]; ring)]
  refine finsum_congr fun j => ?_
  rw [mul_finsum]
  refine finsum_congr fun r => ?_
  have hterm : ∀ t, negOnePow ℓ * (cbz X (r - t) * (negOnePow t * cbz ℓ t)
        * ((cbz (ℓ - t) j * negOnePow (ℓ - t - j)) * F r j))
      = (negOnePow j * cbz ℓ j * F r j) * (cbz (ℓ - j) t * cbz X (r - t)) := by
    intro t
    have hs : negOnePow ℓ * negOnePow t * negOnePow (ℓ - t - j) = negOnePow j := by
      rw [← negOnePow_add, ← negOnePow_add, show ℓ + t + (ℓ - t - j) = 2 * ℓ - j by ring,
        negOnePow_two_sub]
    have hw := swap ℓ t j
    linear_combination (cbz X (r - t) * F r j * negOnePow j) * hw
      + (cbz X (r - t) * cbz ℓ t * cbz (ℓ - t) j * F r j) * hs
  rw [finsum_congr hterm, ← mul_finsum, vand, show ℓ - j + X = ℓ + X - j by ring]
  ring

/-! ## `iter_lemma` -/

theorem iter_lemma_aux (m n : ℤ) (g : ℤ → ℤ → ℂ) (I S : ℤ)
    (hg : ∀ i s, (I ≤ i ∨ S ≤ s) → g i s = 0) :
    ∑ᶠ r, ∑ᶠ s, cbz m r * cbz n s * ∑ᶠ i, cbz r i * g i (r + s - i)
      = ∑ᶠ i, cbz m i * ∑ᶠ s, cbz (m + n - i) s * g i s := by
  set B : ℤ := max I 0 + max S 0 with hB
  -- put the `i`-sum outside
  have h1 : ∑ᶠ r, ∑ᶠ s, cbz m r * cbz n s * ∑ᶠ i, cbz r i * g i (r + s - i)
      = ∑ᶠ r, ∑ᶠ i, ∑ᶠ s, cbz m r * cbz n s * (cbz r i * g i (r + s - i)) := by
    refine finsum_congr fun r => ?_
    simp only [mul_finsum]
    rw [finsum_comm_box _ 0 B 0 B (fun s i hsi => by
      rcases hsi with h | h | h | h
      · rw [cbz_neg h]; ring
      · rcases lt_or_ge r i with hri | hri
        · rcases lt_or_ge i 0 with hi | hi
          · rw [cbz_neg hi]; ring
          · rcases lt_or_ge r 0 with hr | hr
            · rw [cbz_neg hr]; ring
            · rw [cbz_nat_lt hr hri]; ring
        · rw [hg i (r + s - i) (Or.inr (by omega))]; ring
      · rw [cbz_neg h]; ring
      · rw [hg i (r + s - i) (Or.inl (by omega))]; ring)]
  rw [h1]
  -- substitute `s ↦ s' = r + s − i`
  have h2 : ∀ r i, ∑ᶠ s, cbz m r * cbz n s * (cbz r i * g i (r + s - i))
      = ∑ᶠ s, cbz m r * cbz n (s + i - r) * (cbz r i * g i s) := by
    intro r i
    rw [← finsum_shift _ (i - r)]
    refine finsum_congr fun s => ?_
    rw [show r + (s + (i - r)) - i = s by ring, show s + (i - r) = s + i - r by ring]
  simp only [h2]
  -- reorder `(r, i, s) ↦ (i, s, r)`
  have hbox : ∀ r i s, (r < 0 ∨ 2 * B < r ∨ i < 0 ∨ B < i ∨ s < 0 ∨ B < s) →
      cbz m r * cbz n (s + i - r) * (cbz r i * g i s) = 0 := by
    intro r i s h
    rcases lt_or_ge r 0 with hr | hr
    · rw [cbz_neg hr]; ring
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_neg hi]; ring
    rcases le_or_gt I i with hI | hI
    · rw [hg i s (Or.inl hI)]; ring
    rcases le_or_gt S s with hS | hS
    · rw [hg i s (Or.inr hS)]; ring
    rcases lt_or_ge (s + i - r) 0 with hsir | hsir
    · rw [cbz_neg hsir]; ring
    rcases lt_or_ge s 0 with hs | hs
    · -- then `r ≤ s + i < i`, so `C(r,i) = 0`
      rw [cbz_nat_lt hr (by omega)]; ring
    · exfalso; omega
  rw [finsum_comm_box _ 0 (2 * B) 0 B (fun r i hri => by
    refine finsum_eq_zero_of_forall_eq_zero fun s => ?_
    rcases lt_or_ge s 0 with hs | hs
    · exact hbox r i s (by omega)
    rcases le_or_gt S s with hS | hS
    · rw [hg i s (Or.inr hS)]; ring
    rcases hri with h | h | h | h
    · exact hbox r i s (by omega)
    · rcases lt_or_ge (s + i - r) 0 with hsir | hsir
      · rw [cbz_neg hsir]; ring
      · rcases le_or_gt I i with hI | hI
        · rw [hg i s (Or.inl hI)]; ring
        · exfalso; omega
    · exact hbox r i s (by omega)
    · exact hbox r i s (by omega))]
  refine finsum_congr fun i => ?_
  rw [finsum_comm_box _ 0 (2 * B) (-1) B (fun r s hrs => by
    rcases hrs with h | h | h | h
    · exact hbox r i s (by omega)
    · rcases lt_or_ge s 0 with hs | hs
      · exact hbox r i s (by omega)
      rcases le_or_gt S s with hS | hS
      · rw [hg i s (Or.inr hS)]; ring
      rcases lt_or_ge (s + i - r) 0 with hsir | hsir
      · rw [cbz_neg hsir]; ring
      · rcases le_or_gt I i with hI | hI
        · rw [hg i s (Or.inl hI)]; ring
        · rcases lt_or_ge i 0 with hi | hi
          · rw [cbz_neg hi]; ring
          · exfalso; omega
    · exact hbox r i s (by omega)
    · exact hbox r i s (by omega))]
  rw [mul_finsum]
  refine finsum_congr fun s => ?_
  rcases lt_or_ge i 0 with hi | hi
  · rw [cbz_neg hi]
    simp only [zero_mul]
    exact finsum_eq_zero_of_forall_eq_zero fun r => by rw [cbz_neg hi]; ring
  -- `Σ_r C(m,r) C(r,i) C(n, s+i−r) = C(m,i) C(m−i+n, s)`
  have hterm : ∀ r, cbz m r * cbz n (s + i - r) * (cbz r i * g i s)
      = (cbz m i * g i s) * (cbz (m - i) (r - i) * cbz n (s - (r - i))) := by
    intro r
    rcases lt_or_ge r 0 with hr | hr
    · rw [cbz_neg hr, cbz_neg (show r - i < 0 by omega)]; ring
    have ht' := trinom m hr i
    rw [show s + i - r = s - (r - i) by ring]
    linear_combination (-(cbz n (s - (r - i)) * g i s)) * ht'
  rw [finsum_congr hterm, ← mul_finsum]
  have hv : ∑ᶠ r, cbz (m - i) (r - i) * cbz n (s - (r - i)) = cbz (m - i + n) s := by
    rw [← vand, ← finsum_shift _ i]
    exact finsum_congr fun r => by rw [show r + i - i = r by ring]
  rw [hv, show m - i + n = m + n - i by ring]
  ring

/-- The iterate-side reorganization. -/
theorem iter_lemma (m n : ℤ) (g : ℤ → ℤ → ℂ) (I S : ℤ)
    (hg : ∀ i s, 0 ≤ i → (I ≤ i ∨ S ≤ s) → g i s = 0) :
    ∑ᶠ r, ∑ᶠ s, cbz m r * cbz n s * ∑ᶠ i, cbz r i * g i (r + s - i)
      = ∑ᶠ i, cbz m i * ∑ᶠ s, cbz (m + n - i) s * g i s := by
  classical
  set g' : ℤ → ℤ → ℂ := fun i s => if 0 ≤ i then g i s else 0 with hg'def
  have hg' : ∀ i s, (I ≤ i ∨ S ≤ s) → g' i s = 0 := by
    intro i s h
    simp only [hg'def]
    split_ifs with hi
    · exact hg i s hi h
    · rfl
  have e1 : ∀ r s, ∑ᶠ i, cbz r i * g i (r + s - i) = ∑ᶠ i, cbz r i * g' i (r + s - i) := by
    intro r s
    refine finsum_congr fun i => ?_
    simp only [hg'def]
    split_ifs with hi
    · rfl
    · rw [cbz_neg (by omega)]; ring
  have e2 : ∀ i, cbz m i * ∑ᶠ s, cbz (m + n - i) s * g i s
      = cbz m i * ∑ᶠ s, cbz (m + n - i) s * g' i s := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_neg hi]; ring
    · congr 1
      exact finsum_congr fun s => by simp only [hg'def, if_pos hi]
  simp only [e1]
  rw [finsum_congr e2]
  exact iter_lemma_aux m n g' I S hg'

/-! ## Box tools for double and triple sums -/

theorem finsum2_Icc {X : Type*} [AddCommMonoid X] (H : ℤ → ℤ → X) (B : ℤ)
    (h : ∀ a b, (a < -B ∨ B < a ∨ b < -B ∨ B < b) → H a b = 0) :
    ∑ᶠ a, ∑ᶠ b, H a b = ∑ a ∈ Finset.Icc (-B) B, ∑ b ∈ Finset.Icc (-B) B, H a b := by
  rw [finsum_eq_Icc' _ (-B) B (fun a ha => by
    rw [finsum_eq_Icc' _ (-B) B (fun b hb => h a b (by omega))]
    exact Finset.sum_eq_zero fun b _ => h a b (by omega))]
  exact Finset.sum_congr rfl fun a _ => finsum_eq_Icc' _ (-B) B (fun b hb => h a b (by omega))

theorem finsum3_Icc {X : Type*} [AddCommMonoid X] (H : ℤ → ℤ → ℤ → X) (B : ℤ)
    (h : ∀ a b c, (a < -B ∨ B < a ∨ b < -B ∨ B < b ∨ c < -B ∨ B < c) → H a b c = 0) :
    ∑ᶠ a, ∑ᶠ b, ∑ᶠ c, H a b c
      = ∑ a ∈ Finset.Icc (-B) B, ∑ b ∈ Finset.Icc (-B) B, ∑ c ∈ Finset.Icc (-B) B, H a b c := by
  have hin : ∀ a b, ∑ᶠ c, H a b c = ∑ c ∈ Finset.Icc (-B) B, H a b c := fun a b =>
    finsum_eq_Icc' _ (-B) B (fun c hc => h a b c (by omega))
  simp only [hin]
  exact finsum2_Icc _ B (fun a b hab => Finset.sum_eq_zero fun c _ => h a b c (by omega))

/-- Reversal of a triple sum supported in a cube. -/
theorem finsum3_rev {X : Type*} [AddCommMonoid X] (H : ℤ → ℤ → ℤ → X) (B : ℤ)
    (h : ∀ a b c, (a < -B ∨ B < a ∨ b < -B ∨ B < b ∨ c < -B ∨ B < c) → H a b c = 0) :
    ∑ᶠ a, ∑ᶠ b, ∑ᶠ c, H a b c = ∑ᶠ c, ∑ᶠ b, ∑ᶠ a, H a b c := by
  rw [finsum3_Icc H B h,
    finsum3_Icc (fun c b a => H a b c) B (fun c b a hcba => h a b c (by omega))]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm,
    Finset.sum_congr rfl fun c _ => Finset.sum_comm]

/-- Exchange of the two outer indices of a triple sum supported in a cube. -/
theorem finsum3_swap12 {X : Type*} [AddCommMonoid X] (H : ℤ → ℤ → ℤ → X) (B : ℤ)
    (h : ∀ a b c, (a < -B ∨ B < a ∨ b < -B ∨ B < b ∨ c < -B ∨ B < c) → H a b c = 0) :
    ∑ᶠ a, ∑ᶠ b, ∑ᶠ c, H a b c = ∑ᶠ b, ∑ᶠ a, ∑ᶠ c, H a b c := by
  rw [finsum3_Icc H B h,
    finsum3_Icc (fun b a c => H a b c) B (fun b a c hbac => h a b c (by omega)),
    Finset.sum_comm]

end VOA.Huang.PzTensorRho
