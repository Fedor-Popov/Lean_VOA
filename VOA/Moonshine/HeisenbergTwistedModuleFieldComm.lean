/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleLocality

/-!
# The commutator formula for integer products of local fields  (Moonshine step M6a)

For fields `A, B, C` on a vector space `M` with `A, B` mutually local, the integer field
products of `Core.LocalSystemBare` satisfy the **commutator formula** of Li's local-system
vertex algebra, at *every* pair of integer indices:

  `A₍ₚ₎(B₍q₎C) − B₍q₎(A₍ₚ₎C) = Σ_{r ≥ 0} C(p,r) (A₍ᵣ₎B)₍ₚ₊q₋ᵣ₎C`     (`prod_comm_formula`).

No locality of `C` is used.  The proof is a mode computation: expanding both nested products by
the iterate formula `Fld.mode_prod_iterate` gives four families of ordered triple products; two
of them cancel between the two sides, the remaining two are mode commutators `[A_α, B_β]`, which
locality expresses through the nonnegative products (`Fld.commutator_prod_bound_of_local`), and
the resulting double sums are regrouped along antidiagonals by Vandermonde's identity.

Also here: multiplication by `zᶜ` commutes with products in the second slot
(`prod_fzmul_right`) and is expanded binomially in the first slot (`mode_prod_fzmul_left`,
needs locality), the linear mode map `modeL`, and the complex-binomial identities used.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace TwistedReduction

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The linear mode map and extensionality -/

/-- The `n`-th mode, as a linear map on fields. -/
noncomputable def modeL (n : ℤ) : Fld M →ₗ[ℂ] End ℂ M where
  toFun a := mode a.1 n
  map_add' a b := mode_add a.1 b.1 n
  map_smul' c a := mode_smul c a.1 n

@[simp] theorem modeL_apply (n : ℤ) (a : Fld M) : modeL n a = mode a.1 n := rfl

/-- Fields are determined by their modes on vectors. -/
theorem fld_ext_mode {a b : Fld M} (h : ∀ (n : ℤ) (x : M), mode a.1 n x = mode b.1 n x) :
    a = b := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  have := h (-n - 1) x
  rwa [mode_apply, mode_apply, show -(-n - 1) - 1 = n by ring] at this

theorem fld_finset_sum_val {ι : Type*} (s : Finset ι) (f : ι → Fld M) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Fld.add_val, ih]

theorem mode_fld_sum {ι : Type*} (s : Finset ι) (f : ι → Fld M) (n : ℤ) (x : M) :
    mode (∑ i ∈ s, f i).1 n x = ∑ i ∈ s, mode (f i).1 n x := by
  have h := map_sum (modeL (M := M) n) f s
  simp only [modeL_apply] at h
  rw [h, LinearMap.coe_sum, Finset.sum_apply]

theorem mode_fld_smul (c : ℂ) (a : Fld M) (n : ℤ) (x : M) :
    mode (c • a).1 n x = c • mode a.1 n x := by
  rw [Fld.smul_val, mode_smul, LinearMap.smul_apply]

theorem mode_fld_add (a b : Fld M) (n : ℤ) (x : M) :
    mode (a + b).1 n x = mode a.1 n x + mode b.1 n x := by
  rw [Fld.add_val, mode_add, LinearMap.add_apply]

theorem mode_fld_sub (a b : Fld M) (n : ℤ) (x : M) :
    mode (a - b).1 n x = mode a.1 n x - mode b.1 n x := by
  have h := map_sub (modeL (M := M) n) a b
  simp only [modeL_apply] at h
  rw [h, LinearMap.sub_apply]

theorem mode_fld_zero (n : ℤ) (x : M) : mode (0 : Fld M).1 n x = 0 := by
  rw [Fld.zero_val, mode_zero, LinearMap.zero_apply]

@[simp] theorem mode_fzmul (k : ℤ) (a : Fld M) (p : ℤ) :
    mode (fzmul k a).1 p = mode a.1 (p + k) := by
  rw [fzmul_val, mode_zmul]

theorem fzmul_fzmul (a b : ℤ) (F : Fld M) : fzmul a (fzmul b F) = fzmul (a + b) F := by
  apply Subtype.ext
  funext n
  simp only [fzmul_val, zmul]
  rw [sub_sub]

@[simp] theorem fzmul_zero_shift (F : Fld M) : fzmul 0 F = F := by
  apply Subtype.ext
  funext n
  simp [fzmul_val, zmul]

theorem fzmul_add (k : ℤ) (a b : Fld M) : fzmul k (a + b) = fzmul k a + fzmul k b := rfl

theorem fzmul_smul (k : ℤ) (c : ℂ) (a : Fld M) : fzmul k (c • a) = c • fzmul k a := rfl

@[simp] theorem fzmul_zero (k : ℤ) : fzmul k (0 : Fld M) = 0 := rfl

theorem fzmul_sum {ι : Type*} (k : ℤ) (s : Finset ι) (f : ι → Fld M) :
    fzmul k (∑ i ∈ s, f i) = ∑ i ∈ s, fzmul k (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fzmul_add, ih]

theorem fzmul_sub (k : ℤ) (a b : Fld M) : fzmul k (a - b) = fzmul k a - fzmul k b := by
  rw [sub_eq_add_neg, fzmul_add, sub_eq_add_neg, show -b = (-1 : ℂ) • b by simp, fzmul_smul]
  simp

/-! ## Uniform truncation bounds -/

/-- Finitely many eventually-true properties hold simultaneously from some point on. -/
theorem exists_uniform_bound (P : ℕ → ℤ → Prop) (L : ℕ)
    (h : ∀ r < L, ∃ K : ℤ, ∀ n : ℤ, K ≤ n → P r n) :
    ∃ K : ℤ, ∀ r < L, ∀ n : ℤ, K ≤ n → P r n := by
  induction L with
  | zero => exact ⟨0, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ L ih =>
      obtain ⟨K₁, hK₁⟩ := ih (fun r hr => h r (by omega))
      obtain ⟨K₂, hK₂⟩ := h L (by omega)
      refine ⟨max K₁ K₂, fun r hr n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · exact hK₁ r hr n (le_trans (le_max_left _ _) hn)
      · exact hK₂ n (le_trans (le_max_right _ _) hn)

/-- A field has a common truncation bound on finitely many vectors. -/
theorem mode_eventually_zero_family (a : Fld M) (L : ℕ) (y : ℕ → M) :
    ∃ K : ℤ, ∀ r < L, ∀ n : ℤ, K ≤ n → mode a.1 n (y r) = 0 :=
  exists_uniform_bound (fun r n => mode a.1 n (y r) = 0) L
    (fun r _ => Fld.mode_eventually_zero a (y r))

/-! ## The iterate formula as a finite sum -/

/-- `Fld.mode_prod_iterate` as a `range` sum, once both factors are truncated on `y`. -/
theorem mode_prod_eq_sum_range (P Q : Fld M) (ℓ N : ℤ) (y : M) (K : ℕ)
    (hQ : ∀ i : ℕ, K ≤ i → mode Q.1 (N + i) y = 0)
    (hP : ∀ i : ℕ, K ≤ i → mode P.1 i y = 0) :
    mode (Fld.prod ℓ P Q).1 N y = ∑ i ∈ Finset.range K, ((-1 : ℂ) ^ i * gBinom ℓ i) •
      (mode P.1 (ℓ - i) (mode Q.1 (N + i) y)
        - ((-1 : ℂ) ^ ℓ) • mode Q.1 (ℓ + N - i) (mode P.1 i y)) := by
  rw [Fld.mode_prod_iterate]
  exact finsum_nat_eq_sum_range K _ (fun i hi => by rw [hQ i hi, hP i hi]; simp)

/-! ## Multiplication by `zᶜ` -/

/-- **`zᶜ` in the second slot commutes with every product**: `A₍ℓ₎(zᶜB) = zᶜ(A₍ℓ₎B)`. -/
theorem prod_fzmul_right (ℓ c : ℤ) (A B : Fld M) :
    Fld.prod ℓ A (fzmul c B) = fzmul c (Fld.prod ℓ A B) := by
  apply fld_ext_mode
  intro N x
  rw [mode_fzmul, Fld.mode_prod_iterate, Fld.mode_prod_iterate]
  refine finsum_congr fun i => ?_
  simp only [mode_fzmul]
  congr 3 <;> ring_nf

/-- `negOnePow` is the integer power of `−1`. -/
theorem negOnePow_eq_zpow' (ℓ : ℤ) : negOnePow ℓ = (-1 : ℂ) ^ ℓ := by
  rcases lt_or_ge ℓ 0 with hℓ | hℓ
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ) := ⟨(-ℓ).toNat, by omega⟩
    rw [show negOnePow (-(k : ℤ)) = negOnePow (k : ℤ) by
        rw [negOnePow, negOnePow]; simp only [even_neg],
      negOnePow_natCast, zpow_neg, zpow_natCast]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow, inv_one]
    · rw [hk.neg_one_pow]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = (k : ℤ) := ⟨ℓ.toNat, (Int.toNat_of_nonneg hℓ).symm⟩
    rw [negOnePow_natCast, zpow_natCast]

omit [Module ℂ M] in
/-- An integer-indexed `finsum` of a family vanishing on negative indices is the
natural-indexed one. -/
theorem finsum_int_eq_finsum_nat (f : ℤ → M) (hf : ∀ i : ℤ, i < 0 → f i = 0) :
    ∑ᶠ i : ℤ, f i = ∑ᶠ n : ℕ, f n := by
  rw [← finsum_mem_range (g := ((↑) : ℕ → ℤ)) Nat.cast_injective, ← finsum_mem_univ]
  apply finsum_mem_inter_support_eq'
  intro i hi
  simp only [Set.mem_univ, Set.mem_range, true_iff]
  have : 0 ≤ i := by
    by_contra h
    exact hi (hf i (by omega))
  exact ⟨i.toNat, by omega⟩

/-- `Fld.field_jacobi_of_local`, with natural-number binomial sums. -/
theorem field_jacobi_nat {a b : Fld M} (h : Local a.1 b.1) (x : M) (ell m n : ℤ) :
    (∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ell i) •
      (mode a.1 (ell + m - i) (mode b.1 (n + i) x) -
        ((-1 : ℂ) ^ ell) • mode b.1 (ell + n - i) (mode a.1 (m + i) x))) =
      ∑ᶠ i : ℕ, gBinom m i • mode (Fld.prod (ell + i) a b).1 (m + n - i) x := by
  have hJ := Fld.field_jacobi_of_local h x ell m n
  rw [finsum_int_eq_finsum_nat _ (fun i hi => by rw [cbz_apply_neg ell hi, mul_zero, zero_smul]),
    finsum_int_eq_finsum_nat _ (fun i hi => by rw [cbz_apply_neg m hi, zero_smul])] at hJ
  convert hJ using 2
  · funext i
    rw [negOnePow_natCast, cbz_apply_nonneg _ (Int.natCast_nonneg i), Int.toNat_natCast,
      negOnePow_eq_zpow']

/-- **`zᶜ` in the first slot is expanded binomially** (needs locality):
`(zᶜA)₍ℓ₎B = Σ_t C(c,t) z^{c−t} (A₍ℓ₊ₜ₎B)`, in modes. -/
theorem mode_prod_fzmul_left {A B : Fld M} (h : Local A.1 B.1) (c ℓ N : ℤ) (x : M) :
    mode (Fld.prod ℓ (fzmul c A) B).1 N x
      = ∑ᶠ t : ℕ, gBinom c t • mode (Fld.prod (ℓ + t) A B).1 (c + N - t) x := by
  rw [Fld.mode_prod_iterate, ← field_jacobi_nat h x ℓ c N]
  refine finsum_congr fun i => ?_
  simp only [mode_fzmul]
  congr 3 <;> ring_nf


/-! ## Complex binomial identities -/

theorem gBinom_eq_cbinom (n : ℤ) (k : ℕ) : gBinom n k = cbinom (n : ℂ) k := rfl

/-- `C(x,i)·C(x−i,j)` is the falling factorial of length `i+j` over `i!j!`. -/
theorem cbinom_mul_cbinom_sub_eq (x : ℂ) (i j : ℕ) :
    cbinom x i * cbinom (x - i) j
      = (∏ k ∈ Finset.range (i + j), (x - k)) / ((i.factorial : ℂ) * (j.factorial : ℂ)) := by
  rw [cbinom, cbinom, Finset.prod_range_add, div_mul_div_comm]
  congr 2
  refine Finset.prod_congr rfl fun k _ => ?_
  push_cast
  ring

/-- `C(x,i)·C(x−i,j) = C(x,j)·C(x−j,i)`. -/
theorem cbinom_mul_cbinom_sub (x : ℂ) (i j : ℕ) :
    cbinom x i * cbinom (x - i) j = cbinom x j * cbinom (x - j) i := by
  rw [cbinom_mul_cbinom_sub_eq, cbinom_mul_cbinom_sub_eq, add_comm i j, mul_comm]

theorem cbinom_natCast (n k : ℕ) : cbinom (n : ℂ) k = (n.choose k : ℂ) := by
  rw [cbinom_eq_ringChoose, Ring.choose_natCast]

/-- `C(x, j+t)·C(j+t, j) = C(x, j)·C(x−j, t)`. -/
theorem cbinom_mul_choose (x : ℂ) (j t : ℕ) :
    cbinom x (j + t) * cbinom ((j + t : ℕ) : ℂ) j = cbinom x j * cbinom (x - j) t := by
  rw [cbinom_mul_cbinom_sub_eq, cbinom_natCast, Nat.choose_eq_factorial_div_factorial
    (by omega), Nat.add_sub_cancel_left]
  have hj := Nat.factorial_pos j
  have ht := Nat.factorial_pos t
  have hdvd : j.factorial * t.factorial ∣ (j + t).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add j t
  have h0 : ((j.factorial * t.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hj ht).ne'
  have h1 : (((j + t).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (j + t)).ne'
  rw [Nat.cast_div hdvd h0, cbinom]
  push_cast at h0 h1 ⊢
  field_simp

/-- `C(n, k) = 0` for naturals `n < k`. -/
theorem cbinom_natCast_of_lt {n k : ℕ} (h : n < k) : cbinom (n : ℂ) k = 0 := by
  rw [cbinom_natCast, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

/-- Vandermonde for `gBinom` along an antidiagonal. -/
theorem gBinom_vandermonde (x y : ℂ) (m : ℕ) :
    ∑ ik ∈ Finset.antidiagonal m, cbinom x ik.1 * cbinom y ik.2 = cbinom (x + y) m :=
  (cbinom_add x y m).symm


/-! ## Finite-sum bookkeeping -/

omit [Module ℂ M] in
/-- Shrinking a `range` sum past the support. -/
theorem sum_range_eq_of_vanish (f : ℕ → M) {K K' : ℕ} (hK : K ≤ K')
    (hf : ∀ i : ℕ, K ≤ i → f i = 0) :
    ∑ i ∈ Finset.range K', f i = ∑ i ∈ Finset.range K, f i := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hK) fun i hi hni => hf i ?_
  simp only [Finset.mem_range, not_lt] at hni
  exact hni

omit [Module ℂ M] in
/-- Reindexing `i = r + i'` in a `range` sum whose summand vanishes below `r`. -/
theorem sum_range_shift (F : ℕ → M) (r K : ℕ) (h1 : ∀ i : ℕ, i < r → F i = 0)
    (h2 : ∀ i' : ℕ, K ≤ r + i' → F (r + i') = 0) :
    ∑ i ∈ Finset.range K, F i = ∑ i' ∈ Finset.range K, F (r + i') := by
  rcases le_or_gt r K with hrK | hrK
  · rw [← Finset.sum_range_add_sum_Ico F hrK,
      Finset.sum_eq_zero (fun i hi => h1 i (Finset.mem_range.mp hi)), zero_add,
      Finset.sum_Ico_eq_sum_range]
    exact (sum_range_eq_of_vanish (fun i' => F (r + i')) (by omega)
      (fun i' hi' => h2 i' (by omega))).symm
  · rw [Finset.sum_eq_zero (fun i hi => h1 i (by have := Finset.mem_range.mp hi; omega)),
      Finset.sum_eq_zero (fun i' _ => h2 i' (by omega))]

/-! ## The commutator formula -/

section CommFormula

variable {A B C : Fld M}

/-- The mode commutator through the nonnegative products, as a `range` sum. -/
theorem mode_comm_eq_sum_range (hAB : Local A.1 B.1) (L : ℕ)
    (hL : ∀ r : ℕ, L ≤ r → Fld.prod r A B = 0) (α β : ℤ) (y : M) :
    mode A.1 α (mode B.1 β y) - mode B.1 β (mode A.1 α y)
      = ∑ r ∈ Finset.range L, gBinom α r • mode (Fld.prod r A B).1 (α + β - r) y := by
  obtain ⟨N0, hN0, hc⟩ := Fld.commutator_prod_bound_of_local hAB α β
  have h1 : mode A.1 α (mode B.1 β y) - mode B.1 β (mode A.1 α y)
      = ⁅mode A.1 α, mode B.1 β⁆ y := by
    rw [Ring.lie_def]; rfl
  rw [h1, hc, LinearMap.sum_apply,
    Fin.sum_univ_eq_sum_range (fun j => (gBinom α j • mode (Fld.prod (j : ℤ) A B).1
      (α + β - (j : ℤ))) y) N0]
  have hv : ∀ K : ℕ, (∀ r : ℕ, K ≤ r → Fld.prod r A B = 0) → ∀ r : ℕ, K ≤ r →
      gBinom α r • mode (Fld.prod (r : ℤ) A B).1 (α + β - (r : ℤ)) y = 0 := by
    intro K hK r hr
    rw [hK r hr, Fld.zero_val, mode_zero, LinearMap.zero_apply, smul_zero]
  simp only [LinearMap.smul_apply]
  rw [← sum_range_eq_of_vanish _ (le_max_left N0 L) (hv N0 hN0),
    ← sum_range_eq_of_vanish _ (le_max_right N0 L) (hv L hL)]

/-- The two nested products, expanded by the iterate formula: two of the four ordered families
cancel, leaving two commutator families. -/
theorem comm_formula_expand (p q N : ℤ) (x : M) (K : ℕ)
    (hA : ∀ i : ℕ, K ≤ i → mode A.1 i x = 0) (hB : ∀ k : ℕ, K ≤ k → mode B.1 k x = 0)
    (hC : ∀ j : ℕ, K ≤ j → mode C.1 (N + j) x = 0)
    (hF : ∀ i : ℕ, K ≤ i → mode (Fld.prod q B C).1 (N + i) x = 0)
    (hG : ∀ k : ℕ, K ≤ k → mode (Fld.prod p A C).1 (N + k) x = 0)
    (hBA : ∀ i k : ℕ, i < K → K ≤ k → mode B.1 k (mode A.1 i x) = 0)
    (hCA : ∀ i k : ℕ, i < K → K ≤ k → mode C.1 (p + N - i + k) (mode A.1 i x) = 0)
    (hAB : ∀ k i : ℕ, k < K → K ≤ i → mode A.1 i (mode B.1 k x) = 0)
    (hCB : ∀ k i : ℕ, k < K → K ≤ i → mode C.1 (q + N - k + i) (mode B.1 k x) = 0) :
    mode (Fld.prod p A (Fld.prod q B C)).1 N x - mode (Fld.prod q B (Fld.prod p A C)).1 N x
      = ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K,
          (((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) •
          ((mode A.1 (p - i) (mode B.1 (q - k) (mode C.1 (N + ((i + k : ℕ) : ℤ)) x))
              - mode B.1 (q - k) (mode A.1 (p - i) (mode C.1 (N + ((i + k : ℕ) : ℤ)) x)))
            + ((-1 : ℂ) ^ p * (-1 : ℂ) ^ q) •
              (mode C.1 (p + q + N - ((i + k : ℕ) : ℤ)) (mode B.1 k (mode A.1 i x))
                - mode C.1 (p + q + N - ((i + k : ℕ) : ℤ)) (mode A.1 i (mode B.1 k x)))) := by
  have e1 : ∀ i : ℕ, mode (Fld.prod q B C).1 (N + i) x
      = ∑ k ∈ Finset.range K, ((-1 : ℂ) ^ k * gBinom q k) •
          (mode B.1 (q - k) (mode C.1 (N + i + k) x)
            - ((-1 : ℂ) ^ q) • mode C.1 (q + (N + i) - k) (mode B.1 k x)) := fun i =>
    mode_prod_eq_sum_range B C q (N + i) x K
      (fun k hk => by
        have := hC (i + k) (by omega)
        rwa [Nat.cast_add, ← add_assoc] at this) hB
  have e2 : ∀ i : ℕ, i < K → mode (Fld.prod q B C).1 (p + N - i) (mode A.1 i x)
      = ∑ k ∈ Finset.range K, ((-1 : ℂ) ^ k * gBinom q k) •
          (mode B.1 (q - k) (mode C.1 (p + N - i + k) (mode A.1 i x))
            - ((-1 : ℂ) ^ q) • mode C.1 (q + (p + N - i) - k) (mode B.1 k (mode A.1 i x))) :=
    fun i hi => mode_prod_eq_sum_range B C q (p + N - i) (mode A.1 i x) K
      (fun k hk => hCA i k hi hk) (fun k hk => hBA i k hi hk)
  have e3 : ∀ k : ℕ, mode (Fld.prod p A C).1 (N + k) x
      = ∑ i ∈ Finset.range K, ((-1 : ℂ) ^ i * gBinom p i) •
          (mode A.1 (p - i) (mode C.1 (N + k + i) x)
            - ((-1 : ℂ) ^ p) • mode C.1 (p + (N + k) - i) (mode A.1 i x)) := fun k =>
    mode_prod_eq_sum_range A C p (N + k) x K
      (fun i hi => by
        have := hC (k + i) (by omega)
        rwa [Nat.cast_add, ← add_assoc] at this) hA
  have e4 : ∀ k : ℕ, k < K → mode (Fld.prod p A C).1 (q + N - k) (mode B.1 k x)
      = ∑ i ∈ Finset.range K, ((-1 : ℂ) ^ i * gBinom p i) •
          (mode A.1 (p - i) (mode C.1 (q + N - k + i) (mode B.1 k x))
            - ((-1 : ℂ) ^ p) • mode C.1 (p + (q + N - k) - i) (mode A.1 i (mode B.1 k x))) :=
    fun k hk => mode_prod_eq_sum_range A C p (q + N - k) (mode B.1 k x) K
      (fun i hi => hCB k i hk hi) (fun i hi => hAB k i hk hi)
  set σp : ℂ := (-1 : ℂ) ^ p
  set σq : ℂ := (-1 : ℂ) ^ q
  have hL1 : mode (Fld.prod p A (Fld.prod q B C)).1 N x
      = ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K,
          (((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) •
          (mode A.1 (p - i) (mode B.1 (q - k) (mode C.1 (N + i + k) x))
            - σq • mode A.1 (p - i) (mode C.1 (q + (N + i) - k) (mode B.1 k x))
            - σp • mode B.1 (q - k) (mode C.1 (p + N - i + k) (mode A.1 i x))
            + (σp * σq) • mode C.1 (q + (p + N - i) - k) (mode B.1 k (mode A.1 i x))) := by
    rw [mode_prod_eq_sum_range A (Fld.prod q B C) p N x K hF hA]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [e1 i, e2 i (Finset.mem_range.mp hi), map_sum, Finset.smul_sum (r := σp),
      ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_sub, map_smul]
    module
  have hL2 : mode (Fld.prod q B (Fld.prod p A C)).1 N x
      = ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range K,
          (((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) •
          (mode B.1 (q - k) (mode A.1 (p - i) (mode C.1 (N + k + i) x))
            - σp • mode B.1 (q - k) (mode C.1 (p + (N + k) - i) (mode A.1 i x))
            - σq • mode A.1 (p - i) (mode C.1 (q + N - k + i) (mode B.1 k x))
            + (σp * σq) • mode C.1 (p + (q + N - k) - i) (mode A.1 i (mode B.1 k x))) := by
    rw [mode_prod_eq_sum_range B (Fld.prod p A C) q N x K hG hB]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [e3 k, e4 k (Finset.mem_range.mp hk), map_sum, Finset.smul_sum (r := σq),
      ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_sub, map_smul]
    module
  rw [hL1, hL2, Finset.sum_comm (s := Finset.range K) (t := Finset.range K)
    (f := fun k i => (((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) •
          (mode B.1 (q - k) (mode A.1 (p - i) (mode C.1 (N + k + i) x))
            - σp • mode B.1 (q - k) (mode C.1 (p + (N + k) - i) (mode A.1 i x))
            - σq • mode A.1 (p - i) (mode C.1 (q + N - k + i) (mode B.1 k x))
            + (σp * σq) • mode C.1 (p + (q + N - k) - i) (mode A.1 i (mode B.1 k x)))),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show N + ((i + k : ℕ) : ℤ) = N + i + k by push_cast; ring,
    show p + q + N - ((i + k : ℕ) : ℤ) = q + (p + N - i) - k by push_cast; ring,
    show N + (k : ℤ) + i = N + i + k by ring,
    show p + (N + (k : ℤ)) - i = p + N - i + k by ring,
    show q + N - (k : ℤ) + i = q + (N + i) - k by ring,
    show p + (q + N - (k : ℤ)) - i = q + (p + N - i) - k by ring]
  module

/-- The coefficient identity of the commutator-commutator family. -/
theorem comm_coeff_X (p q : ℤ) (r m : ℕ) :
    ∑ ik ∈ Finset.antidiagonal m,
        (((-1 : ℂ) ^ ik.1 * gBinom p ik.1) * ((-1 : ℂ) ^ ik.2 * gBinom q ik.2))
          * gBinom (p - ik.1) r
      = gBinom p r * ((-1 : ℂ) ^ m * gBinom (p + q - r) m) := by
  have hterm : ∀ ik ∈ Finset.antidiagonal m,
      (((-1 : ℂ) ^ ik.1 * gBinom p ik.1) * ((-1 : ℂ) ^ ik.2 * gBinom q ik.2))
          * gBinom (p - ik.1) r
        = (gBinom p r * (-1 : ℂ) ^ m) * (cbinom ((p : ℂ) - r) ik.1 * cbinom (q : ℂ) ik.2) := by
    intro ik hik
    rw [Finset.mem_antidiagonal] at hik
    have h1 : gBinom p ik.1 * gBinom (p - ik.1) r = gBinom p r * cbinom ((p : ℂ) - r) ik.1 := by
      simp only [gBinom_eq_cbinom]
      push_cast
      exact cbinom_mul_cbinom_sub _ _ _
    have h2 : (-1 : ℂ) ^ ik.1 * (-1 : ℂ) ^ ik.2 = (-1 : ℂ) ^ m := by rw [← pow_add, hik]
    calc (((-1 : ℂ) ^ ik.1 * gBinom p ik.1) * ((-1 : ℂ) ^ ik.2 * gBinom q ik.2))
          * gBinom (p - ik.1) r
        = ((-1 : ℂ) ^ ik.1 * (-1 : ℂ) ^ ik.2) * (gBinom p ik.1 * gBinom (p - ik.1) r)
            * gBinom q ik.2 := by ring
      _ = _ := by rw [h1, h2, gBinom_eq_cbinom q]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, gBinom_vandermonde]
  simp only [gBinom_eq_cbinom]
  push_cast
  ring_nf

/-- The coefficient identity of the second commutator family (after `i = r + i'`). -/
theorem comm_coeff_Y (p q : ℤ) (r m : ℕ) :
    ∑ ik ∈ Finset.antidiagonal m,
        (((-1 : ℂ) ^ (r + ik.1) * gBinom p (r + ik.1)) * ((-1 : ℂ) ^ ik.2 * gBinom q ik.2))
          * gBinom ((r + ik.1 : ℕ) : ℤ) r
      = (-1 : ℂ) ^ r * (gBinom p r * ((-1 : ℂ) ^ m * gBinom (p + q - r) m)) := by
  have hterm : ∀ ik ∈ Finset.antidiagonal m,
      (((-1 : ℂ) ^ (r + ik.1) * gBinom p (r + ik.1)) * ((-1 : ℂ) ^ ik.2 * gBinom q ik.2))
          * gBinom ((r + ik.1 : ℕ) : ℤ) r
        = ((-1 : ℂ) ^ r * gBinom p r * (-1 : ℂ) ^ m)
            * (cbinom ((p : ℂ) - r) ik.1 * cbinom (q : ℂ) ik.2) := by
    intro ik hik
    rw [Finset.mem_antidiagonal] at hik
    have h1 : gBinom p (r + ik.1) * gBinom ((r + ik.1 : ℕ) : ℤ) r
        = gBinom p r * cbinom ((p : ℂ) - r) ik.1 := by
      simp only [gBinom_eq_cbinom]
      rw [Int.cast_natCast]
      exact cbinom_mul_choose _ _ _
    have h2 : (-1 : ℂ) ^ (r + ik.1) * (-1 : ℂ) ^ ik.2 = (-1 : ℂ) ^ r * (-1 : ℂ) ^ m := by
      rw [← pow_add, ← pow_add, add_assoc, hik]
    calc (((-1 : ℂ) ^ (r + ik.1) * gBinom p (r + ik.1)) * ((-1 : ℂ) ^ ik.2 * gBinom q ik.2))
          * gBinom ((r + ik.1 : ℕ) : ℤ) r
        = ((-1 : ℂ) ^ (r + ik.1) * (-1 : ℂ) ^ ik.2)
            * (gBinom p (r + ik.1) * gBinom ((r + ik.1 : ℕ) : ℤ) r) * gBinom q ik.2 := by ring
      _ = _ := by rw [h1, h2, gBinom_eq_cbinom q]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, gBinom_vandermonde]
  simp only [gBinom_eq_cbinom]
  push_cast
  ring_nf

/-- The `X` family regrouped along antidiagonals. -/
theorem comm_part_X (p q : ℤ) (r K : ℕ) (X : ℕ → M) (hX : ∀ m : ℕ, K ≤ m → X m = 0) :
    ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K,
        ((((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) * gBinom (p - i) r)
          • X (i + k)
      = ∑ m ∈ Finset.range K, (gBinom p r * ((-1 : ℂ) ^ m * gBinom (p + q - r) m)) • X m := by
  rw [sum_range_sq_eq_sum_antidiagonal K _ (fun i k h => by rw [hX _ h, smul_zero])]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← comm_coeff_X p q r m, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ik hik => ?_
  rw [Finset.mem_antidiagonal] at hik
  rw [hik]

/-- The `Y` family, reindexed by `i = r + i'` and regrouped along antidiagonals. -/
theorem comm_part_Y (p q : ℤ) (r K K' : ℕ) (hK : r + K' ≤ K) (Yf : ℕ → ℕ → M) (Y : ℕ → M)
    (hYf : ∀ i' k : ℕ, Yf (r + i') k = Y (i' + k)) (hY : ∀ m : ℕ, K' ≤ m → Y m = 0) :
    ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K,
        ((((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) * gBinom (i : ℤ) r)
          • Yf i k
      = ∑ m ∈ Finset.range K,
          ((-1 : ℂ) ^ r * (gBinom p r * ((-1 : ℂ) ^ m * gBinom (p + q - r) m))) • Y m := by
  rw [sum_range_shift _ r K (fun i hi => Finset.sum_eq_zero fun k _ => by
      rw [show gBinom (i : ℤ) r = 0 by
        rw [gBinom_eq_cbinom, Int.cast_natCast, cbinom_natCast_of_lt hi], mul_zero, zero_smul])
    (fun i' hi' => Finset.sum_eq_zero fun k _ => by
      rw [hYf, hY _ (by omega), smul_zero])]
  simp only [hYf]
  rw [sum_range_sq_eq_sum_antidiagonal K
    (fun i' k => ((((-1 : ℂ) ^ (r + i') * gBinom p (r + i')) * ((-1 : ℂ) ^ k * gBinom q k))
        * gBinom ((r + i' : ℕ) : ℤ) r) • Y (i' + k))
    (fun i k h => by simp only; rw [hY _ (by omega), smul_zero])]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← comm_coeff_Y p q r m, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ik hik => ?_
  rw [Finset.mem_antidiagonal] at hik
  rw [hik]

/-- **The commutator formula for integer products of fields.**  For fields `A, B, C` with
`A, B` mutually local, and `L` beyond which the products `A₍ᵣ₎B` vanish,
`A₍ₚ₎(B₍q₎C) − B₍q₎(A₍ₚ₎C) = Σ_{r<L} C(p,r) (A₍ᵣ₎B)₍ₚ₊q₋ᵣ₎C` at every `p, q ∈ ℤ`. -/
theorem mode_prod_comm_formula (hAB : Local A.1 B.1) (L : ℕ)
    (hL : ∀ r : ℕ, L ≤ r → Fld.prod r A B = 0) (p q N : ℤ) (x : M) :
    mode (Fld.prod p A (Fld.prod q B C)).1 N x - mode (Fld.prod q B (Fld.prod p A C)).1 N x
      = ∑ r ∈ Finset.range L,
          gBinom p r • mode (Fld.prod (p + q - r) (Fld.prod r A B) C).1 N x := by
  obtain ⟨cA, hcA⟩ := Fld.mode_eventually_zero A x
  obtain ⟨cB, hcB⟩ := Fld.mode_eventually_zero B x
  obtain ⟨cC, hcC⟩ := Fld.mode_eventually_zero C x
  obtain ⟨cF, hcF⟩ := Fld.mode_eventually_zero (Fld.prod q B C) x
  obtain ⟨cG, hcG⟩ := Fld.mode_eventually_zero (Fld.prod p A C) x
  obtain ⟨cBA, hcBA⟩ := mode_eventually_zero_family B cA.toNat (fun i => mode A.1 i x)
  obtain ⟨cCA, hcCA⟩ := mode_eventually_zero_family C cA.toNat (fun i => mode A.1 i x)
  obtain ⟨cAB, hcAB⟩ := mode_eventually_zero_family A cB.toNat (fun k => mode B.1 k x)
  obtain ⟨cCB, hcCB⟩ := mode_eventually_zero_family C cB.toNat (fun k => mode B.1 k x)
  obtain ⟨cD, hcD⟩ := exists_uniform_bound (fun r n => mode (Fld.prod r A B).1 n x = 0) L
    (fun r _ => Fld.mode_eventually_zero _ x)
  have hnat : ∀ c : ℤ, ∃ n : ℕ, c ≤ n ∧ -c ≤ n := fun c => ⟨c.natAbs, by omega, by omega⟩
  obtain ⟨nA, hnA, -⟩ := hnat cA
  obtain ⟨nB, hnB, -⟩ := hnat cB
  obtain ⟨nC, hnC, -⟩ := hnat cC
  obtain ⟨nF, hnF, -⟩ := hnat cF
  obtain ⟨nG, hnG, -⟩ := hnat cG
  obtain ⟨nBA, hnBA, -⟩ := hnat cBA
  obtain ⟨nCA, hnCA, -⟩ := hnat cCA
  obtain ⟨nAB, hnAB, -⟩ := hnat cAB
  obtain ⟨nCB, hnCB, -⟩ := hnat cCB
  obtain ⟨nD, hnD, -⟩ := hnat cD
  obtain ⟨nN, hnN1, hnN2⟩ := hnat N
  obtain ⟨np, hnp1, hnp2⟩ := hnat p
  obtain ⟨nq, hnq1, hnq2⟩ := hnat q
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = nA + nB + nC + nF + nG + nBA + nCA + nAB + nCB + nD + nN + np
      + nq + L + 1 := ⟨_, rfl⟩
  have hA0 : ∀ i : ℕ, cA.toNat ≤ i → mode A.1 i x = 0 := fun i hi => hcA i (by omega)
  have hB0 : ∀ k : ℕ, cB.toNat ≤ k → mode B.1 k x = 0 := fun k hk => hcB k (by omega)
  have hAt : (cA.toNat : ℤ) ≤ nA := by omega
  have hBt : (cB.toNat : ℤ) ≤ nB := by omega
  rw [comm_formula_expand p q N x K
    (fun i hi => hA0 i (by omega)) (fun k hk => hB0 k (by omega))
    (fun j hj => hcC _ (by omega)) (fun i hi => hcF _ (by omega)) (fun k hk => hcG _ (by omega))
    (fun i k _ hk => by
      by_cases hi : i < cA.toNat
      · exact hcBA i hi k (by omega)
      · rw [hA0 i (by omega), map_zero])
    (fun i k _ hk => by
      by_cases hi : i < cA.toNat
      · exact hcCA i hi _ (by omega)
      · rw [hA0 i (by omega), map_zero])
    (fun k i _ hi => by
      by_cases hk : k < cB.toNat
      · exact hcAB k hk i (by omega)
      · rw [hB0 k (by omega), map_zero])
    (fun k i _ hi => by
      by_cases hk : k < cB.toNat
      · exact hcCB k hk _ (by omega)
      · rw [hB0 k (by omega), map_zero])]
  -- the two commutator families, through the nonnegative products
  have hY : ∀ (n : ℤ) (i k : ℕ), mode C.1 n (mode B.1 k (mode A.1 i x))
      - mode C.1 n (mode A.1 i (mode B.1 k x))
      = -∑ r ∈ Finset.range L, gBinom (i : ℤ) r •
          mode C.1 n (mode (Fld.prod r A B).1 (i + k - r) x) := by
    intro n i k
    rw [← map_sub, show mode B.1 k (mode A.1 i x) - mode A.1 i (mode B.1 k x)
        = -(mode A.1 i (mode B.1 k x) - mode B.1 k (mode A.1 i x)) from (neg_sub _ _).symm,
      map_neg, mode_comm_eq_sum_range hAB L hL, map_sum]
    simp only [map_smul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by
    rw [mode_comm_eq_sum_range hAB L hL, hY]))]
  have hRHS : ∀ r ∈ Finset.range L, mode (Fld.prod (p + q - r) (Fld.prod r A B) C).1 N x
      = ∑ m ∈ Finset.range K, ((-1 : ℂ) ^ m * gBinom (p + q - r) m) •
          (mode (Fld.prod r A B).1 (p + q - r - m) (mode C.1 (N + m) x)
            - ((-1 : ℂ) ^ (p + q - r)) • mode C.1 (p + q - r + N - m)
                (mode (Fld.prod r A B).1 m x)) := fun r hr =>
    mode_prod_eq_sum_range _ _ _ _ _ K (fun m hm => hcC _ (by omega))
      (fun m hm => hcD r (Finset.mem_range.mp hr) _ (by omega))
  have hRHS' : (∑ r ∈ Finset.range L,
      gBinom p r • mode (Fld.prod (p + q - r) (Fld.prod r A B) C).1 N x)
      = ∑ r ∈ Finset.range L, gBinom p r • ∑ m ∈ Finset.range K,
          ((-1 : ℂ) ^ m * gBinom (p + q - r) m) •
          (mode (Fld.prod r A B).1 (p + q - r - m) (mode C.1 (N + m) x)
            - ((-1 : ℂ) ^ (p + q - r)) • mode C.1 (p + q - r + N - m)
                (mode (Fld.prod r A B).1 m x)) :=
    Finset.sum_congr rfl (fun r hr => by rw [hRHS r hr])
  rw [hRHS']
  -- distribute and bring the `r`-sum outside
  set σp : ℂ := (-1 : ℂ) ^ p
  set σq : ℂ := (-1 : ℂ) ^ q
  have hσ : ∀ r : ℕ, (-1 : ℂ) ^ (p + q - (r : ℤ)) = σp * σq * (-1 : ℂ) ^ r := by
    intro r
    have h1 : (-1 : ℂ) ≠ 0 := by norm_num
    rw [zpow_sub₀ h1, zpow_add₀ h1, zpow_natCast, div_eq_mul_inv]
    have h2 : ((-1 : ℂ) ^ r)⁻¹ = (-1 : ℂ) ^ r := by
      rcases neg_one_pow_eq_or ℂ r with h | h <;> rw [h] <;> norm_num
    rw [h2]
  have hterm : ∀ i k : ℕ,
      (((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) •
        (∑ r ∈ Finset.range L, gBinom (p - i) r •
            mode (Fld.prod r A B).1 (p - i + (q - k) - r) (mode C.1 (N + ((i + k : ℕ) : ℤ)) x)
          + (σp * σq) • -∑ r ∈ Finset.range L, gBinom (i : ℤ) r •
            mode C.1 (p + q + N - ((i + k : ℕ) : ℤ)) (mode (Fld.prod r A B).1 (i + k - r) x))
      = ∑ r ∈ Finset.range L,
          (((((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) * gBinom (p - i) r) •
              mode (Fld.prod r A B).1 (p + q - r - ((i + k : ℕ) : ℤ))
                (mode C.1 (N + ((i + k : ℕ) : ℤ)) x)
            - (σp * σq) •
              ((((-1 : ℂ) ^ i * gBinom p i) * ((-1 : ℂ) ^ k * gBinom q k)) * gBinom (i : ℤ) r) •
              mode C.1 (p + q + N - ((i + k : ℕ) : ℤ))
                (mode (Fld.prod r A B).1 (i + k - r) x)) := by
    intro i k
    simp only [smul_add, smul_neg, Finset.smul_sum]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show p - (i : ℤ) + (q - k) - r = p + q - r - ((i + k : ℕ) : ℤ) by push_cast; ring]
    module
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => hterm i k))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrL := Finset.mem_range.mp hr
  simp only [Finset.sum_sub_distrib, ← Finset.smul_sum]
  rw [comm_part_X p q r K (fun m => mode (Fld.prod r A B).1 (p + q - r - m)
      (mode C.1 (N + m) x)) (fun m hm => by simp only; rw [hcC _ (by omega), map_zero]),
    comm_part_Y p q r K nD.succ (by omega)
      (fun i k => mode C.1 (p + q + N - ((i + k : ℕ) : ℤ))
        (mode (Fld.prod r A B).1 (i + k - r) x))
      (fun m => mode C.1 (p + q - r + N - m) (mode (Fld.prod r A B).1 m x))
      (fun i' k => by
        simp only
        rw [show p + q + N - ((r + i' + k : ℕ) : ℤ) = p + q - r + N - ((i' + k : ℕ) : ℤ) by
            push_cast; ring,
          show ((r + i' : ℕ) : ℤ) + k - r = ((i' + k : ℕ) : ℤ) by push_cast; ring])
      (fun m hm => by simp only; rw [hcD r hrL _ (by omega), map_zero])]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hσ r]
  module

/-- Field form of the commutator formula. -/
theorem prod_comm_formula (hAB : Local A.1 B.1) (L : ℕ)
    (hL : ∀ r : ℕ, L ≤ r → Fld.prod r A B = 0) (p q : ℤ) :
    Fld.prod p A (Fld.prod q B C) - Fld.prod q B (Fld.prod p A C)
      = ∑ r ∈ Finset.range L, gBinom p r • Fld.prod (p + q - r) (Fld.prod r A B) C := by
  apply fld_ext_mode
  intro N x
  rw [mode_fld_sub, mode_prod_comm_formula hAB L hL, mode_fld_sum]
  simp only [mode_fld_smul]

end CommFormula

/-! ## Linearity of products in each slot -/

/-- The product `A₍ₙ₎·` as a linear map. -/
noncomputable def prodR (n : ℤ) (A : Fld M) : Fld M →ₗ[ℂ] Fld M where
  toFun := Fld.prod n A
  map_add' := Fld.prod_add_right n A
  map_smul' d b := Fld.prod_smul_right n d A b

/-- The product `·₍ₙ₎C` as a linear map. -/
noncomputable def prodLft (n : ℤ) (C : Fld M) : Fld M →ₗ[ℂ] Fld M where
  toFun A := Fld.prod n A C
  map_add' a b := Fld.prod_add_left n a b C
  map_smul' d a := Fld.prod_smul_left n d a C

theorem prod_sum_right {ι : Type*} (n : ℤ) (A : Fld M) (s : Finset ι) (f : ι → Fld M) :
    Fld.prod n A (∑ i ∈ s, f i) = ∑ i ∈ s, Fld.prod n A (f i) :=
  map_sum (prodR n A) f s

theorem prod_sum_left {ι : Type*} (n : ℤ) (C : Fld M) (s : Finset ι) (f : ι → Fld M) :
    Fld.prod n (∑ i ∈ s, f i) C = ∑ i ∈ s, Fld.prod n (f i) C :=
  map_sum (prodLft n C) f s

theorem prod_zero_right (n : ℤ) (A : Fld M) : Fld.prod n A 0 = 0 := map_zero (prodR n A)

theorem prod_zero_left (n : ℤ) (C : Fld M) : Fld.prod n 0 C = 0 := map_zero (prodLft n C)

theorem prod_sub_right (n : ℤ) (A b c : Fld M) :
    Fld.prod n A (b - c) = Fld.prod n A b - Fld.prod n A c := map_sub (prodR n A) b c

theorem prod_sub_left (n : ℤ) (a b C : Fld M) :
    Fld.prod n (a - b) C = Fld.prod n a C - Fld.prod n b C := map_sub (prodLft n C) a b

/-- `zᶜ` in the first slot, field form: `(zᶜD)₍ⱼ₎C = Σ_{t<T} C(c,t) z^{c−t} D₍ⱼ₊ₜ₎C`. -/
theorem prod_fzmul_left {D C : Fld M} (h : Local D.1 C.1) (c j : ℤ) (T : ℕ)
    (hT : ∀ t : ℕ, T ≤ t → Fld.prod (j + t) D C = 0) :
    Fld.prod j (fzmul c D) C
      = ∑ t ∈ Finset.range T, gBinom c t • fzmul (c - t) (Fld.prod (j + t) D C) := by
  apply fld_ext_mode
  intro N x
  rw [mode_prod_fzmul_left h, finsum_nat_eq_sum_range T _ (fun t ht => by
      rw [hT t ht, Fld.zero_val, mode_zero, LinearMap.zero_apply, smul_zero]),
    mode_fld_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mode_fld_smul, mode_fzmul, show c + N - (t : ℤ) = N + (c - t) by ring]

/-! ## Derivatives -/

@[simp] theorem mode_fld_deriv (a : Fld M) (m : ℤ) (x : M) :
    mode (Fld.deriv a).1 m x = (-m : ℂ) • mode a.1 (m - 1) x := by
  rw [Fld.deriv_val, mode_deriv, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg]

/-- `∂(zᶜX) = c z^{c−1} X + zᶜ ∂X`. -/
theorem deriv_fzmul (c : ℤ) (X : Fld M) :
    Fld.deriv (fzmul c X) = (c : ℂ) • fzmul (c - 1) X + fzmul c (Fld.deriv X) := by
  apply fld_ext_mode
  intro n x
  rw [mode_fld_add, mode_fld_smul, mode_fld_deriv, mode_fzmul, mode_fzmul, mode_fzmul,
    mode_fld_deriv, show n - 1 + c = n + (c - 1) by ring, show n + c - 1 = n + (c - 1) by ring,
    ← add_smul]
  congr 1
  push_cast
  ring

omit [Module ℂ M] in
/-- Shifting a `range` sum by one when the end terms vanish. -/
theorem sum_range_shift_one (f : ℕ → M) (K : ℕ) (h0 : f 0 = 0) (hK : f K = 0) :
    ∑ i ∈ Finset.range K, f i = ∑ j ∈ Finset.range K, f (j + 1) := by
  have h1 := Finset.sum_range_succ f K
  have h2 := Finset.sum_range_succ' f K
  rw [hK, add_zero] at h1
  rw [h0, add_zero] at h2
  rw [← h1, h2]

theorem cbinom_succ_mul (x : ℂ) (i : ℕ) :
    cbinom x (i + 1) * ((i : ℂ) + 1) = x * cbinom (x - 1) i := by
  rw [cbinom, cbinom, Finset.prod_range_succ', Nat.factorial_succ]
  have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hi1 : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  push_cast
  have hprod : (∏ k ∈ Finset.range i, (x - ((k : ℂ) + 1))) = ∏ k ∈ Finset.range i, (x - 1 - k) :=
    Finset.prod_congr rfl (fun k _ => by ring)
  rw [hprod]
  field_simp
  ring

theorem cbinom_mul_sub (x : ℂ) (i : ℕ) : cbinom x i * (x - i) = x * cbinom (x - 1) i := by
  rw [← cbinom_succ_mul, cbinom, cbinom, Finset.prod_range_succ, Nat.factorial_succ]
  have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hi1 : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  push_cast
  field_simp

theorem gBinom_succ_mul (n : ℤ) (i : ℕ) :
    gBinom n (i + 1) * ((i : ℂ) + 1) = (n : ℂ) * gBinom (n - 1) i := by
  simp only [gBinom_eq_cbinom]; push_cast; exact cbinom_succ_mul _ _

theorem gBinom_mul_sub (n : ℤ) (i : ℕ) :
    gBinom n i * ((n : ℂ) - i) = (n : ℂ) * gBinom (n - 1) i := by
  simp only [gBinom_eq_cbinom]; push_cast; exact cbinom_mul_sub _ _

/-- `(∂D)₍ₙ₎X = −n D₍ₙ₋₁₎X`. -/
theorem prod_deriv_left (n : ℤ) (D X : Fld M) :
    Fld.prod n (Fld.deriv D) X = (-n : ℂ) • Fld.prod (n - 1) D X := by
  apply fld_ext_mode
  intro N x
  obtain ⟨cX, hX⟩ := Fld.mode_eventually_zero X x
  obtain ⟨cD, hD⟩ := Fld.mode_eventually_zero D x
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, cX - N ≤ K ∧ cD + 1 ≤ K :=
    ⟨(cX - N).toNat + (cD + 1).toNat, by omega, by omega⟩
  rw [mode_fld_smul, mode_prod_eq_sum_range _ _ n N x K (fun i hi => hX _ (by omega))
      (fun i hi => by rw [mode_fld_deriv, hD _ (by omega), smul_zero]),
    mode_prod_eq_sum_range _ _ (n - 1) N x K (fun i hi => hX _ (by omega))
      (fun i hi => hD _ (by omega))]
  simp only [mode_fld_deriv, map_smul, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n - (i : ℤ) - 1 = n - 1 - i by ring]
    simp only [smul_smul]
    congr 1
    have := gBinom_mul_sub n i
    push_cast
    linear_combination (-(-1 : ℂ) ^ i) * this
  · rw [sum_range_shift_one _ K (by simp) (by rw [hD _ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + N - ((j + 1 : ℕ) : ℤ) = n - 1 + N - j by push_cast; ring,
      show ((j + 1 : ℕ) : ℤ) - 1 = j by push_cast; ring]
    simp only [smul_smul]
    congr 1
    have h1 := gBinom_succ_mul n j
    have h2 : (-1 : ℂ) ^ (n - 1) = -(-1 : ℂ) ^ n := by
      rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]; ring
    rw [h2]
    push_cast
    linear_combination ((-1 : ℂ) ^ j * (-1 : ℂ) ^ n) * h1

/-- `∂(D₍ₙ₎X) = (∂D)₍ₙ₎X + D₍ₙ₎(∂X)`. -/
theorem deriv_prod (n : ℤ) (D X : Fld M) :
    Fld.deriv (Fld.prod n D X) = Fld.prod n (Fld.deriv D) X + Fld.prod n D (Fld.deriv X) := by
  rw [prod_deriv_left]
  apply fld_ext_mode
  intro N x
  obtain ⟨cX, hX⟩ := Fld.mode_eventually_zero X x
  obtain ⟨cD, hD⟩ := Fld.mode_eventually_zero D x
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, cX - N + 1 ≤ K ∧ cD ≤ K :=
    ⟨(cX - N + 1).toNat + cD.toNat, by omega, by omega⟩
  rw [mode_fld_deriv, mode_fld_add, mode_fld_smul,
    mode_prod_eq_sum_range D X n (N - 1) x K (fun i hi => hX _ (by omega))
      (fun i hi => hD _ (by omega)),
    mode_prod_eq_sum_range D X (n - 1) N x K (fun i hi => hX _ (by omega))
      (fun i hi => hD _ (by omega)),
    mode_prod_eq_sum_range D (Fld.deriv X) n N x K
      (fun i hi => by rw [mode_fld_deriv, hX _ (by omega), smul_zero])
      (fun i hi => hD _ (by omega))]
  simp only [mode_fld_deriv, map_smul, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  have hσ : (-1 : ℂ) ^ (n - 1) = -(-1 : ℂ) ^ n := by
    rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]; ring
  have hshift : (∑ i ∈ Finset.range K, (-(n : ℂ)) • ((-1 : ℂ) ^ i * gBinom (n - 1) i) •
        mode D.1 (n - 1 - i) (mode X.1 (N + i) x))
      = ∑ i ∈ Finset.range K, ((-1 : ℂ) ^ i * gBinom n i * (i : ℂ)) •
        mode D.1 (n - i) (mode X.1 (N + i - 1) x) := by
    rw [sum_range_shift_one (fun i => ((-1 : ℂ) ^ i * gBinom n i * (i : ℂ)) •
        mode D.1 (n - i) (mode X.1 (N + i - 1) x)) K (by simp)
        (by simp only; rw [hX _ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n - ((j + 1 : ℕ) : ℤ) = n - 1 - j by push_cast; ring,
      show N + ((j + 1 : ℕ) : ℤ) - 1 = N + j by push_cast; ring, smul_smul]
    congr 1
    have h1 := gBinom_succ_mul n j
    push_cast at h1 ⊢
    linear_combination ((-1 : ℂ) ^ j) * h1
  have hDX : (∑ i ∈ Finset.range K, (-(N : ℂ)) • ((-1 : ℂ) ^ i * gBinom n i) •
        mode D.1 (n - i) (mode X.1 (N - 1 + i) x))
      = (∑ i ∈ Finset.range K, (-(n : ℂ)) • ((-1 : ℂ) ^ i * gBinom (n - 1) i) •
          mode D.1 (n - 1 - i) (mode X.1 (N + i) x))
        + ∑ i ∈ Finset.range K, ((-1 : ℂ) ^ i * gBinom n i) • (-((N + i : ℤ) : ℂ)) •
          mode D.1 (n - i) (mode X.1 (N + i - 1) x) := by
    rw [hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show N - 1 + (i : ℤ) = N + i - 1 by ring]
    simp only [smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have hXD : (∑ i ∈ Finset.range K, (-(N : ℂ)) • ((-1 : ℂ) ^ i * gBinom n i) •
        (-1 : ℂ) ^ n • mode X.1 (n + (N - 1) - i) (mode D.1 i x))
      = (∑ i ∈ Finset.range K, (-(n : ℂ)) • ((-1 : ℂ) ^ i * gBinom (n - 1) i) •
          (-1 : ℂ) ^ (n - 1) • mode X.1 (n - 1 + N - i) (mode D.1 i x))
        + ∑ i ∈ Finset.range K, ((-1 : ℂ) ^ i * gBinom n i) • (-1 : ℂ) ^ n •
          (-((n + N - i : ℤ) : ℂ)) • mode X.1 (n + N - i - 1) (mode D.1 i x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n - 1 + N - (i : ℤ) = n + (N - 1) - i by ring,
      show n + N - (i : ℤ) - 1 = n + (N - 1) - i by ring, hσ]
    simp only [smul_smul, ← add_smul]
    congr 1
    have h2 := gBinom_mul_sub n i
    push_cast at h2 ⊢
    linear_combination ((-1 : ℂ) ^ i * (-1 : ℂ) ^ n) * h2
  rw [hDX, hXD]
  abel

end TwistedReduction

end VOA
