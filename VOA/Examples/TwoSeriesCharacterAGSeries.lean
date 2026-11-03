/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# Andrews' functional equations for the Andrews–Gordon series

Formal power series in an outer variable `x` (`xx`) over `R = ℚ⟦q⟧` (`qq`).  For a fixed
`K ≥ 1` and `0 ≤ i ≤ K`, Andrews' series (with the factor `(xq)_∞` cleared) is

`A_i(x) = Σ_{s ≥ 0} (-1)^s q^{K s² + (K-i) s + s(s+1)/2} / (q)_s · x^{Ks} (1 - x^i q^{(2s+1)i}) (xq)_s`,

defined coefficientwise in `x` (only `s ≤ m` contributes to `x^m`).  The main theorem
`AA_functional` is Andrews' functional equation in the form

`A_{a+1}(x) - A_a(x) = x^a q^a (1 - xq) A_{j}(xq)`,   `a + j = K`, `j ≥ 1`,

proved termwise (`term_sub_eq`, `term_resc_eq`) and by a telescoping of the `s`-sums.
Everything is proved; no hypothesis is introduced.
-/

namespace VOA.TwoSeriesCharacter.AG

open PowerSeries
open scoped BigOperators

noncomputable section

/-- The coefficient ring `ℚ⟦q⟧`. -/
abbrev R := PowerSeries ℚ

/-- The variable `q`. -/
def qq : R := PowerSeries.X

/-- The outer variable `x`. -/
def xx : PowerSeries R := PowerSeries.X

/-- Constants. -/
def CC : R →+* PowerSeries R := PowerSeries.C

/-- The substitution `x ↦ q x`. -/
def resc : PowerSeries R →+* PowerSeries R := rescale qq

theorem coeff_resc (f : PowerSeries R) (n : ℕ) : coeff n (resc f) = qq ^ n * coeff n f :=
  coeff_rescale f qq n

theorem resc_CC (r : R) : resc (CC r) = CC r := by
  ext n
  rw [coeff_resc]
  simp only [CC, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem resc_xx : resc xx = CC qq * xx := rescale_X qq

/-! ## §1  `q`-Pochhammer symbols -/

/-- `(q)_s ∈ ℚ⟦q⟧`. -/
def poch (s : ℕ) : R := ∏ j ∈ Finset.range s, (1 - qq ^ (j + 1))

theorem poch_succ (s : ℕ) : poch (s + 1) = poch s * (1 - qq ^ (s + 1)) := by
  rw [poch, Finset.prod_range_succ]; rfl

theorem constantCoeff_poch (s : ℕ) : constantCoeff (poch s) = 1 := by
  rw [poch, map_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  simp [qq]

/-- `1/(q)_s`. -/
def ipoch (s : ℕ) : R := (poch s)⁻¹

theorem poch_mul_ipoch (s : ℕ) : poch s * ipoch s = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_poch]; exact one_ne_zero)

theorem ipoch_succ (s : ℕ) : (1 - qq ^ (s + 1)) * ipoch (s + 1) = ipoch s := by
  have h1 := poch_mul_ipoch (s + 1)
  have h2 := poch_mul_ipoch s
  rw [poch_succ] at h1
  calc (1 - qq ^ (s + 1)) * ipoch (s + 1)
      = (poch s * ipoch s) * ((1 - qq ^ (s + 1)) * ipoch (s + 1)) := by rw [h2, one_mul]
    _ = ipoch s * (poch s * (1 - qq ^ (s + 1)) * ipoch (s + 1)) := by ring
    _ = ipoch s := by rw [h1, mul_one]

/-- `(xq; q)_s`. -/
def PP (s : ℕ) : PowerSeries R := ∏ j ∈ Finset.range s, (1 - CC (qq ^ (j + 1)) * xx)

theorem PP_succ (s : ℕ) : PP (s + 1) = PP s * (1 - CC (qq ^ (s + 1)) * xx) := by
  rw [PP, Finset.prod_range_succ]; rfl

theorem PP_succ' (s : ℕ) : PP (s + 1) = (1 - CC qq * xx) * resc (PP s) := by
  rw [PP, Finset.prod_range_succ', PP, map_prod, mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_one, map_mul, resc_CC, resc_xx, pow_succ, map_mul]
    ring

/-! ## §2  The terms and the series `A_i` -/

/-- Triangular numbers. -/
def tri : ℕ → ℕ
  | 0 => 0
  | s + 1 => tri s + s + 1

variable (K : ℕ)

/-- The `s`-th term of `A_i` with `d = K - i`. -/
def term (d i s : ℕ) : PowerSeries R :=
  CC ((-1) ^ s * qq ^ (K * s * s + d * s + tri s) * ipoch s) * xx ^ (K * s) *
    (1 - CC (qq ^ ((2 * s + 1) * i)) * xx ^ i) * PP s

theorem coeff_term_of_lt (d i s m : ℕ) (h : m < K * s) : coeff m (term K d i s) = 0 := by
  have : term K d i s = xx ^ (K * s) *
      (CC ((-1) ^ s * qq ^ (K * s * s + d * s + tri s) * ipoch s) *
        (1 - CC (qq ^ ((2 * s + 1) * i)) * xx ^ i) * PP s) := by
    unfold term; ring
  rw [this, xx, coeff_X_pow_mul', if_neg (by omega)]

/-- Andrews' series `A_i`, coefficientwise in `x`. -/
def AA (i : ℕ) : PowerSeries R :=
  mk fun m => ∑ s ∈ Finset.range (m + 1), coeff m (term K (K - i) i s)

theorem coeff_AA (i m : ℕ) :
    coeff m (AA K i) = ∑ s ∈ Finset.range (m + 1), coeff m (term K (K - i) i s) :=
  coeff_mk _ _

/-- Any longer `s`-range gives the same coefficient. -/
theorem coeff_AA_eq (hK : 1 ≤ K) (i m M : ℕ) (hM : m ≤ M) :
    coeff m (AA K i) = ∑ s ∈ Finset.range (M + 1), coeff m (term K (K - i) i s) := by
  rw [coeff_AA]
  obtain ⟨d, rfl⟩ : ∃ d, M = m + d := ⟨M - m, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [ih (by omega), show m + (d + 1) + 1 = (m + d + 1) + 1 by ring,
        Finset.sum_range_succ _ (m + d + 1),
        coeff_term_of_lt K _ _ (m + d + 1) m
          (lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_left _ hK)), add_zero]

/-! ## §3  The termwise identities -/

/-- The first auxiliary term. -/
def UU (j' s : ℕ) : PowerSeries R :=
  CC ((-1) ^ s * qq ^ (K * s * s + j' * s + tri s) * ((1 - qq ^ s) * ipoch s)) * xx ^ (K * s) *
    PP s

/-- The second auxiliary term. -/
def VV (a s : ℕ) : PowerSeries R :=
  CC ((-1) ^ s * qq ^ (K * s * s + K * s + tri s + a * s + a) * ipoch s) * xx ^ (K * s + a) *
    PP (s + 1)

theorem UU_zero (j' : ℕ) : UU K j' 0 = 0 := by
  simp [UU]

theorem coeff_UU_of_lt (j' s m : ℕ) (h : m < K * s) : coeff m (UU K j' s) = 0 := by
  have : UU K j' s = xx ^ (K * s) *
      (CC ((-1) ^ s * qq ^ (K * s * s + j' * s + tri s) * ((1 - qq ^ s) * ipoch s)) * PP s) := by
    unfold UU; ring
  rw [this, xx, coeff_X_pow_mul', if_neg (by omega)]

/-- **Identity (a)**: `term_{a+1} - term_a = U + V`. -/
theorem term_sub_eq (a j' s : ℕ) (hK : K = a + j' + 1) :
    term K j' (a + 1) s - term K (j' + 1) a s = UU K j' s + VV K a s := by
  subst hK
  unfold term UU VV
  rw [PP_succ]
  simp only [map_mul, map_pow, map_sub, map_one, map_neg]
  ring

/-- **Identity (b)**: `x^a q^a (1 - xq) term_j(xq) = V + U_{s+1}`. -/
theorem term_resc_eq (a j' s : ℕ) (hK : K = a + j' + 1) :
    xx ^ a * CC (qq ^ a) * (1 - CC qq * xx) * resc (term K a (j' + 1) s) =
      VV K a s + UU K j' (s + 1) := by
  subst hK
  have hU : UU (a + j' + 1) j' (s + 1) =
      CC ((-1) ^ (s + 1) * qq ^ ((a + j' + 1) * (s + 1) * (s + 1) + j' * (s + 1) + tri (s + 1)) *
        ipoch s) * xx ^ ((a + j' + 1) * (s + 1)) * PP (s + 1) := by
    unfold UU; rw [ipoch_succ]
  rw [hU]
  unfold term VV
  have hP : (1 - CC qq * xx) * resc (PP s) = PP (s + 1) := (PP_succ' s).symm
  simp only [map_mul, resc_CC, map_pow, map_sub, map_one, resc_xx, map_neg]
  rw [← hP, tri]
  ring

/-! ## §4  The functional equation -/

/-- Coefficients up to `m` determine `coeff m (Y * resc F)`. -/
theorem coeff_mul_resc_congr (Y F G : PowerSeries R) (m : ℕ)
    (h : ∀ k ≤ m, coeff k F = coeff k G) : coeff m (Y * resc F) = coeff m (Y * resc G) := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : p.2 ≤ m := by
    have := Finset.mem_antidiagonal.mp hp; omega
  rw [coeff_resc, coeff_resc, h p.2 hp2]

/-- **Andrews' functional equation** `A_{a+1} - A_a = x^a q^a (1 - xq) A_{j}(xq)`,
`a + j = K`, `j ≥ 1`. -/
theorem AA_functional (a j' : ℕ) (hK : K = a + j' + 1) :
    AA K (a + 1) - AA K a = xx ^ a * CC (qq ^ a) * (1 - CC qq * xx) * resc (AA K (j' + 1)) := by
  have hK1 : 1 ≤ K := by omega
  refine PowerSeries.ext fun m => ?_
  have hd1 : K - (a + 1) = j' := by omega
  have hd2 : K - a = j' + 1 := by omega
  have hd3 : K - (j' + 1) = a := by omega
  rw [LinearMap.map_sub, coeff_AA, coeff_AA, hd1, hd2, ← Finset.sum_sub_distrib]
  have hL : ∀ s ∈ Finset.range (m + 1),
      coeff m (term K j' (a + 1) s) - coeff m (term K (j' + 1) a s) =
        coeff m (UU K j' s) + coeff m (VV K a s) := by
    intro s _
    rw [← LinearMap.map_sub, term_sub_eq K a j' s hK, LinearMap.map_add]
  rw [Finset.sum_congr rfl hL]
  set T := ∑ s ∈ Finset.range (m + 1), term K a (j' + 1) s with hT
  have htr : ∀ k ≤ m, coeff k (AA K (j' + 1)) = coeff k T := by
    intro k hk
    rw [coeff_AA_eq K hK1 (j' + 1) k m hk, hT, map_sum, hd3]
  rw [coeff_mul_resc_congr _ _ T m htr, hT, map_sum resc, Finset.mul_sum, map_sum (coeff m)]
  have hR : ∀ s ∈ Finset.range (m + 1),
      coeff m (xx ^ a * CC (qq ^ a) * (1 - CC qq * xx) * resc (term K a (j' + 1) s)) =
        coeff m (VV K a s) + coeff m (UU K j' (s + 1)) := by
    intro s _
    rw [term_resc_eq K a j' s hK, LinearMap.map_add]
  rw [Finset.sum_congr rfl hR]
  have hUs : ∑ s ∈ Finset.range (m + 1), coeff m (UU K j' (s + 1)) =
      ∑ s ∈ Finset.range (m + 1), coeff m (UU K j' s) := by
    rw [Finset.sum_range_succ (fun s => coeff m (UU K j' (s + 1))) m,
      coeff_UU_of_lt K j' (m + 1) m (lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_left _ hK1)),
      add_zero, Finset.sum_range_succ' (fun s => coeff m (UU K j' s)) m, UU_zero,
      LinearMap.map_zero, add_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hUs, add_comm]

/-! ## §5  Boundary values -/

theorem AA_zero : AA K 0 = 0 := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_AA, LinearMap.map_zero]
  refine Finset.sum_eq_zero fun s _ => ?_
  simp [term]

theorem constantCoeff_AA (i : ℕ) (hi : 1 ≤ i) : constantCoeff (AA K i) = 1 := by
  have hP : PP 0 = 1 := by simp [PP]
  have hi0 : ipoch 0 = 1 := by
    have := poch_mul_ipoch 0
    simpa [poch] using this
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_AA, Finset.sum_range_one]
  have ht : term K (K - i) i 0 = 1 - CC (qq ^ i) * xx ^ i := by
    simp [term, tri, hP, hi0]
  rw [ht, LinearMap.map_sub, coeff_one, if_pos rfl]
  have h0 : coeff 0 (CC (qq ^ i) * xx ^ i) = 0 := by
    rw [CC, coeff_C_mul, xx, coeff_X_pow, if_neg (by omega), mul_zero]
  rw [h0, sub_zero]

end

end VOA.TwoSeriesCharacter.AG
