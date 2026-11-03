/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.WbarDeriv
import VOA.Modules.ContragredientClose

/-!
# `W̄`: the dagger commutator identity  (Moonshine step M8c, `W̄` part 4)

The form-free heart of the intertwining property of `W̄`.  For a **quasi-primary**
`u ∈ 𝒱_p` (`L₁u = 0`), `t ∈ M_w` and `Q = 2p − m − 2`, the dagger `W†` of the skew intertwiner
satisfies (`Wdag_comm_qp`)

  `(−1)^p (W†(t)₍ₙ₎ u₍Q₎ − u₍Q₎ W†(t)₍ₙ₎) = ∑_{r<J} C(m,r) W†(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎`,

the transpose (`u₍ₘ₎ ↦ (−1)^p u₍Q₎` is the FHL contragredient of a quasi-primary mode) of the
commutator formula of `W̄`.  Proof: the commutator formula of `W` (`wMode_comm`) on each
`L₁ʲt`, the `L₁`-expansion `L₁ᵏ(u₍ᵣ₎t) = ∑ C(k,b)·(2p−r−2)^{(c)}·u₍ᵣ₊c₎L₁ᵇt` (`Lp1_pow_act_qp`),
and the Vandermonde identity `∑_r (−1)^r C(m,r) C(N−r, s−r) = C(N−m, s)` (`vandermonde_neg`).

## Status
All declarations proved; no `sorry`/axioms.  Unconditional (no forms are involved).
-/

namespace VOA.Moonshine.SkewAdjoint

open Module (End Dual)
open VertexOperatorAlgebra SkewIntertwiner InvForm
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Finite-sum bookkeeping -/

section Sums

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- Regrouping a double sum along `s = r + c`. -/
theorem regroup (K : ℕ) (h : ℕ → ℕ → ℂ) (T : ℕ → X) (hT : ∀ s, K ≤ s → T s = 0) :
    ∑ r ∈ Finset.range K, ∑ c ∈ Finset.range K, h r c • T (r + c)
      = ∑ s ∈ Finset.range K, (∑ r ∈ Finset.range (s + 1), h r (s - r)) • T s := by
  simp_rw [Finset.sum_smul]
  have e : ∀ s ∈ Finset.range K, ∑ r ∈ Finset.range (s + 1), h r (s - r) • T s
      = ∑ r ∈ Finset.range (s + 1), h r (s - r) • T (r + (s - r)) := by
    intro s _
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [Nat.add_sub_cancel' (by omega)]
  rw [Finset.sum_congr rfl e, Finset.sum_range_diag_flip K (fun r c => h r c • T (r + c))]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun c _ hc => ?_).symm
  rw [Finset.mem_range, not_lt] at hc
  rw [hT _ (by omega), smul_zero]

omit [Module ℂ X] in
/-- An antidiagonal sum over `k < K` as a double range sum (terms with `b + c ≥ K` vanishing). -/
theorem antidiag_range (K : ℕ) (g : ℕ → ℕ → X) (hg : ∀ b c, K ≤ b + c → g b c = 0) :
    ∑ k ∈ Finset.range K, ∑ q ∈ Finset.antidiagonal k, g q.1 q.2
      = ∑ b ∈ Finset.range K, ∑ c ∈ Finset.range K, g b c := by
  simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_diag_flip K g]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun c _ hc => ?_
  rw [Finset.mem_range, not_lt] at hc
  exact hg b c (by omega)

end Sums

theorem gBinom_succ_mul' (n : ℤ) (i : ℕ) :
    gBinom n (i + 1) * ((i : ℂ) + 1) = (n : ℂ) * gBinom (n - 1) i := by
  have hf : ((i.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  refine mul_left_cancel₀ hf ?_
  have h1 := gBinom_mul_factorial n (i + 1)
  have h2 := gBinom_mul_factorial (n - 1) i
  rw [Nat.factorial_succ, Finset.prod_range_succ'] at h1
  push_cast at h1 h2
  have h3 : ∏ k ∈ Finset.range i, ((n : ℂ) - ((k : ℂ) + 1)) = ∏ k ∈ Finset.range i, ((n : ℂ) - 1 - k) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [h3, ← h2] at h1
  linear_combination h1

theorem negOne_zpow_sub_nat (a : ℤ) (r : ℕ) : (-1 : ℂ) ^ (a - (r : ℤ)) = (-1 : ℂ) ^ a * (-1 : ℂ) ^ r := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast]
  have : ((-1 : ℂ) ^ r)⁻¹ = (-1 : ℂ) ^ r := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [div_eq_mul_inv, this]

/-! ## The `L₁`-expansion of `L₁ᵏ(u₍ᵣ₎x)` for quasi-primary `u` -/

/-- For `u ∈ 𝒱_p` with `L₁u = 0`:
`(1/k!) L₁ᵏ(u₍ᵣ₎x) = ∑_{b+c=k} (1/b!) C(2p−r−2, c) u₍ᵣ₊c₎ L₁ᵇx`. -/
theorem Lp1_pow_act_qp (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqp : W.L 1 u = 0) (r : ℤ) (x : M) (k : ℕ) :
    ((k.factorial : ℂ)⁻¹) • (Lp1 N ^ k) (N.act u r x)
      = ∑ q ∈ Finset.antidiagonal k, (((q.1.factorial : ℂ)⁻¹) * gBinom (2 * p - r - 2) q.2) •
          N.act u (r + q.2) ((Lp1 N ^ q.1) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ∀ (c : ℕ) (y : M), Lp1 N (N.act u (r + c) y)
        = N.act u (r + c) (Lp1 N y) + ((2 * p - (r + c) - 2 : ℤ) : ℂ) • N.act u (r + (c + 1 : ℕ)) y := by
      intro c y
      rw [Lp1_act N hu, hqp]
      simp only [WeakModule.act_def, map_zero, mode_zero, LinearMap.zero_apply, add_zero]
      congr 3; push_cast; ring_nf
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have e : (((k + 1).factorial : ℂ)⁻¹) • (Lp1 N ^ (k + 1)) (N.act u r x)
        = ((k : ℂ) + 1)⁻¹ • Lp1 N (((k.factorial : ℂ)⁻¹) • (Lp1 N ^ k) (N.act u r x)) := by
      rw [map_smul, smul_smul, pow_succ', Module.End.mul_apply, Nat.factorial_succ]
      congr 1; push_cast; rw [mul_inv]
    rw [e, ih, map_sum]
    simp_rw [map_smul, hstep, smul_add]
    rw [Finset.sum_add_distrib]
    -- target: split `(k+1)·coef` as `b' + c'`
    have hsplit : ∑ q ∈ Finset.antidiagonal (k + 1),
        (((q.1.factorial : ℂ)⁻¹) * gBinom (2 * p - r - 2) q.2) • N.act u (r + q.2) ((Lp1 N ^ q.1) x)
        = ((k : ℂ) + 1)⁻¹ • ∑ q ∈ Finset.antidiagonal (k + 1),
          (((q.1 : ℂ) + q.2) * (((q.1.factorial : ℂ)⁻¹) * gBinom (2 * p - r - 2) q.2)) •
            N.act u (r + q.2) ((Lp1 N ^ q.1) x) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_antidiagonal] at hq
      rw [smul_smul, ← mul_assoc, show ((q.1 : ℂ) + q.2) = (k : ℂ) + 1 by exact_mod_cast hq,
        inv_mul_cancel₀ hk1, one_mul]
    rw [hsplit]
    congr 1
    simp_rw [add_mul, add_smul]
    rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ']
    simp only [Nat.cast_zero, zero_mul, zero_smul, zero_add]
    congr 1
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Module.End.mul_apply, ← pow_succ']
      congr 1
      rw [Nat.factorial_succ]
      have hf : ((q.1.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q.1
      have h1 : ((q.1 : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q.1
      push_cast
      field_simp
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_smul]
      congr 1
      have hfall := gBinom_falling (2 * p - r - 2) q.2
      push_cast at hfall ⊢
      linear_combination (-((q.1.factorial : ℂ)⁻¹)) * hfall

/-! ## The dagger commutator identity -/

theorem wMode_finset_sum (A : WeakModule W M) {ι : Type*} (S : Finset ι) (f : ι → M) (n : ℤ)
    (φ : 𝒱) : wMode A (∑ i ∈ S, f i) n φ = ∑ i ∈ S, wMode A (f i) n φ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [wMode_zero_right]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, wMode_add_right, ih]

/-- **The dagger commutator identity** for a quasi-primary `u ∈ 𝒱_p` and `t ∈ M_w`
(`Q = 2p − m − 2`, `J` past the truncation of `u` on `t`):
`(−1)^p (W†(t)₍ₙ₎(u₍Q₎φ) − u₍Q₎W†(t)₍ₙ₎φ) = ∑_{r<J} C(m,r) W†(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎φ`. -/
theorem Wdag_comm_qp (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqp : W.L 1 u = 0) {w : ℤ} {t : M} (ht : t ∈ N.weight (w : ℂ)) (m n : ℤ) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → N.act u j t = 0) (φ : 𝒱) :
    (-1 : ℂ) ^ p • (Wdag N n t (W.smul u (2 * p - m - 2) φ)
        - N.act u (2 * p - m - 2) (Wdag N n t φ))
      = ∑ r ∈ Finset.range J, gBinom m r • Wdag N (m + n - r) (N.act u r t) φ := by
  set A := N.toWeakModule with hA
  set L := lowB N
  set K : ℕ := (p + w - L).toNat + (w - L).toNat + J + 2 with hK
  set Q := 2 * p - m - 2 with hQ
  have hK1 : ∀ j : ℕ, K ≤ j → (Lp1 N ^ j) t = 0 := fun j hj =>
    Lp1_pow_eq_zero N ht (by omega)
  have hvanish : ∀ b s : ℕ, K ≤ b + s → N.act u s ((Lp1 N ^ b) t) = 0 := by
    intro b s hbs
    refine eq_zero_of_lt N (k := p + (w - b) - s - 1) (by omega) ?_
    have h := mode_mem_weight N hu (Lp1_pow_mem N ht b) s
    convert h using 2; push_cast; ring
  have hmem_r : ∀ r : ℕ, N.act u r t ∈ N.weight (((p + w - r - 1 : ℤ)) : ℂ) := by
    intro r
    have h := mode_mem_weight N hu ht r
    convert h using 2; push_cast; ring
  have hvan_r : ∀ r k : ℕ, K ≤ k → (Lp1 N ^ k) (N.act u r t) = 0 := fun r k hk =>
    Lp1_pow_eq_zero N (hmem_r r) (by omega)
  -- the common terms
  set T : ℕ → ℕ → M := fun b s => ((b.factorial : ℂ)⁻¹) •
    wMode A (N.act u s ((Lp1 N ^ b) t)) (2 * p + 2 * w - m - n - 4 - b - s) φ with hT
  have hTvan : ∀ b s : ℕ, K ≤ s → T b s = 0 := by
    intro b s hs
    simp only [hT]; rw [hvanish b s (by omega), wMode_zero_right, smul_zero]
  /- LHS -/
  have hLHS : (-1 : ℂ) ^ p • (Wdag N n t (W.smul u Q φ) - N.act u Q (Wdag N n t φ))
      = ∑ b ∈ Finset.range K, ∑ s ∈ Finset.range K,
          (-((-1 : ℂ) ^ p * (-1 : ℂ) ^ w) * gBinom Q s) • T b s := by
    rw [Wdag_int_eq_sum N n ht K hK1, Wdag_int_eq_sum N n ht K hK1]
    simp only [WeakModule.act_def, map_smul, map_sum]
    rw [← smul_sub, ← Finset.sum_sub_distrib, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_sub]
    have hc := wMode_comm A u Q ((Lp1 N ^ b) t) (2 * w - n - 2 - b) φ K
      (fun s hs => hvanish b s (by omega))
    simp only [WeakModule.act_def] at hc
    rw [← neg_sub, hc, smul_neg, smul_neg, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hT, smul_smul, WeakModule.act_def]
    rw [← neg_smul]
    congr 1
    · ring
    · congr 1; ring
  /- RHS -/
  set h : ℕ → ℕ → ℂ := fun r c => gBinom m r * (-1 : ℂ) ^ (p + w - r - 1) *
    gBinom (2 * p - r - 2) c with hh
  have hRHS : ∑ r ∈ Finset.range J, gBinom m r • Wdag N (m + n - r) (N.act u r t) φ
      = ∑ b ∈ Finset.range K, ∑ s ∈ Finset.range K,
          (∑ r ∈ Finset.range (s + 1), h r (s - r)) • T b s := by
    rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega : J ≤ K)) (fun r _ hr => by
      rw [Finset.mem_range, not_lt] at hr
      rw [hJ r hr, map_zero, LinearMap.zero_apply, smul_zero])]
    have hr1 : ∀ r ∈ Finset.range K, gBinom m r • Wdag N (m + n - r) (N.act u r t) φ
        = ∑ b ∈ Finset.range K, ∑ c ∈ Finset.range K, h r c • T b (r + c) := by
      intro r _
      rw [Wdag_int_eq_sum N (m + n - r) (hmem_r r) K (hvan_r r)]
      have hk : ∀ k ∈ Finset.range K, ((k.factorial : ℂ)⁻¹) • wMode A ((Lp1 N ^ k) (N.act u r t))
          (2 * (p + w - r - 1) - (m + n - r) - 2 - k) φ
          = ∑ q ∈ Finset.antidiagonal k, (((q.1.factorial : ℂ)⁻¹) * gBinom (2 * p - r - 2) q.2) •
            wMode A (N.act u ((r + q.2 : ℕ) : ℤ) ((Lp1 N ^ q.1) t))
              (2 * p + 2 * w - m - n - 4 - q.1 - (r + q.2 : ℕ)) φ := by
        intro k _
        rw [← wMode_smul_right, Lp1_pow_act_qp N hu hqp, wMode_finset_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [Finset.mem_antidiagonal] at hq
        rw [wMode_smul_right]
        congr 2; rw [← hq]; push_cast; ring
      rw [Finset.sum_congr rfl hk, antidiag_range K (fun b c =>
          (((b.factorial : ℂ)⁻¹) * gBinom (2 * p - r - 2) c) •
            wMode A (N.act u ((r + c : ℕ) : ℤ) ((Lp1 N ^ b) t))
              (2 * p + 2 * w - m - n - 4 - b - (r + c : ℕ)) φ) (fun b c hbc => by
        dsimp only
        rw [hvanish b (r + c) (by omega), wMode_zero_right, smul_zero]), Finset.smul_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hT, hh, smul_smul]
      congr 1
      ring
    rw [Finset.sum_congr rfl hr1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact regroup K h (T b) (hTvan b)
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun s _ => ?_
  congr 1
  -- the Vandermonde collapse
  have hv := vandermonde_neg m (2 * p - 2) s
  have e : ∀ r ∈ Finset.range (s + 1), h r (s - r)
      = (-1 : ℂ) ^ (p + w - 1) * ((-1 : ℂ) ^ r * gBinom m r * gBinom (2 * p - 2 - r) (s - r)) := by
    intro r _
    simp only [hh]
    rw [show p + w - (r : ℤ) - 1 = (p + w - 1) - r by ring, negOne_zpow_sub_nat,
      show 2 * p - (r : ℤ) - 2 = 2 * p - 2 - r by ring]
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hv, hQ, show 2 * p - 2 - m = 2 * p - m - 2 by ring,
    zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

end VOA.Moonshine.SkewAdjoint
