/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.VnatGenuine

/-!
# M8h-0b: skew-symmetry of the adjoint `W̄` (DGM CMP 1996, eq. (4.9))

For homogeneous `t₁ ∈ TP_a`, `t₂ ∈ TP_b` (`TP = (V_Λ^T)^+`) the genuine adjoint
`W̄ = leechWbar` of the skew intertwiner `W` satisfies

  `W̄(t₁, z) t₂ = e^{zL₋₁} W̄(t₂, −z) t₁`,

i.e. in modes (library conventions `mode f n = f (−n−1)`)

  `W̄(t₁)₍ₙ₎ t₂ = ∑_{i ≥ 0} (1/i!) (−1)^{n+i+1} L₋₁ⁱ (W̄(t₂)₍ₙ₊ᵢ₎ t₁)`.

## Proof

Pair both sides with `φ ∈ (V_Λ^+)_k`, `k = a + b − n − 1`, under the nondegenerate invariant form
`leechBV` (`leechBV_gradedNondeg`).  Using

* the defining adjunction `leechWbar_adj'` (with its `(−1)^w`),
* the mode formula of `W(s)₍q₎φ = ∑_l (1/l!)(−1)^{q+l+1} L₋₁ˡ (φ₍q+l₎ s)`,
* `L₋₁ ⊣ L₁` for `TPForm` (`TPForm_Lm1`, from `TPForm_fhlInv` at `ω`, as `L₁ω = 0`) and for
  `leechBV` (`InvariantForm.virasoro_adj`),
* symmetry and FHL invariance of `TPForm` (`TPForm_symm`, `TPForm_fhlInv`),

both sides become triple sums of the matrix elements
`TPForm(L₁ʲ t₁, (L₁ʳ φ)₍γ₎ L₁ˡ t₂)`, which agree **term by term** after the relabelling
`(j, l, r) ↦ (r, l, j)` (`coeff_match`): the factorials match, the mode indices agree exactly
because `n = a + b − k − 1`, and the signs differ by an even power of `−1`.

## Main results
* `TPForm_Lm1` — `TPForm(L₋₁x, y) = TPForm(x, L₁y)`.
* `leechBV_Lm1_pow` — `B_V(L₋₁ⁱx, y) = B_V(x, L₁ⁱy)`.
* `leechWbar_skew` — the skew-symmetry for homogeneous `t₁, t₂` (any `n`).

## Status
`sorry`-free; no new hypotheses (homogeneity of `t₁, t₂` is a genuine restriction of the
statement, harmless since `TP` is graded and both sides are linear in each argument for fixed
weights).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.M8h0

open Module (End)
open VertexOperatorAlgebra SkewIntertwiner SkewAdjoint InvForm
open scoped BigOperators

/-! ## Sign bookkeeping -/

theorem negOnePow_eq_zpow (n : ℤ) : negOnePow n = (-1 : ℂ) ^ n := by
  unfold negOnePow
  split_ifs with h
  · rw [h.neg_one_zpow]
  · rw [(Int.not_even_iff_odd.mp h).neg_one_zpow]

theorem neg_one_zpow_eq_of_even_sub {x y : ℤ} (h : Even (x - y)) :
    (-1 : ℂ) ^ x = (-1 : ℂ) ^ y := by
  have : x = y + (x - y) := by ring
  rw [this, zpow_add₀ (by norm_num), h.neg_one_zpow, mul_one]

/-! ## `L₋₁ ⊣ L₁` for the two forms -/

theorem leechVOAPlus_L1_omega : leechVOAPlus.L 1 leechVOAPlus.conformalVector = 0 := by
  have h := L_one_lower leechVOAPlus leechVOAPlus.conformal_mem
  rw [show (2 : ℤ) - 1 = 1 by norm_num, leechVOAPlus_grading_one, Submodule.mem_bot] at h
  exact h

/-- `TPForm(L₋₁x, y) = TPForm(x, L₁y)`. -/
theorem TPForm_Lm1 (x y : TP) : TPForm (leechLTP x) y = TPForm x (Lp1 plusModule y) := by
  have h := TPForm_fhlInv leechVOAPlus.conformal_mem 0 x y
  have h1 : ((leechVOAPlus.L 1) ^ 1) leechVOAPlus.conformalVector = 0 := by
    rw [pow_one, leechVOAPlus_L1_omega]
  have h2 : ((leechVOAPlus.L 1) ^ 2) leechVOAPlus.conformalVector = 0 := by
    rw [pow_two, Module.End.mul_apply, leechVOAPlus_L1_omega, map_zero]
  rw [show ((2 : ℤ)).toNat + 1 = 3 by rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, h1, h2] at h
  have hm : ∀ k, mode (0 : FormalDist (End ℂ TP)) k = 0 := fun _ => rfl
  simp only [map_zero, hm, LinearMap.zero_apply, map_zero, smul_zero, add_zero, pow_zero,
    Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul] at h
  rw [show (2 : ℤ) * 2 - 0 - 2 - ((0 : ℕ) : ℤ) = 2 by norm_num] at h
  rw [show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num, one_smul] at h
  exact h

theorem TPForm_Lm1_pow (i : ℕ) (x y : TP) :
    TPForm x ((leechLTP ^ i) y) = TPForm ((Lp1 plusModule ^ i) x) y := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, TPForm_symm, TPForm_Lm1, TPForm_symm, ih,
      ← Module.End.mul_apply, ← pow_succ]

theorem leechBV_Lm1_pow (i : ℕ) (x y : SkewVP) :
    leechBV (((leechVOAPlus.L (-1)) ^ i) x) y = leechBV x (((leechVOAPlus.L 1) ^ i) y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    have hadj : ∀ a b : SkewVP, leechBV (leechVOAPlus.L (-1) a) b = leechBV a (leechVOAPlus.L 1 b) :=
      fun a b => by have := leechBVForm.virasoro_adj (-1) a b; rwa [neg_neg] at this
    rw [pow_succ', Module.End.mul_apply, hadj, ih, ← Module.End.mul_apply, ← pow_succ]

/-! ## Vanishing and range extension -/

theorem sum_range_extend {X : Type*} [AddCommMonoid X] (f : ℕ → X) {m₀ m : ℕ} (hm : m₀ ≤ m)
    (hf : ∀ r, m₀ ≤ r → f r = 0) :
    ∑ r ∈ Finset.range m, f r = ∑ r ∈ Finset.range m₀, f r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range d) fun r _ => hf _ (by omega),
    add_zero]

/-- Weight of a module mode applied to an `L₁`-power. -/
theorem act_Lp1_pow_eq_zero {c w : ℤ} {φ : SkewVP} (hφ : φ ∈ leechVOAPlus.grading c) {s : TP}
    (hs : s ∈ plusModule.weight (w : ℂ)) (j : ℕ) (p : ℤ)
    (hlt : w - j + c - p - 1 < lowB plusModule) :
    mode (plusModule.YM φ) p ((Lp1 plusModule ^ j) s) = 0 := by
  have h1 := Lp1_pow_mem plusModule hs j
  have h2 := mode_mem_weight plusModule hφ h1 p
  refine eq_zero_of_lt plusModule hlt ?_
  convert h2 using 2; push_cast; ring

/-- The `W` mode as a finite sum with the explicit summands. -/
theorem mode_leechWsk_eq_sum (s : TP) (q : ℤ) (φ : SkewVP) (K : ℕ)
    (hK : ∀ l : ℕ, K ≤ l → mode (plusModule.YM φ) (q + l) s = 0) :
    mode (leechWsk s) q φ = ∑ l ∈ Finset.range K,
      (((l.factorial : ℂ)⁻¹) * negOnePow (q + l + 1)) •
        ((leechLTP ^ l) (mode (plusModule.YM φ) (q + l) s)) := by
  rw [leechWsk, mode_Wsk, wModeLin_apply, wMode_eq_sum plusModule.toWeakModule K hK]
  rfl

/-! ## The two expansions -/

section Expand

variable {a b k : ℤ} {t t' : TP} {φ : SkewVP}

/-- The inner FHL step: `TPForm(t', L₋₁ˡ φ₍p₎ s) = (−1)^k ∑_r (1/r!) TPForm(s, (L₁ʳφ)₍2k−p−2−r₎ L₁ˡ t')`. -/
theorem inner_fhl (hφ : φ ∈ leechVOAPlus.grading k) (K : ℕ) (hKk : k.toNat < K) (s : TP) (p : ℤ) (l : ℕ) :
    TPForm t' ((leechLTP ^ l) (mode (plusModule.YM φ) p s))
      = (-1 : ℂ) ^ k * ∑ r ∈ Finset.range K, ((r.factorial : ℂ)⁻¹) *
          TPForm s (mode (plusModule.YM (((leechVOAPlus.L 1) ^ r) φ)) (2 * k - p - 2 - r)
            ((Lp1 plusModule ^ l) t')) := by
  rw [TPForm_Lm1_pow, TPForm_symm, TPForm_fhlInv hφ p s, smul_eq_mul]
  congr 1
  have hz : ∀ r, k.toNat + 1 ≤ r → ((r.factorial : ℂ)⁻¹) *
      TPForm s (mode (plusModule.YM (((leechVOAPlus.L 1) ^ r) φ)) (2 * k - p - 2 - r)
        ((Lp1 plusModule ^ l) t')) = 0 := by
    intro r hr
    rw [L_one_pow_eq_zero leechVOAPlus hφ (by omega), map_zero]
    have hm : ∀ m, mode (0 : FormalDist (End ℂ TP)) m = 0 := fun _ => rfl
    rw [hm, LinearMap.zero_apply, map_zero, mul_zero]
  rw [sum_range_extend _ (by omega : k.toNat + 1 ≤ K) hz]
  simp only [smul_eq_mul]

/-- **LHS expansion.** `B_V(W̄(t)₍ₙ₎t', φ)` as a triple sum of matrix elements. -/
theorem lhs_expand (ht : t ∈ plusModule.weight (a : ℂ))
    (hφ : φ ∈ leechVOAPlus.grading k) {n : ℤ} (hn : n = a + b - k - 1) (K : ℕ)
    (hKa : a - lowB plusModule < K) (hKb : b - lowB plusModule < K) (hKk : k.toNat < K) :
    leechBV (leechWbarMode n t t') φ
      = ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, ∑ r ∈ Finset.range K,
          ((-1 : ℂ) ^ a * (j.factorial : ℂ)⁻¹ *
            (((l.factorial : ℂ)⁻¹) * negOnePow (2 * a - n - 2 - j + l + 1)) *
            ((-1 : ℂ) ^ k * (r.factorial : ℂ)⁻¹)) *
          TPForm ((Lp1 plusModule ^ j) t)
            (mode (plusModule.YM (((leechVOAPlus.L 1) ^ r) φ))
              (2 * k - (2 * a - n - 2 - j + l) - 2 - r) ((Lp1 plusModule ^ l) t')) := by
  have hR : ∀ j : ℕ, K ≤ j → (Lp1 plusModule ^ j) t = 0 :=
    fun j hj => Lp1_pow_eq_zero plusModule ht (by omega)
  rw [leechWbar_adj' n ht K hR t' φ, smul_eq_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hK : ∀ l : ℕ, K ≤ l →
      mode (plusModule.YM φ) ((2 * a - n - 2 - j) + l) ((Lp1 plusModule ^ j) t) = 0 :=
    fun l hl => act_Lp1_pow_eq_zero hφ ht j _ (by omega)
  rw [mode_leechWsk_eq_sum _ _ _ K hK]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_fhl hφ K hKk]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- The right-hand side of the skew formula as a finite sum. -/
theorem rhs_eq_sum (ht : t ∈ plusModule.weight (a : ℂ)) (ht' : t' ∈ plusModule.weight (b : ℂ))
    {n : ℤ} (hn : n = a + b - k - 1) (K : ℕ) (hKk : k.toNat < K) :
    (∑ᶠ i : ℕ, (((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) •
        ((leechVOAPlus.L (-1)) ^ i) (leechWbarMode (n + i) t' t))
      = ∑ i ∈ Finset.range K, (((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) •
        ((leechVOAPlus.L (-1)) ^ i) (leechWbarMode (n + i) t' t) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  rw [Function.mem_support] at hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hiK
  apply hi
  have hmem := leechWbar_mem (n + i) ht' ht
  rw [leechVOAPlus.positivity _ (by omega), Submodule.mem_bot] at hmem
  rw [hmem, map_zero, smul_zero]

theorem rhs_mem (ht : t ∈ plusModule.weight (a : ℂ)) (ht' : t' ∈ plusModule.weight (b : ℂ))
    {n : ℤ} (hn : n = a + b - k - 1) :
    (∑ᶠ i : ℕ, (((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) •
        ((leechVOAPlus.L (-1)) ^ i) (leechWbarMode (n + i) t' t)) ∈ leechVOAPlus.grading k := by
  rw [rhs_eq_sum ht ht' hn (k.toNat + 1) (by omega)]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hmem := leechWbar_mem (n + i) ht' ht
  have h2 := L_neg_one_pow_raise leechVOAPlus hmem i
  convert h2 using 2; rw [hn]; ring

/-- **RHS expansion.** -/
theorem rhs_expand (ht : t ∈ plusModule.weight (a : ℂ)) (ht' : t' ∈ plusModule.weight (b : ℂ))
    (hφ : φ ∈ leechVOAPlus.grading k) {n : ℤ} (hn : n = a + b - k - 1) (K : ℕ)
    (hKa : a - lowB plusModule < K) (hKb : b - lowB plusModule < K) (hKk : k.toNat < K) :
    leechBV (∑ᶠ i : ℕ, (((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) •
        ((leechVOAPlus.L (-1)) ^ i) (leechWbarMode (n + i) t' t)) φ
      = ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ((((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) * ((-1 : ℂ) ^ b *
            (j.factorial : ℂ)⁻¹ *
            (((l.factorial : ℂ)⁻¹) * negOnePow (2 * b - (n + i) - 2 - j + l + 1)))) *
          TPForm ((Lp1 plusModule ^ l) t)
            (mode (plusModule.YM (((leechVOAPlus.L 1) ^ i) φ))
              (2 * b - (n + i) - 2 - j + l) ((Lp1 plusModule ^ j) t')) := by
  have hR : ∀ j : ℕ, K ≤ j → (Lp1 plusModule ^ j) t' = 0 :=
    fun j hj => Lp1_pow_eq_zero plusModule ht' (by omega)
  rw [rhs_eq_sum ht ht' hn K hKk, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, leechBV_Lm1_pow,
    leechWbar_adj' (n + i) ht' K hR t _, smul_eq_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hψ := L_one_pow_mem leechVOAPlus hφ i
  have hK : ∀ l : ℕ, K ≤ l → mode (plusModule.YM (((leechVOAPlus.L 1) ^ i) φ))
      ((2 * b - (n + i) - 2 - j) + l) ((Lp1 plusModule ^ j) t') = 0 :=
    fun l hl => act_Lp1_pow_eq_zero hψ ht' j _ (by omega)
  rw [mode_leechWsk_eq_sum _ _ _ K hK]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TPForm_symm, ← TPForm_Lm1_pow, TPForm_symm]
  ring

end Expand

/-! ## The skew-symmetry -/

theorem sum3_perm (s : Finset ℕ) (G : ℕ → ℕ → ℕ → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l = ∑ l ∈ s, ∑ j ∈ s, ∑ i ∈ s, G i j l := by
  calc ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l = ∑ i ∈ s, ∑ l ∈ s, ∑ j ∈ s, G i j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l ∈ s, ∑ i ∈ s, ∑ j ∈ s, G i j l := Finset.sum_comm
    _ = ∑ l ∈ s, ∑ j ∈ s, ∑ i ∈ s, G i j l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

/-- The termwise match of the two triple sums (`(j, l, r) ↦ (r, l, j)`). -/
theorem coeff_match {a b k n : ℤ} (hn : n = a + b - k - 1) (j l r : ℕ) :
    (-1 : ℂ) ^ a * (j.factorial : ℂ)⁻¹ *
        (((l.factorial : ℂ)⁻¹) * negOnePow (2 * a - n - 2 - j + l + 1)) *
        ((-1 : ℂ) ^ k * (r.factorial : ℂ)⁻¹)
      = (((r.factorial : ℂ)⁻¹) * negOnePow (n + r + 1)) * ((-1 : ℂ) ^ b *
          (l.factorial : ℂ)⁻¹ *
          (((j.factorial : ℂ)⁻¹) * negOnePow (2 * b - (n + r) - 2 - l + j + 1))) := by
  rw [negOnePow_eq_zpow, negOnePow_eq_zpow, negOnePow_eq_zpow]
  have hs : (-1 : ℂ) ^ a * (-1 : ℂ) ^ (2 * a - n - 2 - j + l + 1) * (-1 : ℂ) ^ k
      = (-1 : ℂ) ^ (n + r + 1) * (-1 : ℂ) ^ b * (-1 : ℂ) ^ (2 * b - (n + r) - 2 - l + j + 1) := by
    rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
      ← zpow_add₀ (by norm_num)]
    exact neg_one_zpow_eq_of_even_sub ⟨a - 2 * b + k - j + l, by omega⟩
  linear_combination ((r.factorial : ℂ)⁻¹ * (l.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹) * hs

/-- **Skew-symmetry of `W̄` (DGM (4.9))**: for homogeneous `t₁ ∈ TP_a`, `t₂ ∈ TP_b` and every
`n`, `W̄(t₁)₍ₙ₎t₂ = ∑_{i≥0} (1/i!)(−1)^{n+i+1} L₋₁ⁱ W̄(t₂)₍ₙ₊ᵢ₎t₁`, i.e.
`W̄(t₁,z)t₂ = e^{zL₋₁} W̄(t₂,−z)t₁`. -/
theorem leechWbar_skew {a b : ℤ} {t₁ t₂ : TP} (ht₁ : t₁ ∈ plusModule.weight (a : ℂ))
    (ht₂ : t₂ ∈ plusModule.weight (b : ℂ)) (n : ℤ) :
    leechWbarMode n t₁ t₂ = ∑ᶠ i : ℕ, (((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) •
      ((leechVOAPlus.L (-1)) ^ i) (leechWbarMode (n + i) t₂ t₁) := by
  set k : ℤ := a + b - n - 1 with hk
  have hn : n = a + b - k - 1 := by omega
  have hL : leechWbarMode n t₁ t₂ ∈ leechVOAPlus.grading k := by
    have := leechWbar_mem n ht₁ ht₂
    convert this using 2; omega
  have hR := rhs_mem ht₁ ht₂ (k := k) (n := n) (by omega)
  refine eq_of_form leechBV_orth leechBV_gradedNondeg fun φ => ?_
  have hφ : φ ∈ ⨆ c, leechVOAPlus.grading c := by
    rw [leechVOAPlus.isInternal.submodule_iSup_eq_top]; trivial
  induction hφ using Submodule.iSup_induction' with
  | mem c φ hφ =>
    by_cases hc : c = k
    · subst hc
      set K : ℕ := (a - lowB plusModule).toNat + (b - lowB plusModule).toNat + k.toNat + 1
      rw [lhs_expand ht₁ hφ hn K (by omega) (by omega) (by omega),
        rhs_expand ht₁ ht₂ hφ (by omega) K (by omega) (by omega) (by omega)]
      -- reorder `∑ᵢ∑ⱼ∑ₗ` into `∑ₗ∑ⱼ∑ᵢ`
      rw [sum3_perm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun r _ => ?_
      rw [coeff_match hn r l j,
        show 2 * k - (2 * a - n - 2 - (r : ℤ) + l) - 2 - j = 2 * b - (n + j) - 2 - l + r by omega]
    · rw [leechBV_orth k c (Ne.symm hc) _ hL _ hφ, leechBV_orth k c (Ne.symm hc) _ hR _ hφ]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

end VOA.Moonshine.M8h0
