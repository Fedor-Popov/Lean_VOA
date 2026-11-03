/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LogRemovalAdmissible

/-!
# The associator identities for products of intertwiners

For a product `F(w₁, w₂) = ⟨f, 𝒴₁(w₁, z₁) 𝒴₂(w₂, 1) w₃⟩` (`‖z₁‖ > 1`) and `u ∈ V`, `ℓ ∈ ℤ`
(in particular `ℓ < 0`), the iterate (associator) form of the Jacobi identity of `𝒴₁`
expresses the product with `w₁` replaced by `u_ℓ w₁` through products with the outside data
modified and with `w₂` replaced by `u_j w₂`, `j ≥ 0`:

`F(u_ℓ w₁, w₂; f, w₃) = Σᵢ (−1)ⁱ C(ℓ,i) z₁ⁱ F(w₁, w₂; f∘u_{ℓ−i}, w₃)`
`   − (−1)^ℓ Σᵢ (−1)ⁱ C(ℓ,i) z₁^{ℓ−i} F(w₁, w₂; f, uᵢ w₃)`
`   − (−1)^ℓ Σⱼ (−1)ʲ C(ℓ,j) (z₁ − 1)^{ℓ−j} F(w₁, uⱼ w₂; f, w₃)`

(all sums finite).  Coefficientwise the third sum is an infinite sum over `i` of finite sums;
summing over the line it becomes the binomial series `Σᵣ C(ℓ−j,r)(−1)ʳ z₁^{ℓ−j−r} = (z₁−1)^{ℓ−j}`
(`hasSum_cbz_pow`, `cbz_trinomial`), interchanged with the line sum by absolute convergence
(`tsum_conv`).  At `z₁ = 1 + u` the factor is `u^{ℓ−j}`: the inside–inside terms *preserve the
intermediate weight*, the outside terms gain `wt u − ℓ − 1`.  This is the identity behind the
uniform log-degree bound and the lower bound of the intermediate weights.

The mirror identity for `u_ℓ w₂` (right associator) reads
`F(w₁, u_ℓ w₂) = Σᵢ (−1)ⁱC(ℓ,i) F(f∘u_{ℓ−i}) − (−1)^ℓ Σᵢ (−1)ⁱC(ℓ,i) F(uᵢw₃)
   − Σᵣ C(ℓ,r) (z₁ − 1)^{ℓ−r} F(u_r w₁)`.

## Main results
* `cbz_trinomial`, `cbz_swap`, `hasSum_cbz_pow` (binomial series with integer exponent),
  `tsum_conv`, `hasSum_assocCoeff`, `hasSum_assocCoeff_right`.
* `prodCoeff_assoc_left`, `prodCoeff_assoc_right` (coefficientwise, finite sums).
* `prodValueZ_assoc_left`, `prodValueZ_assoc_right` (values, given summability).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.AssocAssociator

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules VOA.Huang.AssocCommutator
open Filter Topology
open scoped BigOperators

universe u

/-! ## Binomial coefficients with integer upper index -/

section Binom

theorem gBinom_succ (n : ℤ) (k : ℕ) :
    gBinom n (k + 1) = gBinom n k * (((n : ℂ) - k) / ((k : ℂ) + 1)) := by
  unfold gBinom
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  field_simp

theorem prod_range_falling_add (x : ℂ) (a b : ℕ) :
    (∏ t ∈ Finset.range (a + b), (x - (t : ℂ)))
      = (∏ t ∈ Finset.range a, (x - (t : ℂ))) * ∏ t ∈ Finset.range b, ((x - a) - (t : ℂ)) := by
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  push_cast; ring

theorem gBinom_natCast (a k : ℕ) : gBinom (a : ℤ) k = (a.choose k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [gBinom_succ, ih]
    have hk1 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    rcases lt_or_ge k a with hka | hka
    · have h := Nat.choose_succ_right_eq a k
      have hc : ((a.choose (k + 1) : ℂ)) * ((k : ℂ) + 1) = (a.choose k : ℂ) * ((a : ℂ) - k) := by
        have := congrArg (fun n : ℕ => (n : ℂ)) h
        push_cast [Nat.cast_sub hka.le] at this
        exact this
      field_simp
      push_cast
      linear_combination -hc
    · rw [Nat.choose_eq_zero_of_lt (by omega : a < k + 1)]
      rcases eq_or_lt_of_le hka with h | h
      · subst h; simp
      · rw [Nat.choose_eq_zero_of_lt h]; simp

/-- `C(ℓ,i) C(i,j) = C(ℓ,j) C(ℓ−j,i−j)` for `0 ≤ i, j`. -/
theorem cbz_trinomial (ℓ : ℤ) {i j : ℤ} (hi : 0 ≤ i) (hj : 0 ≤ j) :
    cbz ℓ i * cbz i j = cbz ℓ j * cbz (ℓ - j) (i - j) := by
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, i = a := ⟨i.toNat, (Int.toNat_of_nonneg hi).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, j = b := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
  rcases lt_or_ge a b with hab | hab
  · rw [cbz_apply_neg (ℓ - b) (by omega), mul_zero,
      cbz_apply_nonneg (a : ℤ) (show (0 : ℤ) ≤ (b : ℤ) by omega)]
    simp only [Int.toNat_natCast]
    rw [gBinom_natCast, Nat.choose_eq_zero_of_lt hab]
    simp
  · obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
    rw [cbz_apply_nonneg _ (by omega), cbz_apply_nonneg _ (by omega), cbz_apply_nonneg _ (by omega),
      cbz_apply_nonneg _ (by omega)]
    simp only [Int.toNat_natCast, show ((b + c : ℕ) : ℤ) - b = c by push_cast; ring,
      Int.toNat_natCast]
    rw [gBinom_natCast]
    have hb : ((b.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
    have hc : ((c.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero c
    have hbc : (((b + c).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hch : ((b + c).choose b : ℂ) * b.factorial * c.factorial = (b + c).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right b c)
      rw [Nat.add_sub_cancel_left] at this
      exact_mod_cast this
    have e1 := gBinom_mul_factorial ℓ (b + c)
    have e2 := gBinom_mul_factorial ℓ b
    have e3 := gBinom_mul_factorial (ℓ - b) c
    rw [prod_range_falling_add] at e1
    have e4 : (((ℓ - b : ℤ)) : ℂ) = (ℓ : ℂ) - b := by push_cast; ring
    rw [e4] at e3
    rw [← e2, ← e3] at e1
    -- e1 : (b+c)! * C(ℓ,b+c) = (b! C(ℓ,b)) (c! C(ℓ−b,c))
    apply mul_left_cancel₀ hbc
    linear_combination (↑((b + c).choose b) : ℂ) * e1
      + (gBinom ℓ b * gBinom (ℓ - b) c) * hch

/-- Summability of the binomial series `Σᵣ C(a,r) yʳ` for `‖y‖ < 1`. -/
theorem summable_cbz_pow (a : ℤ) {y : ℂ} (hy : ‖y‖ < 1) :
    Summable fun r : ℕ => cbz a r * y ^ r := by
  set q : ℝ := (1 + ‖y‖) / 2 with hq
  have hq1 : q < 1 := by rw [hq]; linarith
  refine summable_of_ratio_norm_eventually_le hq1 ?_
  -- `|a − r| / (r + 1) ‖y‖ ≤ q` eventually
  have hlim : Tendsto (fun r : ℕ => ‖((a : ℂ) - r) / ((r : ℂ) + 1)‖) atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℕ => ((a : ℂ) - r) / ((r : ℂ) + 1)) atTop (𝓝 (-1)) := by
      have e : (fun r : ℕ => ((a : ℂ) - r) / ((r : ℂ) + 1))
          = fun r : ℕ => ((a : ℂ) + 1) / ((r : ℂ) + 1) - 1 := by
        funext r
        have : ((r : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero r
        field_simp; ring
      rw [e]
      have h0 : Tendsto (fun r : ℕ => ((a : ℂ) + 1) / ((r : ℂ) + 1)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa [div_eq_mul_one_div ((a : ℂ) + 1)] using this.const_mul ((a : ℂ) + 1)
      simpa using h0.sub_const 1
    simpa using h1.norm
  have hpos : ‖y‖ < q := by rw [hq]; linarith
  rcases eq_or_ne y 0 with hy0 | hy0
  · have hq0 : 0 ≤ q := by rw [hq]; positivity
    refine Eventually.of_forall fun r => ?_
    simp only [hy0, pow_succ, mul_zero, norm_zero]
    exact mul_nonneg hq0 (norm_nonneg _)
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hev : ∀ᶠ r : ℕ in atTop, ‖((a : ℂ) - r) / ((r : ℂ) + 1)‖ < q / ‖y‖ :=
    hlim.eventually (gt_mem_nhds (by rw [lt_div_iff₀ hyn, one_mul]; exact hpos))
  filter_upwards [hev] with r hr
  rw [cbz_apply_nonneg _ (by omega), cbz_apply_nonneg _ (by omega)]
  simp only [Int.toNat_natCast, show ((r + 1 : ℕ) : ℤ).toNat = r + 1 from Int.toNat_natCast _]
  rw [gBinom_succ, pow_succ]
  rw [show gBinom a r * (((a : ℂ) - r) / ((r : ℂ) + 1)) * (y ^ r * y)
      = (gBinom a r * y ^ r) * ((((a : ℂ) - r) / ((r : ℂ) + 1)) * y) by ring,
    norm_mul, norm_mul, mul_comm q]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [lt_div_iff₀ hyn] at hr
  rw [norm_mul]
  exact hr.le

/-- **The binomial series with integer exponent**: `Σᵣ C(a,r) yʳ = (1 + y)^a`, `‖y‖ < 1`. -/
theorem hasSum_cbz_pow (a : ℤ) {y : ℂ} (hy : ‖y‖ < 1) :
    HasSum (fun r : ℕ => cbz a r * y ^ r) ((1 + y) ^ a) := by
  have hy1 : (1 + y) ≠ 0 := by
    intro h
    have : y = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hy
    exact lt_irrefl _ hy
  -- `S(a) = (1 + y) S(a − 1)` by Pascal
  have step : ∀ a : ℤ, ∑' r : ℕ, cbz a r * y ^ r
      = (1 + y) * ∑' r : ℕ, cbz (a - 1) r * y ^ r := by
    intro a
    have hs := summable_cbz_pow (a - 1) hy
    have e : ∀ r : ℕ, cbz a r * y ^ r
        = cbz (a - 1) r * y ^ r + (if r = 0 then 0 else y * (cbz (a - 1) (r - 1 : ℕ) * y ^ (r - 1)))
        := by
      intro r
      rw [cbz_pascal a r]
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp [cbz_apply_neg (a - 1) (show (-1 : ℤ) < 0 by norm_num)]
      · rw [if_neg (by omega), show ((r : ℤ) - 1) = ((r - 1 : ℕ) : ℤ) by omega]
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
    have hs2 : Summable fun r : ℕ =>
        (if r = 0 then 0 else y * (cbz (a - 1) (r - 1 : ℕ) * y ^ (r - 1))) := by
      rw [← summable_nat_add_iff 1]
      simpa using hs.mul_left y
    rw [tsum_congr e, hs.tsum_add hs2, hs2.tsum_eq_zero_add]
    simp only [if_true, zero_add, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    rw [tsum_mul_left]
    ring
  have h0 : ∑' r : ℕ, cbz 0 r * y ^ r = 1 := by
    rw [tsum_eq_single 0 (fun r hr => by
      rw [cbz_zero_left, if_neg (by exact_mod_cast hr), zero_mul])]
    simp
  have key : ∀ a : ℤ, ∑' r : ℕ, cbz a r * y ^ r = (1 + y) ^ a := by
    intro a
    induction a using Int.induction_on with
    | zero => rw [h0, zpow_zero]
    | succ n ih =>
      rw [step, show ((n : ℤ) + 1 - 1) = n by ring, ih, zpow_add_one₀ hy1]
      ring
    | pred n ih =>
      have h := step (-(n : ℤ))
      rw [ih] at h
      rw [zpow_sub_one₀ hy1, h, mul_comm, ← mul_assoc, inv_mul_cancel₀ hy1, one_mul]
  rw [← key a]
  exact (summable_cbz_pow a hy).hasSum

end Binom

/-! ## Convolution of an absolutely convergent series with a line sum -/

/-- `Σ_k Σ_i aᵢ T(k − i) = (Σ aᵢ)(Σ T)`, for summable `a` (on `ℕ`) and `T` (on `ℤ`). -/
theorem tsum_conv (a : ℕ → ℂ) (ha : Summable a) (T : ℤ → ℂ) (hT : Summable T) :
    Summable (fun k : ℤ => ∑' i : ℕ, a i * T (k - i))
      ∧ ∑' k : ℤ, ∑' i : ℕ, a i * T (k - i) = (∑' i, a i) * ∑' k, T k := by
  have ha' : Summable fun i => ‖a i‖ := (summable_norm_iff (E := ℂ)).mpr ha
  have hT' : Summable fun k => ‖T k‖ := (summable_norm_iff (E := ℂ)).mpr hT
  have hP : Summable fun p : ℕ × ℤ => a p.1 * T p.2 := summable_mul_of_summable_norm ha' hT'
  let e : ℕ × ℤ ≃ ℤ × ℕ :=
    { toFun := fun p => (p.2 + p.1, p.1)
      invFun := fun q => (q.2, q.1 - q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  set F : ℤ × ℕ → ℂ := fun q => a q.2 * T (q.1 - q.2) with hF
  have hFe : F ∘ e = fun p : ℕ × ℤ => a p.1 * T p.2 := by
    funext p; simp [hF, e]
  have hFs : Summable F := by
    rw [← e.summable_iff, hFe]; exact hP
  refine ⟨hFs.prod, ?_⟩
  rw [← hFs.tsum_prod' (fun k => hFs.prod_factor k), ← e.tsum_eq,
    show (fun c => F (e c)) = fun p : ℕ × ℤ => a p.1 * T p.2 from hFe,
    tsum_mul_tsum_of_summable_norm ha' hT']

/-! ## Sums over `ℤ` supported in `[0, R)` -/

theorem finsum_eq_sum_range {X : Type*} [AddCommMonoid X] {g : ℤ → X} {R : ℕ}
    (hneg : ∀ i < 0, g i = 0) (hbig : ∀ i : ℤ, (R : ℤ) ≤ i → g i = 0) :
    ∑ᶠ i : ℤ, g i = ∑ i ∈ Finset.range R, g i := by
  rw [finsum_eq_sum_of_support_subset (s := (Finset.range R).map Nat.castEmbedding) g ?_,
    Finset.sum_map]
  · rfl
  · intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    have h0 : 0 ≤ i := by by_contra h; exact hi (hneg i (by omega))
    refine ⟨i.toNat, ?_, by simp [Int.toNat_of_nonneg h0]⟩
    by_contra h; exact hi (hbig i (by omega))

theorem sum_range_eq_of_vanish {X : Type*} [AddCommMonoid X] {g : ℕ → X} {R R' : ℕ}
    (hR : R' ≤ R) (h : ∀ i, R' ≤ i → g i = 0) :
    ∑ i ∈ Finset.range R, g i = ∑ i ∈ Finset.range R', g i := by
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hR) fun i hi hi' => ?_).symm
  simp only [Finset.mem_range, not_lt] at hi'
  exact h i hi'

/-! ## The associator identity, coefficientwise -/

section Coeff

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}

/-- A truncation bound valid for finitely many indices at once. -/
theorem exists_uniform_bound (N : ℕ) (P : ℕ → ℤ → Prop) (h : ∀ j, ∃ R : ℤ, ∀ i, R ≤ i → P j i) :
    ∃ R : ℕ, ∀ j < N, ∀ i : ℤ, (R : ℤ) ≤ i → P j i := by
  choose Rf hRf using h
  refine ⟨∑ j ∈ Finset.range N, (Rf j).toNat, fun j hj i hi => hRf j i ?_⟩
  have h1 : (Rf j).toNat ≤ ∑ j ∈ Finset.range N, (Rf j).toNat :=
    Finset.single_le_sum (f := fun j => (Rf j).toNat) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hj)
  have h2 : Rf j ≤ ((Rf j).toNat : ℤ) := Int.self_le_toNat _
  omega

/-- **The left associator identity, coefficientwise**: for `u ∈ V`, `ℓ ∈ ℤ`,
`⟨f, (u_ℓ w₁)_n (w₂)_{n₂} w₃⟩ = Σᵢ (−1)ⁱC(ℓ,i) ⟨f∘u_{ℓ−i}, (w₁)_{n+i}(w₂)_{n₂}w₃⟩
  − (−1)^ℓ Σᵢ (−1)ⁱC(ℓ,i) ⟨f, (w₁)_{ℓ+n−i}(w₂)_{n₂} uᵢw₃⟩
  − (−1)^ℓ Σⱼ Σᵢ (−1)ⁱC(ℓ,i)C(i,j) ⟨f, (w₁)_{ℓ+n−i}(uⱼw₂)_{i+n₂−j} w₃⟩`
(the inner `i`-sum has finite support). -/
theorem prodCoeff_assoc_left {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {NA N₂ N₃ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (A₄.YM u) (ℓ - i) = 0)
    (h₂ : ∀ j : ℕ, N₂ ≤ j → mode (A₂.YM u) j w₂ = 0)
    (h₃ : ∀ i : ℕ, N₃ ≤ i → mode (A₃.YM u) i w₃ = 0) (n n₂ : ℂ) :
    prodCoeff Y₁ Y₂ f (mode (A₁.YM u) ℓ w₁) w₂ w₃ n n₂
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃ (n + i) n₂
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃) (ℓ + n - i) n₂
        - negOnePow ℓ * ∑ j ∈ Finset.range N₂, ∑' i : ℕ, negOnePow i * cbz ℓ i * cbz i j
          * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (ℓ + n - i) (i + n₂ - j) := by
  set q := Y₂ n₂ w₂ w₃ with hq
  -- truncation bounds
  obtain ⟨R₁, hR₁⟩ := hY₁.truncation w₁ q n
  obtain ⟨R₂, hR₂⟩ := A₅.truncation u q
  obtain ⟨R₃, hR₃⟩ := exists_uniform_bound N₂
    (fun j i => Y₂ (i + n₂ - j) (mode (A₂.YM u) j w₂) w₃ = 0)
    (fun j => by
      obtain ⟨R, hR⟩ := hY₂.truncation (mode (A₂.YM u) j w₂) w₃ (n₂ - j)
      exact ⟨R, fun i hi => by
        have := hR i hi
        rwa [show n₂ - (j : ℂ) + (i : ℂ) = (i : ℂ) + n₂ - j by ring] at this⟩)
  set R : ℕ := R₁.toNat + R₂.toNat + R₃ + NA + N₃ with hR
  -- the Jacobi identity at `(ℓ, 0, n)`
  have J := hY₁.jacobi u w₁ q ℓ 0 n
  have hRHS := finsum_eq_single (fun i : ℤ =>
      cbz 0 i • Y₁ (((0 : ℤ) : ℂ) + n - i) (mode (A₁.YM u) (ℓ + i) w₁) q) 0
    (fun i hi => by simp only; rw [cbz_zero_left, if_neg hi, zero_smul])
  have hLHS := finsum_eq_sum_range (R := R) (g := fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (mode (A₄.YM u) (ℓ + 0 - i) (Y₁ (n + i) w₁ q)
        - negOnePow ℓ • Y₁ (ℓ + n - i) w₁ (mode (A₅.YM u) (0 + i) q)))
    (fun i hi => by simp only; rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul])
    (fun i hi => by
      have e1 : Y₁ (n + i) w₁ q = 0 := hR₁ i (by omega)
      have e2 : mode (A₅.YM u) (0 + i) q = 0 := hR₂ _ (by omega)
      simp only
      rw [e1, e2, map_zero, map_zero, smul_zero, sub_zero, smul_zero])
  rw [hRHS, hLHS] at J
  have J' := congrArg f J
  simp only [cbz_zero, one_smul, add_zero, zero_add, map_sum, map_smul, map_sub,
    smul_eq_mul] at J'
  -- the commutator for `uᵢ q`
  have hcomm : ∀ i : ℕ, f (Y₁ (ℓ + n - i) w₁ (mode (A₅.YM u) i q))
      = prodCoeff Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃) (ℓ + n - i) n₂
        + ∑ j ∈ Finset.range N₂, cbz i j
          * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (ℓ + n - i) (i + n₂ - j) := by
    intro i
    have c := hY₂.commutator u w₂ w₃ i n₂
    rw [finsum_eq_sum_range (R := N₂) (fun j hj => by rw [cbz_apply_neg _ hj, zero_smul])
      (fun j hj => by
        obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' := ⟨j.toNat, by omega⟩
        rw [h₂ j' (by exact_mod_cast hj), map_zero, LinearMap.zero_apply, smul_zero])] at c
    rw [sub_eq_iff_eq_add'] at c
    rw [hq, c]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, prodCoeff]
    congr 1
  -- assemble
  have hsplit : ∀ i : ℕ, (negOnePow i * cbz ℓ i) * (f (mode (A₄.YM u) (ℓ - i) (Y₁ (n + i) w₁ q))
        - negOnePow ℓ * f (Y₁ (ℓ + n - i) w₁ (mode (A₅.YM u) i q)))
      = negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃ (n + i) n₂
        - negOnePow ℓ * (negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃) (ℓ + n - i) n₂)
        - negOnePow ℓ * ∑ j ∈ Finset.range N₂, negOnePow i * cbz ℓ i * cbz i j
          * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (ℓ + n - i) (i + n₂ - j) := by
    intro i
    rw [hcomm i]
    have hs : ∑ j ∈ Finset.range N₂, negOnePow i * cbz ℓ i * cbz i j
          * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (ℓ + n - i) (i + n₂ - j)
        = negOnePow i * cbz ℓ i * ∑ j ∈ Finset.range N₂, cbz i j
          * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (ℓ + n - i) (i + n₂ - j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    simp only [prodCoeff, LinearMap.comp_apply]
    ring
  simp only [Int.cast_natCast, Int.cast_zero, zero_add, sub_zero] at J'
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at J'
  rw [Finset.sum_comm] at J'
  have hRA : NA ≤ R := by omega
  have hR3 : N₃ ≤ R := by omega
  rw [sum_range_eq_of_vanish hRA (fun i hi => by
      simp only [prodCoeff, hA i hi, LinearMap.zero_apply, mul_zero]),
    sum_range_eq_of_vanish hR3 (fun i hi => by
      simp only [prodCoeff, h₃ i hi, map_zero, mul_zero])] at J'
  have hC : ∀ j ∈ Finset.range N₂, ∑ i ∈ Finset.range R, negOnePow i * cbz ℓ i * cbz i j
        * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (ℓ + n - i) (i + n₂ - j)
      = ∑' i : ℕ, negOnePow i * cbz ℓ i * cbz i j
        * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (ℓ + n - i) (i + n₂ - j) := by
    intro j hj
    refine (tsum_eq_sum fun i hi => ?_).symm
    simp only [Finset.mem_range, not_lt] at hi hj
    have := hR₃ j hj i (by omega)
    simp only [Int.cast_natCast] at this
    simp only [prodCoeff, this, map_zero, mul_zero]
  rw [Finset.sum_congr rfl hC] at J'
  exact J'.symm

/-! ## The geometric resummation -/

/-- `Σᵢ (−1)ⁱ C(ℓ,i) C(i,j) z^{ℓ−i} = (−1)ʲ C(ℓ,j) (z − 1)^{ℓ−j}` for `‖z‖ > 1`. -/
theorem hasSum_assocCoeff (ℓ : ℤ) (j : ℕ) {z : ℂ} (hz : 1 < ‖z‖) :
    HasSum (fun i : ℕ => negOnePow i * cbz ℓ i * cbz i j * z ^ (ℓ - i))
      (negOnePow j * cbz ℓ j * (z - 1) ^ (ℓ - j)) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hy : ‖-z⁻¹‖ < 1 := by rw [norm_neg, norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have H := (hasSum_cbz_pow (ℓ - j) hy).mul_left (negOnePow j * cbz ℓ j * z ^ (ℓ - j))
  have e : negOnePow j * cbz ℓ j * z ^ (ℓ - j) * (1 + -z⁻¹) ^ (ℓ - j)
      = negOnePow j * cbz ℓ j * (z - 1) ^ (ℓ - j) := by
    rw [mul_assoc, ← mul_zpow]
    congr 2
    field_simp
    ring
  rw [e] at H
  rw [← hasSum_nat_add_iff' j]
  have hzero : ∑ i ∈ Finset.range j, negOnePow i * cbz ℓ i * cbz i j * z ^ (ℓ - i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [cbz_apply_nonneg (i : ℤ) (by omega), Int.toNat_natCast, gBinom_natCast,
      Nat.choose_eq_zero_of_lt hi]
    simp
  rw [hzero, sub_zero]
  convert H using 1
  funext r
  have ht := cbz_trinomial ℓ (i := ((r + j : ℕ) : ℤ)) (j := (j : ℤ)) (by omega) (by omega)
  rw [show ((r + j : ℕ) : ℤ) - (j : ℤ) = (r : ℤ) by push_cast; ring] at ht
  rw [mul_assoc (negOnePow _), ht, show (((r + j : ℕ) : ℤ)) = (j : ℤ) + (r : ℤ) by push_cast; ring,
    negOnePow_add, negOnePow_natCast r, cbz_apply_nonneg (ℓ - j) (by omega : (0 : ℤ) ≤ r),
    Int.toNat_natCast, show ℓ - ((j : ℤ) + (r : ℤ)) = (ℓ - j) - (r : ℤ) by ring,
    zpow_sub₀ hz0, zpow_natCast]
  simp only [neg_pow (z⁻¹), inv_pow]
  field_simp

/-- **The left associator identity for values** (`z₂ = 1`, `‖z₁‖ > 1`), given summability of
the right-hand lines. -/
theorem prodValueZ_assoc_left {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {NA N₂ N₃ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (A₄.YM u) (ℓ - i) = 0)
    (h₂ : ∀ j : ℕ, N₂ ≤ j → mode (A₂.YM u) j w₂ = 0)
    (h₃ : ∀ i : ℕ, N₃ ≤ i → mode (A₃.YM u) i w₃ = 0) (S ν z₁ : ℂ) (hz : 1 < ‖z₁‖)
    (sA : ∀ i : ℕ, Summable (prodTermZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃
      (S + ((i : ℤ) : ℂ)) ν z₁ 1))
    (s₃ : ∀ i : ℕ, Summable (prodTermZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃)
      (S + ((ℓ - i : ℤ) : ℂ)) ν z₁ 1))
    (s₂ : ∀ j : ℕ, Summable (prodTermZ Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃
      (S + ((ℓ - j : ℤ) : ℂ)) (ν - j) z₁ 1)) :
    prodValueZ Y₁ Y₂ f (mode (A₁.YM u) ℓ w₁) w₂ w₃ S ν z₁ 1
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i * z₁ ^ (i : ℤ)
          * prodValueZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃ (S + ((i : ℤ) : ℂ)) ν z₁ 1
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i * z₁ ^ (ℓ - i)
          * prodValueZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃) (S + ((ℓ - i : ℤ) : ℂ)) ν z₁ 1
        - negOnePow ℓ * ∑ j ∈ Finset.range N₂, negOnePow j * cbz ℓ j * (z₁ - 1) ^ (ℓ - j)
          * prodValueZ Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃ (S + ((ℓ - j : ℤ) : ℂ)) (ν - j)
              z₁ 1 := by
  have hz0 : z₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  set TA : ℕ → ℤ → ℂ := fun i => prodTermZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃
    (S + ((i : ℤ) : ℂ)) ν z₁ 1 with hTA
  set TB : ℕ → ℤ → ℂ := fun i => prodTermZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃)
    (S + ((ℓ - i : ℤ) : ℂ)) ν z₁ 1 with hTB
  set TC : ℕ → ℤ → ℂ := fun j => prodTermZ Y₁ Y₂ f w₁ (mode (A₂.YM u) j w₂) w₃
    (S + ((ℓ - j : ℤ) : ℂ)) (ν - j) z₁ 1 with hTC
  set γ : ℕ → ℕ → ℂ := fun j i => negOnePow i * cbz ℓ i * cbz i j * z₁ ^ (ℓ - i) with hγ
  -- the identity term by term
  have hk : ∀ k : ℤ, prodTermZ Y₁ Y₂ f (mode (A₁.YM u) ℓ w₁) w₂ w₃ S ν z₁ 1 k
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i * z₁ ^ (i : ℤ) * TA i k
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i * z₁ ^ (ℓ - i) * TB i k
        - negOnePow ℓ * ∑ j ∈ Finset.range N₂, ∑' i : ℕ, γ j i * TC j (k - i) := by
    intro k
    simp only [prodTermZ, Complex.one_cpow, mul_one]
    rw [prodCoeff_assoc_left hY₁ hY₂ u ℓ f w₁ w₂ w₃ hA h₂ h₃ (S - ν + k) (ν - k)]
    rw [sub_mul, sub_mul, Finset.sum_mul, mul_assoc, Finset.sum_mul, mul_assoc,
      Finset.sum_mul]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hTA, prodTermZ, Complex.one_cpow, mul_one]
        have e1 : S - ν + (k : ℂ) + (i : ℂ) = S + ((i : ℤ) : ℂ) - ν + k := by push_cast; ring
        rw [e1, ← cpow_shift hz0 (S + ((i : ℤ) : ℂ) - ν + k) (-(i : ℤ)), Complex.cpow_intCast]
        rw [show S + ((i : ℤ) : ℂ) - ν + k + ((-(i : ℤ) : ℤ) : ℂ) = S - ν + k by push_cast; ring]
        rw [zpow_neg]
        field_simp
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hTB, prodTermZ, Complex.one_cpow, mul_one]
        have e1 : (ℓ : ℂ) + (S - ν + k) - (i : ℂ) = S + ((ℓ - i : ℤ) : ℂ) - ν + k := by
          push_cast; ring
        rw [e1, ← cpow_shift hz0 (S + ((ℓ - i : ℤ) : ℂ) - ν + k) (-(ℓ - i)),
          Complex.cpow_intCast]
        rw [show S + ((ℓ - i : ℤ) : ℂ) - ν + k + ((-(ℓ - i) : ℤ) : ℂ) = S - ν + k by
          push_cast; ring]
        rw [zpow_neg]
        field_simp
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← tsum_mul_right]
      refine tsum_congr fun i => ?_
      simp only [hTC, hγ, prodTermZ, Complex.one_cpow, mul_one]
      have e1 : (ℓ : ℂ) + (S - ν + k) - (i : ℂ)
          = S + ((ℓ - j : ℤ) : ℂ) - (ν - j) + ((k - i : ℤ) : ℂ) := by push_cast; ring
      have e2 : (i : ℂ) + (ν - k) - (j : ℂ) = ν - j - ((k - i : ℤ) : ℂ) := by push_cast; ring
      rw [e1, e2, ← cpow_shift hz0 (S + ((ℓ - j : ℤ) : ℂ) - (ν - j) + ((k - i : ℤ) : ℂ))
        (-(ℓ - i)), Complex.cpow_intCast]
      rw [show S + ((ℓ - j : ℤ) : ℂ) - (ν - j) + ((k - i : ℤ) : ℂ) + ((-(ℓ - i) : ℤ) : ℂ)
          = S - ν + k by push_cast; ring]
      rw [zpow_neg]
      field_simp
  -- summability and the line sums
  have hγs : ∀ j, HasSum (γ j) (negOnePow j * cbz ℓ j * (z₁ - 1) ^ (ℓ - j)) :=
    fun j => hasSum_assocCoeff ℓ j hz
  have hconv : ∀ j, Summable (fun k : ℤ => ∑' i : ℕ, γ j i * TC j (k - i))
      ∧ ∑' k : ℤ, ∑' i : ℕ, γ j i * TC j (k - i) = (∑' i, γ j i) * ∑' k, TC j k :=
    fun j => tsum_conv (γ j) (hγs j).summable (TC j) (s₂ j)
  have sA' : Summable fun k => ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i * z₁ ^ (i : ℤ)
      * TA i k := summable_sum fun i _ => (sA i).mul_left _
  have sB' : Summable fun k => negOnePow ℓ * ∑ i ∈ Finset.range N₃,
      negOnePow i * cbz ℓ i * z₁ ^ (ℓ - i) * TB i k :=
    (summable_sum fun i _ => (s₃ i).mul_left _).mul_left _
  have sC' : Summable fun k => negOnePow ℓ * ∑ j ∈ Finset.range N₂,
      ∑' i : ℕ, γ j i * TC j (k - i) :=
    (summable_sum fun j _ => (hconv j).1).mul_left _
  unfold prodValueZ
  rw [tsum_congr hk, (sA'.sub sB').tsum_sub sC', sA'.tsum_sub sB', tsum_mul_left,
    tsum_mul_left, Summable.tsum_finsetSum (fun i _ => (sA i).mul_left _),
    Summable.tsum_finsetSum (fun i _ => (s₃ i).mul_left _),
    Summable.tsum_finsetSum (fun j _ => (hconv j).1)]
  simp only [tsum_mul_left]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hconv j).2, (hγs j).tsum_eq]

/-! ## The right associator identity -/

/-- `C(ℓ,i) C(ℓ−i,r) = C(ℓ,r) C(ℓ−r,i)` for `0 ≤ i, r`. -/
theorem cbz_swap (ℓ : ℤ) (i r : ℕ) :
    cbz ℓ i * cbz (ℓ - i) r = cbz ℓ r * cbz (ℓ - r) i := by
  rw [cbz_apply_nonneg _ (by omega), cbz_apply_nonneg _ (by omega), cbz_apply_nonneg _ (by omega),
    cbz_apply_nonneg _ (by omega)]
  simp only [Int.toNat_natCast]
  have hi : ((i.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hr : ((r.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have e1 := gBinom_mul_factorial ℓ i
  have e2 := gBinom_mul_factorial (ℓ - i) r
  have e3 := gBinom_mul_factorial ℓ r
  have e4 := gBinom_mul_factorial (ℓ - r) i
  have p1 := prod_range_falling_add (ℓ : ℂ) i r
  have p2 := prod_range_falling_add (ℓ : ℂ) r i
  rw [add_comm r i] at p2
  have c1 : (((ℓ - i : ℤ)) : ℂ) = (ℓ : ℂ) - i := by push_cast; ring
  have c2 : (((ℓ - r : ℤ)) : ℂ) = (ℓ : ℂ) - r := by push_cast; ring
  rw [c1] at e2
  rw [c2] at e4
  apply mul_left_cancel₀ (mul_ne_zero hi hr)
  linear_combination ((r.factorial : ℂ) * gBinom (ℓ - i) r) * e1
    + (∏ t ∈ Finset.range i, ((ℓ : ℂ) - (t : ℂ))) * e2
    - ((i.factorial : ℂ) * gBinom (ℓ - r) i) * e3
    - (∏ t ∈ Finset.range r, ((ℓ : ℂ) - (t : ℂ))) * e4 - p1 + p2

/-- `Σᵢ (−1)ⁱ C(ℓ,i) C(ℓ−i,r) z^{ℓ−r−i} = C(ℓ,r) (z − 1)^{ℓ−r}` for `‖z‖ > 1`. -/
theorem hasSum_assocCoeff_right (ℓ : ℤ) (r : ℕ) {z : ℂ} (hz : 1 < ‖z‖) :
    HasSum (fun i : ℕ => negOnePow i * cbz ℓ i * cbz (ℓ - i) r * z ^ (ℓ - r - i))
      (cbz ℓ r * (z - 1) ^ (ℓ - r)) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hy : ‖-z⁻¹‖ < 1 := by rw [norm_neg, norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have H := (hasSum_cbz_pow (ℓ - r) hy).mul_left (cbz ℓ r * z ^ (ℓ - r))
  have e : cbz ℓ r * z ^ (ℓ - r) * (1 + -z⁻¹) ^ (ℓ - r) = cbz ℓ r * (z - 1) ^ (ℓ - r) := by
    rw [mul_assoc, ← mul_zpow]
    congr 2
    field_simp
    ring
  rw [e] at H
  convert H using 1
  funext i
  rw [mul_assoc (negOnePow _), cbz_swap, negOnePow_natCast, zpow_sub₀ hz0, zpow_natCast,
    cbz_apply_nonneg (ℓ - r) (by omega : (0 : ℤ) ≤ i), Int.toNat_natCast]
  simp only [neg_pow (z⁻¹), inv_pow]
  field_simp

/-- **The right associator identity, coefficientwise**:
`⟨f, (w₁)_n (u_ℓ w₂)_{n₂} w₃⟩ = Σᵢ (−1)ⁱC(ℓ,i) ⟨f∘u_{ℓ−i}, (w₁)_n(w₂)_{n₂+i}w₃⟩
  − (−1)^ℓ Σᵢ (−1)ⁱC(ℓ,i) ⟨f, (w₁)_n(w₂)_{ℓ+n₂−i} uᵢw₃⟩
  − Σᵣ Σᵢ (−1)ⁱC(ℓ,i)C(ℓ−i,r) ⟨f, (u_r w₁)_{ℓ−i+n−r}(w₂)_{n₂+i} w₃⟩`. -/
theorem prodCoeff_assoc_right {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {NA N₁ N₃ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (A₄.YM u) (ℓ - i) = 0)
    (h₁ : ∀ r : ℕ, N₁ ≤ r → mode (A₁.YM u) r w₁ = 0)
    (h₃ : ∀ i : ℕ, N₃ ≤ i → mode (A₃.YM u) i w₃ = 0) (n n₂ : ℂ) :
    prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM u) ℓ w₂) w₃ n n₂
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃ n (n₂ + i)
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃) n (ℓ + n₂ - i)
        - ∑ r ∈ Finset.range N₁, ∑' i : ℕ, negOnePow i * cbz ℓ i * cbz (ℓ - i) r
          * prodCoeff Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (ℓ - i + n - r) (n₂ + i) := by
  obtain ⟨R₁, hR₁⟩ := hY₂.truncation w₂ w₃ n₂
  set R : ℕ := R₁.toNat + NA + N₃ with hR
  have J := hY₂.jacobi u w₂ w₃ ℓ 0 n₂
  have hRHS := finsum_eq_single (fun i : ℤ =>
      cbz 0 i • Y₂ (((0 : ℤ) : ℂ) + n₂ - i) (mode (A₂.YM u) (ℓ + i) w₂) w₃) 0
    (fun i hi => by simp only; rw [cbz_zero_left, if_neg hi, zero_smul])
  have hLHS := finsum_eq_sum_range (R := R) (g := fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (mode (A₅.YM u) (ℓ + 0 - i) (Y₂ (n₂ + i) w₂ w₃)
        - negOnePow ℓ • Y₂ (ℓ + n₂ - i) w₂ (mode (A₃.YM u) (0 + i) w₃)))
    (fun i hi => by simp only; rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul])
    (fun i hi => by
      have e1 : Y₂ (n₂ + i) w₂ w₃ = 0 := hR₁ i (by omega)
      obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
      have e2 : mode (A₃.YM u) (0 + (i' : ℤ)) w₃ = 0 := by
        rw [zero_add]; exact h₃ i' (by omega)
      simp only
      rw [e1, e2, map_zero, map_zero, smul_zero, sub_zero, smul_zero])
  rw [hRHS, hLHS] at J
  have J' := congrArg (fun x => f (Y₁ n w₁ x)) J
  simp only [cbz_zero, one_smul, add_zero, zero_add, map_sum, map_smul, map_sub,
    smul_eq_mul, Int.cast_natCast, Int.cast_zero, sub_zero] at J'
  -- the commutator of `u_{ℓ−i}` with `Y₁`
  have hcomm : ∀ i : ℕ, f (Y₁ n w₁ (mode (A₅.YM u) (ℓ - i) (Y₂ (n₂ + i) w₂ w₃)))
      = prodCoeff Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃ n (n₂ + i)
        - ∑ r ∈ Finset.range N₁, cbz (ℓ - i) r
          * prodCoeff Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (ℓ - i + n - r) (n₂ + i) := by
    intro i
    have c := hY₁.commutator u w₁ (Y₂ (n₂ + i) w₂ w₃) (ℓ - i) n
    rw [finsum_eq_sum_range (R := N₁) (fun r hr => by rw [cbz_apply_neg _ hr, zero_smul])
      (fun r hr => by
        obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
        rw [h₁ r' (by exact_mod_cast hr), map_zero, LinearMap.zero_apply, smul_zero])] at c
    rw [sub_eq_iff_eq_add'] at c
    have c' := congrArg f c
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at c'
    simp only [prodCoeff, LinearMap.comp_apply]
    rw [c']
    simp only [Int.cast_natCast, Int.cast_sub]
    ring_nf
  have hsplit : ∀ i : ℕ, (negOnePow i * cbz ℓ i)
        * (f (Y₁ n w₁ (mode (A₅.YM u) (ℓ - i) (Y₂ (n₂ + i) w₂ w₃)))
          - negOnePow ℓ * f (Y₁ n w₁ (Y₂ (ℓ + n₂ - i) w₂ (mode (A₃.YM u) i w₃))))
      = negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃ n (n₂ + i)
        - negOnePow ℓ * (negOnePow i * cbz ℓ i
          * prodCoeff Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃) n (ℓ + n₂ - i))
        - ∑ r ∈ Finset.range N₁, negOnePow i * cbz ℓ i * cbz (ℓ - i) r
          * prodCoeff Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (ℓ - i + n - r) (n₂ + i) := by
    intro i
    rw [hcomm i]
    have hs : ∑ r ∈ Finset.range N₁, negOnePow i * cbz ℓ i * cbz (ℓ - i) r
          * prodCoeff Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (ℓ - i + n - r) (n₂ + i)
        = negOnePow i * cbz ℓ i * ∑ r ∈ Finset.range N₁, cbz (ℓ - i) r
          * prodCoeff Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (ℓ - i + n - r) (n₂ + i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
    rw [hs]
    simp only [prodCoeff]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum] at J'
  rw [Finset.sum_comm] at J'
  have hRA : NA ≤ R := by omega
  have hR3 : N₃ ≤ R := by omega
  rw [sum_range_eq_of_vanish hRA (fun i hi => by
      simp only [prodCoeff, hA i hi, LinearMap.zero_apply, mul_zero]),
    sum_range_eq_of_vanish hR3 (fun i hi => by
      simp only [prodCoeff, h₃ i hi, map_zero, mul_zero])] at J'
  have hC : ∀ r ∈ Finset.range N₁, ∑ i ∈ Finset.range R, negOnePow i * cbz ℓ i * cbz (ℓ - i) r
        * prodCoeff Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (ℓ - i + n - r) (n₂ + i)
      = ∑' i : ℕ, negOnePow i * cbz ℓ i * cbz (ℓ - i) r
        * prodCoeff Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (ℓ - i + n - r) (n₂ + i) := by
    intro r _
    refine (tsum_eq_sum fun i hi => ?_).symm
    simp only [Finset.mem_range, not_lt] at hi
    have := hR₁ i (by omega)
    simp only [Int.cast_natCast] at this
    simp only [prodCoeff, this, map_zero, mul_zero]
  rw [Finset.sum_congr rfl hC] at J'
  exact J'.symm

/-- **The right associator identity for values** (`z₂ = 1`, `‖z₁‖ > 1`), given summability
of the right-hand lines. -/
theorem prodValueZ_assoc_right {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {NA N₁ N₃ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (A₄.YM u) (ℓ - i) = 0)
    (h₁ : ∀ r : ℕ, N₁ ≤ r → mode (A₁.YM u) r w₁ = 0)
    (h₃ : ∀ i : ℕ, N₃ ≤ i → mode (A₃.YM u) i w₃ = 0) (S ν z₁ : ℂ) (hz : 1 < ‖z₁‖)
    (sA : ∀ i : ℕ, Summable (prodTermZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃
      (S + ((i : ℤ) : ℂ)) (ν + ((i : ℤ) : ℂ)) z₁ 1))
    (s₃ : ∀ i : ℕ, Summable (prodTermZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃)
      (S + ((ℓ - i : ℤ) : ℂ)) (ν + ((ℓ - i : ℤ) : ℂ)) z₁ 1))
    (s₁ : ∀ r : ℕ, Summable (prodTermZ Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃
      (S + ((ℓ - r : ℤ) : ℂ)) ν z₁ 1)) :
    prodValueZ Y₁ Y₂ f w₁ (mode (A₂.YM u) ℓ w₂) w₃ S ν z₁ 1
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i
          * prodValueZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃ (S + ((i : ℤ) : ℂ))
              (ν + ((i : ℤ) : ℂ)) z₁ 1
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
          * prodValueZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃) (S + ((ℓ - i : ℤ) : ℂ))
              (ν + ((ℓ - i : ℤ) : ℂ)) z₁ 1
        - ∑ r ∈ Finset.range N₁, cbz ℓ r * (z₁ - 1) ^ (ℓ - r)
          * prodValueZ Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃ (S + ((ℓ - r : ℤ) : ℂ)) ν z₁ 1 := by
  have hz0 : z₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  set TA : ℕ → ℤ → ℂ := fun i => prodTermZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM u) (ℓ - i)) w₁ w₂ w₃
    (S + ((i : ℤ) : ℂ)) (ν + ((i : ℤ) : ℂ)) z₁ 1 with hTA
  set TB : ℕ → ℤ → ℂ := fun i => prodTermZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM u) i w₃)
    (S + ((ℓ - i : ℤ) : ℂ)) (ν + ((ℓ - i : ℤ) : ℂ)) z₁ 1 with hTB
  set TC : ℕ → ℤ → ℂ := fun r => prodTermZ Y₁ Y₂ f (mode (A₁.YM u) r w₁) w₂ w₃
    (S + ((ℓ - r : ℤ) : ℂ)) ν z₁ 1 with hTC
  set γ : ℕ → ℕ → ℂ := fun r i => negOnePow i * cbz ℓ i * cbz (ℓ - i) r * z₁ ^ (ℓ - r - i)
    with hγ
  have hk : ∀ k : ℤ, prodTermZ Y₁ Y₂ f w₁ (mode (A₂.YM u) ℓ w₂) w₃ S ν z₁ 1 k
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i * TA i k
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i * TB i k
        - ∑ r ∈ Finset.range N₁, ∑' i : ℕ, γ r i * TC r (k - i) := by
    intro k
    simp only [prodTermZ, Complex.one_cpow, mul_one]
    rw [prodCoeff_assoc_right hY₁ hY₂ u ℓ f w₁ w₂ w₃ hA h₁ h₃ (S - ν + k) (ν - k)]
    rw [sub_mul, sub_mul, Finset.sum_mul, mul_assoc, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hTA, prodTermZ, Complex.one_cpow, mul_one]
        rw [show S + ((i : ℤ) : ℂ) - (ν + ((i : ℤ) : ℂ)) + k = S - ν + k by ring,
          show ν + ((i : ℤ) : ℂ) - k = ν - k + i by push_cast; ring]
        ring
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hTB, prodTermZ, Complex.one_cpow, mul_one]
        rw [show S + ((ℓ - i : ℤ) : ℂ) - (ν + ((ℓ - i : ℤ) : ℂ)) + k = S - ν + k by ring,
          show ν + ((ℓ - i : ℤ) : ℂ) - k = ℓ + (ν - k) - i by push_cast; ring]
        ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [← tsum_mul_right]
      refine tsum_congr fun i => ?_
      simp only [hTC, hγ, prodTermZ, Complex.one_cpow, mul_one]
      have e1 : (ℓ : ℂ) - (i : ℂ) + (S - ν + k) - (r : ℂ)
          = S + ((ℓ - r : ℤ) : ℂ) - ν + ((k - i : ℤ) : ℂ) := by push_cast; ring
      have e2 : ν - k + (i : ℂ) = ν - ((k - i : ℤ) : ℂ) := by push_cast; ring
      rw [e1, e2, ← cpow_shift hz0 (S + ((ℓ - r : ℤ) : ℂ) - ν + ((k - i : ℤ) : ℂ))
        (-(ℓ - r - i)), Complex.cpow_intCast]
      rw [show S + ((ℓ - r : ℤ) : ℂ) - ν + ((k - i : ℤ) : ℂ) + ((-(ℓ - r - i) : ℤ) : ℂ)
          = S - ν + k by push_cast; ring]
      rw [zpow_neg]
      field_simp
  have hγs : ∀ r, HasSum (γ r) (cbz ℓ r * (z₁ - 1) ^ (ℓ - r)) :=
    fun r => hasSum_assocCoeff_right ℓ r hz
  have hconv : ∀ r, Summable (fun k : ℤ => ∑' i : ℕ, γ r i * TC r (k - i))
      ∧ ∑' k : ℤ, ∑' i : ℕ, γ r i * TC r (k - i) = (∑' i, γ r i) * ∑' k, TC r k :=
    fun r => tsum_conv (γ r) (hγs r).summable (TC r) (s₁ r)
  have sA' : Summable fun k => ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i * TA i k :=
    summable_sum fun i _ => (sA i).mul_left _
  have sB' : Summable fun k => negOnePow ℓ * ∑ i ∈ Finset.range N₃,
      negOnePow i * cbz ℓ i * TB i k :=
    (summable_sum fun i _ => (s₃ i).mul_left _).mul_left _
  have sC' : Summable fun k => ∑ r ∈ Finset.range N₁, ∑' i : ℕ, γ r i * TC r (k - i) :=
    summable_sum fun r _ => (hconv r).1
  unfold prodValueZ
  rw [tsum_congr hk, (sA'.sub sB').tsum_sub sC', sA'.tsum_sub sB', tsum_mul_left,
    Summable.tsum_finsetSum (fun i _ => (sA i).mul_left _),
    Summable.tsum_finsetSum (fun i _ => (s₃ i).mul_left _),
    Summable.tsum_finsetSum (fun r _ => (hconv r).1)]
  simp only [tsum_mul_left]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [(hconv r).2, (hγs r).tsum_eq]

end Coeff

end VOA.Huang.AssocAssociator
