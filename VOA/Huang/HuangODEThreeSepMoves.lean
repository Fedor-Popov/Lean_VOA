import VOA.Huang.HuangODEThreeSepCoeff

/-!
# The three insertion moves for the normalized three-intertwiner series

The C₁ relations `u₋₁ wᵢ` (`i = 1, 2, 3`) as identities of double series with
coefficients in `sepRing = ℂ[x, y, (1-x)⁻¹, (1-y)⁻¹, (1-xy)⁻¹]` (`x = z₂/z₁`,
`y = z₃/z₂`), for the total-level normalization of `HuangODEThree.normalizedSeries`.
Every term on the right has strictly smaller total external level. Together with the
proved terminal and dual moves (`normalizedSeries_terminal`, `normalizedSeries_dual`)
these are the five moves of the five-slot filtration induction.

Coefficient series that occur (`B_k = Σ C(i,k) tⁱ`):
* third insertion: `(xy)^{2(d+i)}` (output), `(-1)^k xy B_k(xy)` (first), `(-1)^k y B_k(y)`
  (second), `1` (terminal);
* second insertion: `x^{2(d+i)} y^{2d+i}` (output), `(-1)^k x B_k(x) y^{k+1}` (first),
  `y^{1+i}` (terminal), `y B_k(y)` (third);
* first insertion: `(xy)^{2d+i}` (output), `(xy)^{1+i}` (terminal), `xy B_k(xy)` (third),
  `x B_k(x) y^{k+1}` (second).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop PowerSeries VOA.Huang.HuangODEThree
open VOA.Huang.HuangODEProduct VOA.Huang.HuangODEModes
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {A₅ : OrdVModule W M₅} {A₆ : OrdVModule W M₆}
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {Y₂ : IntertwiningModes M₂ M₅ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

theorem prod3_vec_congr (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    {p p' q q' r r' : ℂ} (hp : p = p') (hq : q = q') (hr : r = r') :
    Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄)) = Y₁ p' w₁ (Y₂ q' w₂ (Y₃ r' w₃ w₄)) := by
  rw [hp, hq, hr]

theorem prod3_congr (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    {p p' q q' r r' : ℂ} (hp : p = p') (hq : q = q') (hr : r = r') :
    f (Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄))) = f (Y₁ p' w₁ (Y₂ q' w₂ (Y₃ r' w₃ w₄))) := by
  rw [hp, hq, hr]

/-- **Third insertion move** (`u₋₁ w₃`): a regular relation lowering the total level. -/
theorem normalizedSeries_third
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ (mode (A₃.YM u) (-1) w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d) + N₄) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), X ^ (2 * (d + i)) * PowerSeries.C (X ^ (2 * (d + i))) *
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + i))
        ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)
    - ∑ k ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ k) •
      (ιxy (X * HuangODEAlgebra.binomSeries 1 k) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄))
    - ∑ k ∈ Finset.range (N₂ + d), ((-1 : ℂ) ^ k) •
      (ιy (X * HuangODEAlgebra.binomSeries 1 k) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
    + ∑ i ∈ Finset.range (N₄ + d),
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ w₃ (mode (A₄.YM u) i w₄) N₀
        (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (i + 1))) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_sub, c2_sub, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries]
  unfold normalizedCoeff productCoeff
  set s := N₀ + N₁ + N₂ + (N₃ + d) + N₄ with hs
  obtain ⟨T, hT⟩ := hY₃.truncation w₃ w₄ (μ + (s : ℂ) - n)
  have hT' := Int.self_le_toNat T
  set I := T.toNat + N₀ + N₄ + d + m + n + 1 with hI
  rw [product_third_neg_one hY₁ hY₂ hY₃ u f w₁ w₂ w₃ w₄ _ _ _ (N₁ + N₂ + d) I
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun i hi => ⟨hT i (by omega), mode_eq_zero_of_le hl₄ hu hw₄ (by omega)⟩)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) ?_ ?_) ?_) ?_
  · -- output terms
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun i hi => by
      rw [eq_zero_of_mem_weight_neg hl₀ (product_mem_weight hY₁ hY₂ hY₃ hw₁ hw₂ hw₃ hw₄ _ _ _)
        (j := (N₀ : ℤ) - d - i) (by rw [hC, hs]; push_cast; ring) (by omega), map_zero,
        map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄]
    unfold normalizedCoeff productCoeff
    rw [LinearMap.comp_apply]
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ)) v)) (prod3_vec_congr w₁ w₂ w₃ w₄
      ?_ ?_ ?_)
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i ≤ N₀ by omega)]
      push_cast; ring
  · -- first insertion terms
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₁ + d) (by omega) (fun k hk => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_ιxy_binom_normalized hB (by omega) hw₂ hw₃ hw₄ _ _ _ _ k m n (k + I)
      (by omega), Finset.sum_range_add (n := k) (m := I),
      Finset.sum_eq_zero (s := Finset.range k) (fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj), Nat.cast_zero, zero_mul]),
      zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_neg_one_sub, add_comm i k, mul_assoc]
    congr 2
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₁ + d by omega)]
      push_cast; ring
  · -- second insertion terms
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_ιy_binom_normalized hB (by omega) (mode_mem_weight_nat hu hw₂ hk') hw₃ hw₄
      _ _ _ _ k m n (k + I) (by omega), Finset.sum_range_add (n := k) (m := I),
      Finset.sum_eq_zero (s := Finset.range k) (fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj), Nat.cast_zero, zero_mul]),
      zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_neg_one_sub, add_comm i k, mul_assoc]
    congr 2
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₂ + d by omega)]
      push_cast; ring
  · -- terminal terms
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_normalizedSeries]
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · ring
    · ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₄ + d by omega)]
      push_cast; ring

/-- **Second insertion move** (`u₋₁ w₂`): a regular relation lowering the total level. -/
theorem normalizedSeries_second
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ (mode (A₂.YM u) (-1) w₂) w₃ w₄ N₀ (N₀ + N₁ + (N₂ + d) + N₃ + N₄) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), X ^ (2 * (d + i)) * PowerSeries.C (X ^ (2 * d + i)) *
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + i))
        ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)
    - ∑ k ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ k) •
      (ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄)))
    + ∑ i ∈ Finset.range (N₄ + d), X ^ 0 * PowerSeries.C (X ^ (i + 1)) *
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ w₃ (mode (A₄.YM u) i w₄) N₀
        (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (i + 1)))
    + ∑ k ∈ Finset.range (N₃ + d),
      ιy (X * HuangODEAlgebra.binomSeries 1 k) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) k w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (k + 1)) + N₄) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_add, c2_sub, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries]
  unfold normalizedCoeff productCoeff
  set s := N₀ + N₁ + (N₂ + d) + N₃ + N₄ with hs
  obtain ⟨T, hT⟩ := hY₂.truncation w₂ (Y₃ (μ + (s : ℂ) - n) w₃ w₄) (ν - μ - m + n)
  obtain ⟨T₅, hT₅⟩ := A₅.truncation u (Y₃ (μ + (s : ℂ) - n) w₃ w₄)
  have hT' := Int.self_le_toNat T
  have hT₅' := Int.self_le_toNat T₅
  set I := T.toNat + T₅.toNat + N₀ + N₄ + d + m + n + 1 with hI
  rw [product_second_neg_one hY₁ hY₂ hY₃ u f w₁ w₂ w₃ w₄ _ _ _ (N₁ + N₃ + d) I
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun i hi => ⟨hT i (by omega), hT₅ i (by omega)⟩)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· - ·) ?_ ?_) ?_) ?_
  · -- output terms
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun i hi => by
      rw [eq_zero_of_mem_weight_neg hl₀ (product_mem_weight hY₁ hY₂ hY₃ hw₁ hw₂ hw₃ hw₄ _ _ _)
        (j := (N₀ : ℤ) - d - i) (by rw [hC, hs]; push_cast; ring) (by omega), map_zero,
        map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄]
    unfold normalizedCoeff productCoeff
    rw [LinearMap.comp_apply]
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ)) v)) (prod3_vec_congr w₁ w₂ w₃ w₄
      ?_ ?_ ?_)
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
    · push_cast; ring
    · rw [hs]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i ≤ N₀ by omega)]
      push_cast; ring
  · -- first insertion terms
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₁ + d) (by omega) (fun k hk => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_ιx_binom_normalized hB (by omega) hw₂ hw₃ hw₄ _ _ _ _ k (k + 1) m n (k + I)
      (by omega), Finset.sum_range_add (n := k) (m := I),
      Finset.sum_eq_zero (s := Finset.range k) (fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj), Nat.cast_zero, zero_mul]),
      zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_neg_one_sub, add_comm i k, mul_assoc]
    congr 2
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₁ + d by omega)]
      push_cast; ring
  · -- terminal terms
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hi')]
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  · -- third insertion terms
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun k hk => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_ιy_binom_normalized hB (by omega) hw₂ (mode_mem_weight_nat hu hw₃ hk') hw₄
      _ _ _ _ k m n I (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_nat]
    congr 1
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · ring
    · ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₃ + d by omega)]
      push_cast; ring

/-- **First insertion move** (`u₋₁ w₁`): a regular relation lowering the total level. -/
theorem normalizedSeries_first
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₂ : IsLowestWeight A₂ h₂)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f (mode (A₁.YM u) (-1) w₁) w₂ w₃ w₄ N₀ (N₀ + (N₁ + d) + N₂ + N₃ + N₄) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), X ^ (2 * d + i) * PowerSeries.C (X ^ (2 * d + i)) *
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + i))
        ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)
    + ∑ i ∈ Finset.range (N₄ + d), X ^ (i + 1) * PowerSeries.C (X ^ (i + 1)) *
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ w₃ (mode (A₄.YM u) i w₄) N₀
        (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (i + 1)))
    + ∑ k ∈ Finset.range (N₃ + d),
      ιxy (X * HuangODEAlgebra.binomSeries 1 k) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) k w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (k + 1)) + N₄)
    + ∑ k ∈ Finset.range (N₂ + d),
      ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄)) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_add, c2_add, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries]
  unfold normalizedCoeff productCoeff
  set s := N₀ + (N₁ + d) + N₂ + N₃ + N₄ with hs
  obtain ⟨T, hT⟩ := hY₁.truncation w₁ (Y₂ (ν - μ - m + n) w₂ (Y₃ (μ + (s : ℂ) - n) w₃ w₄))
    (C - ν - 2 * N₀ + m)
  obtain ⟨T₆, hT₆⟩ := A₆.truncation u (Y₂ (ν - μ - m + n) w₂ (Y₃ (μ + (s : ℂ) - n) w₃ w₄))
  have hT' := Int.self_le_toNat T
  have hT₆' := Int.self_le_toNat T₆
  set I := T.toNat + T₆.toNat + N₀ + N₄ + d + m + n + 1 with hI
  rw [product_first_neg_one hY₁ hY₂ hY₃ u f w₁ w₂ w₃ w₄ _ _ _ (N₂ + N₃ + d) I
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun i hi => ⟨hT i (by omega), hT₆ i (by omega)⟩)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · -- output terms
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun i hi => by
      rw [eq_zero_of_mem_weight_neg hl₀ (product_mem_weight hY₁ hY₂ hY₃ hw₁ hw₂ hw₃ hw₄ _ _ _)
        (j := (N₀ : ℤ) - d - i) (by rw [hC, hs]; push_cast; ring) (by omega), map_zero,
        map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄]
    unfold normalizedCoeff productCoeff
    rw [LinearMap.comp_apply]
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ)) v)) (prod3_vec_congr w₁ w₂ w₃ w₄
      ?_ ?_ ?_)
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
    · push_cast; ring
    · rw [hs]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i ≤ N₀ by omega)]
      push_cast; ring
  · -- terminal terms
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hi')]
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  · -- third insertion terms
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun k hk => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_ιxy_binom_normalized hB (by omega) hw₂ (mode_mem_weight_nat hu hw₃ hk') hw₄
      _ _ _ _ k m n I (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_nat]
    congr 1
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · ring
    · ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₃ + d by omega)]
      push_cast; ring
  · -- second insertion terms
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_ιx_binom_normalized hB (by omega) (mode_mem_weight_nat hu hw₂ hk') hw₃ hw₄
      _ _ _ _ k (k + 1) m n I (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_nat]
    congr 1
    unfold normalizedCoeff productCoeff
    apply prod3_congr
    · ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₂ + d by omega)]
      push_cast; ring

end VOA.Huang.FivePointSep
