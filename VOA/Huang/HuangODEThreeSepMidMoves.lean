import VOA.Huang.HuangODEThreeSepMidModes
import VOA.Huang.HuangODEThreeSepMoves

/-!
# The five moves of the middle (iterate-in-product) chart

The C₁ relations for `f(𝒴₁(w₁)_p 𝒴_B(𝒴₃(w₃)_r w₄)_q w₂)` as identities of the
total-level-normalized double series (`normalizedSeries 𝒴₁ (swap2 𝒴_B) 𝒴₃ …`), with
coefficients in `midRing = ℂ[x, y, (1-x)⁻¹, (1+y)⁻¹, (1-x(1+y))⁻¹]` (`x = z₂/z₁`,
`y = z₀/z₂`). Every term on the right has strictly smaller total external level.
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
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {YB : IntertwiningModes M₅ M₂ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

theorem mid3_congr (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    {p p' q q' r r' : ℂ} (hp : p = p') (hq : q = q') (hr : r = r') :
    f (Y₁ p w₁ (YB q (Y₃ r w₃ w₄) w₂)) = f (Y₁ p' w₁ (YB q' (Y₃ r' w₃ w₄) w₂)) := by
  rw [hp, hq, hr]

theorem mid3_vec_congr (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    {p p' q q' r r' : ℂ} (hp : p = p') (hq : q = q') (hr : r = r') :
    Y₁ p w₁ (YB q (Y₃ r w₃ w₄) w₂) = Y₁ p' w₁ (YB q' (Y₃ r' w₃ w₄) w₂) := by
  rw [hp, hq, hr]

theorem midNC_def (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (N₀ s : ℕ) (m n : ℂ) :
    normalizedCoeff Y₁ (swap2 YB) Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s m n =
      f (Y₁ (c - ν - 2 * N₀ + m) w₁ (YB (ν - μ - m + n) (Y₃ (μ + s - n) w₃ w₄) w₂)) := rfl

theorem cbz_neg_one_nat' (k : ℕ) : cbz (-1) (k : ℤ) = (-1 : ℂ) ^ k := by
  have h := cbz_neg_one_sub 0 k
  simpa using h

/-- **Terminal move** of the middle chart (`u₋₁` on the terminal vector `w₂`). -/
theorem midSeries_terminal
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hYB : IsIntertwiningOperator A₅ A₂ A₆ YB)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ (swap2 YB) Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ (mode (A₂.YM u) (-1) w₂) w₃ w₄ N₀ (N₀ + N₁ + (N₂ + d) + N₃ + N₄) =
    (if d ≤ N₀ then X ^ (2 * d) * PowerSeries.C (X ^ (2 * d)) *
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1)) w₁ w₂ w₃ w₄ (N₀ - d)
        ((N₀ - d) + N₁ + N₂ + N₃ + N₄) else 0)
    - ∑ k ∈ Finset.range (N₁ + d), (cbz (-1) k) •
      (X ^ (k + 1) * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄))
    - ∑ k ∈ Finset.range (N₄ + d), (cbz (-1) k) •
      (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
          (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))
    - ∑ l ∈ Finset.range (N₃ + d), ((-1 : ℂ) ^ l) •
      (ιy (X * HuangODEAlgebra.binomSeries (-1) l) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄)) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_sub, c2_sub, c2_sub, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, midNC_def]
  set s := N₀ + N₁ + (N₂ + d) + N₃ + N₄ with hs
  obtain ⟨T, hT⟩ := A₅.truncation u (Y₃ (μ + (s : ℂ) - n) w₃ w₄)
  have hT' := Int.self_le_toNat T
  set K := T.toNat + N₁ + N₃ + N₄ + d + n + 1 with hK
  rw [mid_terminal_mode hY₁ hYB hY₃ u f w₁ w₂ w₃ w₄ _ _ _ K
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun k hk => hT k (by omega))]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show ∀ a b c e : ℂ, a - b - (c + e) = a - b - c - e from fun a b c e => by ring]
  refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) ?_ ?_) ?_) ?_
  · -- output
    split_ifs with hd
    · rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄, midNC_def,
        LinearMap.comp_apply]
      refine congrArg (fun v => f (mode (A₀.YM u) (-1) v)) (mid3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
      · rw [Nat.cast_sub hd]; push_cast; ring
      · push_cast; ring
      · rw [hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hd]; push_cast; ring
    · rw [c2_zero]
      have hz := eq_zero_of_mem_weight_neg hl₀
        (mid_mem_weight hY₁ hYB hY₃ hw₁ hw₂ hw₃ hw₄ (C - ν - 2 * N₀ + m)
          (ν - μ - m + n) (μ + s - n))
        (j := (N₀ : ℤ) - d) (by rw [hC, hs]; push_cast; ring) (by omega)
      rw [swap2_apply] at hz
      rw [hz, map_zero, map_zero]
  · -- first insertion
    rw [sum_range_trim (J := N₁ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄, midNC_def]
    congr 1
    apply mid3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₁ + d by omega)]
      push_cast; ring
  · -- second inner slot
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃
      (mode_mem_weight_nat hu hw₄ hk'), midNC_def]
    congr 1
    apply mid3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  · -- first inner slot: a binomial line in `y`
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun l hl => by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    rw [c2_smul, c2_ιy_binomNeg_normalized hB (by omega) hw₂
      (mode_mem_weight_nat hu hw₃ hl') hw₄ _ _ _ _ l m n K (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cbz_neg_one_nat', cbz_nat, midNC_def]
    rcases lt_or_ge k l with hkl | hkl
    · rw [Nat.choose_eq_zero_of_lt hkl]; simp
    have hsign : (-1 : ℂ) ^ l * (-1) ^ (k - l) = (-1) ^ k := by
      rw [← pow_add, Nat.add_sub_cancel' hkl]
    have e : f (Y₁ (C - ν - 2 * N₀ + m) w₁ (YB (-1 + (ν - μ - m + n) - k)
        (Y₃ (k + (μ + s - n) - l) (mode (A₃.YM u) l w₃) w₄) w₂)) =
      f (Y₁ (C - ν - 2 * N₀ + m) w₁ (YB (ν - μ - m + ((n : ℂ) - 1 - k))
        (Y₃ (μ + ((N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄ : ℕ) : ℂ) - ((n : ℂ) - 1 - k))
          (mode (A₃.YM u) l w₃) w₄) w₂)) := by
      apply mid3_congr
      · rfl
      · ring
      · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show l + 1 ≤ N₃ + d by omega)]
        push_cast; ring
    rw [e]
    calc (-1 : ℂ) ^ k * ((k.choose l : ℂ) * _) =
        (-1) ^ l * (-1) ^ (k - l) * ((k.choose l : ℂ) * _) := by rw [hsign]
      _ = _ := by ring

/-- **Second inner slot move** of the middle chart (`u₋₁ w₄`). -/
theorem midSeries_four
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hYB : IsIntertwiningOperator A₅ A₂ A₆ YB)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃)
    (hB : UniformTwoBase A₂ A₃ A₄ (swap2 YB) Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ w₃ (mode (A₄.YM u) (-1) w₄) N₀ (N₀ + N₁ + N₂ + N₃ + (N₄ + d)) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), X ^ (2 * (d + i)) * PowerSeries.C (X ^ (2 * d + i)) *
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + i))
        ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)
    - ∑ k ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ k) •
      (ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄)))
    + ∑ i ∈ Finset.range (N₂ + d), X ^ 0 * PowerSeries.C (X ^ (i + 1)) *
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ (mode (A₂.YM u) i w₂) w₃ w₄ N₀
        (N₀ + N₁ + (N₂ + d - (i + 1)) + N₃ + N₄)
    - ∑ k ∈ Finset.range (N₃ + d), (cbz (-1) k) •
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ (mode (A₃.YM u) k w₃) w₄ N₀
        (N₀ + N₁ + N₂ + (N₃ + d - (k + 1)) + N₄) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_sub, c2_add, c2_sub, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, midNC_def]
  set s := N₀ + N₁ + N₂ + N₃ + (N₄ + d) with hs
  obtain ⟨T, hT⟩ := hYB.truncation (Y₃ (μ + (s : ℂ) - n) w₃ w₄) w₂ (ν - μ - m + n)
  have hT' := Int.self_le_toNat T
  set I := T.toNat + N₀ + N₂ + d + m + n + 1 with hI
  rw [mid_four_mode hY₁ hYB hY₃ u f w₁ w₂ w₃ w₄ _ _ _ (N₁ + N₃ + d) I
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun i hi => ⟨hT i (by omega), mode_eq_zero_of_le hl₂ hu hw₂ (by omega)⟩)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  refine congrArg₂ (· - ·) (congrArg₂ (· + ·) (congrArg₂ (· - ·) ?_ ?_) ?_) ?_
  · -- output
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun i hi => by
      have hz := eq_zero_of_mem_weight_neg hl₀
        (mid_mem_weight hY₁ hYB hY₃ hw₁ hw₂ hw₃ hw₄ (C - ν - 2 * N₀ + m)
          (ν - μ - m + n + i) (μ + s - n))
        (j := (N₀ : ℤ) - d - i) (by rw [hC, hs]; push_cast; ring) (by omega)
      rw [swap2_apply] at hz
      rw [hz, map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄, midNC_def,
      LinearMap.comp_apply]
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ)) v))
      (mid3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i ≤ N₀ by omega)]
      push_cast; ring
  · -- outer insertion: a binomial line in `x`
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
    rw [cbz_neg_one_sub, add_comm i k, mul_assoc, midNC_def]
    congr 2
    apply mid3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₁ + d by omega)]
      push_cast; ring
  · -- terminal
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) (mode_mem_weight_nat hu hw₂ hi') hw₃ hw₄,
      midNC_def]
    apply mid3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₂ + d by omega)]
      push_cast; ring
  · -- first inner slot
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_normalizedSeries, midNC_def]
    congr 1
    apply mid3_congr
    · ring
    · ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₃ + d by omega)]
      push_cast; ring

theorem negOnePow_neg_one_sub_nat (i : ℕ) : negOnePow (-1 - (i : ℤ)) = -(-1 : ℂ) ^ i := by
  rw [show (-1 - (i:ℤ)) = -(i:ℤ) - 1 by ring, negOnePow_pred]
  simp [negOnePow]
  split_ifs with h <;> simp [h, Nat.not_even_iff_odd.mp]

theorem negOnePow_mul_cbz_neg_one_sub (i j : ℕ) :
    negOnePow (j : ℤ) * cbz (-1 - (i : ℤ)) (j : ℤ) = ((i + j).choose j : ℂ) := by
  rw [negOnePow_natCast, cbz_neg_one_sub, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Reindexing the triangle `(a,b) ↔ (i,j) = (b, a-b)` of the two-dimensional series
`(1 - x(1+y))^{-k-1}`. -/
theorem sum_tri_reindex (k M N I J : ℕ) (hI : N < I) (hJ : M < J) (F : ℤ → ℤ → ℂ)
    (hF : ∀ x y, x < 0 ∨ y < 0 → F x y = 0) :
    (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (N + 1),
      ((a + k).choose k : ℂ) * (a.choose b : ℂ) * F ((M : ℤ) - a) ((N : ℤ) - b)) =
    ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
      ((i + j).choose j : ℂ) * ((i + j + k).choose k : ℂ) * F ((M : ℤ) - i - j) ((N : ℤ) - i) := by
  rw [← Finset.sum_product' (f := fun a b => ((a + k).choose k : ℂ) * (a.choose b : ℂ) *
      F ((M : ℤ) - a) ((N : ℤ) - b)),
    ← Finset.sum_product' (f := fun i j => ((i + j).choose j : ℂ) * ((i + j + k).choose k : ℂ) *
      F ((M : ℤ) - i - j) ((N : ℤ) - i))]
  have hle : ∀ x : ℕ × ℕ, ((x.1 + k).choose k : ℂ) * (x.1.choose x.2 : ℂ) *
      F ((M : ℤ) - x.1) ((N : ℤ) - x.2) ≠ 0 → x.2 ≤ x.1 := by
    intro x hne
    by_contra h
    apply hne
    rw [Nat.choose_eq_zero_of_lt (not_le.mp h)]
    simp
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x.2, x.1 - x.2)) ?_ ?_ ?_ ?_
  · intro x hx hne
    have hb := hle x hne
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    omega
  · intro x hx hne y hy hne' h
    have hb := hle x hne
    have hb' := hle y hne'
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  · intro y hy hne
    simp only [Finset.mem_product, Finset.mem_range] at hy
    have h1 : 0 ≤ (M : ℤ) - y.1 - y.2 := by
      by_contra h
      apply hne
      rw [hF _ _ (Or.inl (by omega)), mul_zero]
    have h2 : 0 ≤ (N : ℤ) - y.1 := by
      by_contra h
      apply hne
      rw [hF _ _ (Or.inr (by omega)), mul_zero]
    refine ⟨(y.1 + y.2, y.1), ?_, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · intro h0
      apply hne
      rw [show (M : ℤ) - y.1 - y.2 = (M : ℤ) - ((y.1 + y.2 : ℕ) : ℤ) by push_cast; ring]
      rw [Nat.choose_symm_add] at h0
      rw [show y.1 + y.2 + k = y.1 + y.2 + k from rfl]
      linear_combination h0
    · ext <;> simp
  · intro x hx hne
    have hb := hle x hne
    rw [show x.2 + (x.1 - x.2) = x.1 by omega, Nat.choose_symm hb,
      show (M : ℤ) - (x.2 : ℕ) - ((x.1 - x.2 : ℕ) : ℤ) = (M : ℤ) - x.1 by
        rw [Nat.cast_sub hb]; ring]
    ring

theorem c2_monomial_mul (a b : ℕ) (R : PS2) (m n : ℕ) :
    c2 (X ^ a * PowerSeries.C ((X : PowerSeries ℂ) ^ b) * R) m n =
      if a ≤ m ∧ b ≤ n then c2 R (m - a) (n - b) else 0 := by
  unfold c2
  rw [mul_assoc, coeff_X_pow_mul']
  split_ifs with h1 h2 h2
  · rw [coeff_C_mul, coeff_X_pow_mul', if_pos h2.2]
  · rw [coeff_C_mul, coeff_X_pow_mul', if_neg (fun h => h2 ⟨h1, h⟩)]
  · exact absurd h2.1 h1
  · simp

/-- **First inner slot move** of the middle chart (`u₋₁ w₃`): two-dimensional
coefficients `(xy)^{k+1} (1 - x(1+y))^{-k-1}` appear. -/
theorem midSeries_three
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hYB : IsIntertwiningOperator A₅ A₂ A₆ YB)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ (swap2 YB) Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ (mode (A₃.YM u) (-1) w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d) + N₄) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), ∑ j ∈ Finset.range (N₀ + 1 - d - i),
      ((i + j).choose j : ℂ) • (X ^ (2 * (d + i + j)) * PowerSeries.C (X ^ (2 * d + 2 * i + j)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ) - j)) w₁ w₂ w₃ w₄ (N₀ - (d + i + j))
          ((N₀ - (d + i + j)) + N₁ + N₂ + N₃ + N₄))
    - ∑ k ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ k) •
      (X ^ (k + 1) * PowerSeries.C (X ^ (k + 1)) * (ιm (HuangODEAlgebra.geom 1 ^ (k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄)))
    + ∑ j ∈ Finset.range (N₂ + d),
      ιy (X * HuangODEAlgebra.binomSeries (-1) j) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) j w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (j + 1)) + N₃ + N₄)
    + ∑ i ∈ Finset.range (N₄ + d),
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ w₃ (mode (A₄.YM u) i w₄) N₀
        (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (i + 1))) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_add, c2_sub, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, midNC_def]
  simp only [c2_sum]
  set s := N₀ + N₁ + N₂ + (N₃ + d) + N₄ with hs
  set p := C - ν - 2 * (N₀ : ℂ) + m with hp
  set q := ν - μ - (m : ℂ) + n with hq
  set r := μ + (s : ℂ) - n with hr
  obtain ⟨T, hT⟩ := hY₃.truncation w₃ w₄ r
  have hT' := Int.self_le_toNat T
  set I := T.toNat + N₀ + N₄ + d + m + n + 1 with hI
  obtain ⟨B₆, hB₆⟩ := A₆.boundedBelow
  set J := Nat.ceil (((h₃ + N₃) + (h₄ + N₄) - r - 1 + (h₂ + N₂) - q - 1).re - B₆) +
    N₀ + N₂ + d + m + n + 1 with hJ
  have hJv : ∀ i : ℕ, i < I → ∀ j : ℤ, (J : ℤ) ≤ j → YB (q + j) (Y₃ (r + i) w₃ w₄) w₂ = 0 ∧
      mode (A₂.YM u) j w₂ = 0 := by
    intro i _ j hj
    refine ⟨?_, mode_eq_zero_of_le hl₂ hu hw₂ (by omega)⟩
    have hv := mem_weight hYB (mem_weight hY₃ hw₃ hw₄ (r + i)) hw₂ (q + j)
    by_contra hne
    have hbot := hB₆ _ (fun hb => hne (by rw [hb] at hv; exact (Submodule.mem_bot ℂ).mp hv))
    have hc : ((Nat.ceil (((h₃ + N₃) + (h₄ + N₄) - r - 1 + (h₂ + N₂) - q - 1).re - B₆) : ℕ) :
      ℝ) ≥ (((h₃ + N₃) + (h₄ + N₄) - r - 1 + (h₂ + N₂) - q - 1).re - B₆) := Nat.le_ceil _
    have hj' : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hJr : (J : ℝ) = (Nat.ceil (((h₃ + N₃) + (h₄ + N₄) - r - 1 + (h₂ + N₂) - q - 1).re -
      B₆) : ℝ) + N₀ + N₂ + d + m + n + 1 := by rw [hJ]; push_cast; ring
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.intCast_re,
      Complex.one_re] at hbot hc hJr
    have : (0 : ℝ) ≤ N₀ + N₂ + d + m + n := by positivity
    linarith
  rw [mid_three_mode hY₁ hYB hY₃ u f w₁ w₂ w₃ w₄ p q r (N₁ + d) I J
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun i hi => ⟨hT i (by omega), mode_eq_zero_of_le hl₄ hu hw₄ (by omega)⟩) hJv]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- the four groups
  have hout : (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, negOnePow (j : ℤ) *
      cbz (-1 - (i : ℤ)) (j : ℤ) * f (mode (A₀.YM u) (-1 - (i : ℤ) - j)
        (Y₁ p w₁ (YB (q + j) (Y₃ (r + i) w₃ w₄) w₂)))) =
      ∑ i ∈ Finset.range (N₀ + 1 - d), ∑ j ∈ Finset.range (N₀ + 1 - d - i),
        c2 (((i + j).choose j : ℂ) • (X ^ (2 * (d + i + j)) *
          PowerSeries.C (X ^ (2 * d + 2 * i + j)) *
          normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ) - j))
            w₁ w₂ w₃ w₄ (N₀ - (d + i + j)) ((N₀ - (d + i + j)) + N₁ + N₂ + N₃ + N₄))) m n := by
    have hvan : ∀ i j : ℕ, N₀ + 1 - d ≤ i + j → f (mode (A₀.YM u) (-1 - (i : ℤ) - j)
        (Y₁ p w₁ (YB (q + j) (Y₃ (r + i) w₃ w₄) w₂))) = 0 := by
      intro i j hij
      have hz := eq_zero_of_mem_weight_neg hl₀
        (mid_mem_weight hY₁ hYB hY₃ hw₁ hw₂ hw₃ hw₄ p (q + j) (r + i))
        (j := (N₀ : ℤ) - d - i - j) (by rw [hp, hq, hr, hC, hs]; push_cast; ring) (by omega)
      rw [swap2_apply] at hz
      rw [hz, map_zero, map_zero]
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun i hi => Finset.sum_eq_zero
      fun j _ => by rw [hvan i j (by omega), mul_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [sum_range_trim (J := N₀ + 1 - d - i) (by omega) (fun j hj => by
      rw [hvan i j (by omega), mul_zero])]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [negOnePow_mul_cbz_neg_one_sub, c2_smul,
      c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄, midNC_def, LinearMap.comp_apply]
    congr 1
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ) - j) v))
      (mid3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
    · rw [hp, Nat.cast_sub (by omega)]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i + j ≤ N₀ by omega)]
      push_cast; ring
  have hthree : (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, negOnePow (j : ℤ) *
      cbz (-1 - (i : ℤ)) (j : ℤ) * (negOnePow (-1 - (i : ℤ)) *
        f (Y₁ p w₁ (YB ((-1 - i : ℤ) + q - j) (Y₃ (r + i) w₃ w₄) (mode (A₂.YM u) j w₂))))) =
      -∑ j ∈ Finset.range (N₂ + d), c2 (ιy (X * HuangODEAlgebra.binomSeries (-1) j) *
        normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ (mode (A₂.YM u) j w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (j + 1)) + N₃ + N₄)) m n := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun j hj => Finset.sum_eq_zero fun i _ => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [c2_ιy_binomNeg_normalized hB (by omega) (mode_mem_weight_nat hu hw₂ hj') hw₃ hw₄
      _ _ _ _ j m n (j + I) (by omega), Finset.sum_range_add (n := j) (m := I),
      Finset.sum_eq_zero (s := Finset.range j) (fun t ht => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp ht), Nat.cast_zero, zero_mul,
          zero_mul]), zero_add, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [negOnePow_mul_cbz_neg_one_sub, negOnePow_neg_one_sub_nat, midNC_def,
      show j + i - j = i by omega, add_comm i j]
    have e : f (Y₁ p w₁ (YB ((-1 - i : ℤ) + q - j) (Y₃ (r + i) w₃ w₄) (mode (A₂.YM u) j w₂))) =
        f (Y₁ (C - ν - 2 * N₀ + m) w₁ (YB (ν - μ - m + ((n : ℂ) - 1 - ((j + i : ℕ) : ℂ)))
          (Y₃ (μ + ((N₀ + N₁ + (N₂ + d - (j + 1)) + N₃ + N₄ : ℕ) : ℂ) -
            ((n : ℂ) - 1 - ((j + i : ℕ) : ℂ))) w₃ w₄) (mode (A₂.YM u) j w₂))) := by
      apply mid3_congr
      · rw [hp]
      · rw [hq]; push_cast; ring
      · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show j + 1 ≤ N₂ + d by omega)]
        push_cast; ring
    rw [e]
    rw [Nat.choose_symm_add]
    ring
  have hone : (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, negOnePow (j : ℤ) *
      cbz (-1 - (i : ℤ)) (j : ℤ) * ∑ k ∈ Finset.range (N₁ + d), cbz (-1 - (i : ℤ) - j) k *
        f (Y₁ ((-1 - i - j : ℤ) + p - k) (mode (A₁.YM u) k w₁)
          (YB (q + j) (Y₃ (r + i) w₃ w₄) w₂))) =
      ∑ k ∈ Finset.range (N₁ + d), c2 (((-1 : ℂ) ^ k) • (X ^ (k + 1) *
        PowerSeries.C (X ^ (k + 1)) * (ιm (HuangODEAlgebra.geom 1 ^ (k + 1)) *
          normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
            (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄)))) m n := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hwk := mode_mem_weight_nat hu hw₁ hk'
    rw [c2_smul, c2_monomial_mul]
    -- the vanishing array
    set G : ℤ → ℤ → ℂ := fun x y => normalizedCoeff Y₁ (swap2 YB) Y₃ C ν μ f
      (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀ (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄)
        (x : ℂ) (y : ℂ) with hG
    have hGz : ∀ x y : ℤ, x < 0 ∨ y < 0 → G x y = 0 := fun x y hxy =>
      normalizedCoeff_neg' hB (by omega) hw₂ hw₃ hw₄ C f _ N₀ x y hxy rfl rfl
    have hterm : ∀ i j : ℕ, negOnePow (j : ℤ) * cbz (-1 - (i : ℤ)) (j : ℤ) *
        (cbz (-1 - (i : ℤ) - j) k * f (Y₁ ((-1 - i - j : ℤ) + p - k) (mode (A₁.YM u) k w₁)
          (YB (q + j) (Y₃ (r + i) w₃ w₄) w₂))) =
        (-1 : ℂ) ^ k * (((i + j).choose j : ℂ) * ((i + j + k).choose k : ℂ) *
          G ((m : ℤ) - 1 - k - i - j) ((n : ℤ) - 1 - k - i)) := by
      intro i j
      have hcbz : cbz (-1 - (i : ℤ) - j) (k : ℤ) = (-1 : ℂ) ^ k * ((i + j + k).choose k : ℂ) := by
        rw [show (-1 - (i : ℤ) - j) = -1 - ((i + j : ℕ) : ℤ) by push_cast; ring, cbz_neg_one_sub]
      rw [negOnePow_mul_cbz_neg_one_sub, hcbz]
      have e : f (Y₁ ((-1 - i - j : ℤ) + p - k) (mode (A₁.YM u) k w₁)
          (YB (q + j) (Y₃ (r + i) w₃ w₄) w₂)) =
          G ((m : ℤ) - 1 - k - i - j) ((n : ℤ) - 1 - k - i) := by
        rw [hG]; simp only; rw [midNC_def]
        apply mid3_congr
        · rw [hp]; push_cast; ring
        · rw [hq]; push_cast; ring
        · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₁ + d by omega)]
          push_cast; ring
      rw [e]; ring
    simp only [hterm, ← Finset.mul_sum]
    congr 1
    split_ifs with hmn
    · obtain ⟨hm1, hn1⟩ := hmn
      have key := sum_tri_reindex k (m - (k + 1)) (n - (k + 1)) I J (by omega) (by omega) G hGz
      have hM : ((m - (k + 1) : ℕ) : ℤ) = (m : ℤ) - 1 - k := by omega
      have hN : ((n - (k + 1) : ℕ) : ℤ) = (n : ℤ) - 1 - k := by omega
      simp only [hM, hN] at key
      rw [c2_ιm_geom_normalized]
      rw [show (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
          ((i + j).choose j : ℂ) * ((i + j + k).choose k : ℂ) *
            G ((m : ℤ) - 1 - k - i - j) ((n : ℤ) - 1 - k - i)) =
          ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
          ((i + j).choose j : ℂ) * ((i + j + k).choose k : ℂ) *
            G ((m : ℤ) - 1 - k - i - j) ((n : ℤ) - 1 - k - i) from rfl, ← key]
      have e1 : ((m - (k + 1) : ℕ) : ℂ) = (m : ℂ) - 1 - k := by
        rw [Nat.cast_sub hm1]; push_cast; ring
      have e2 : ((n - (k + 1) : ℕ) : ℂ) = (n : ℂ) - 1 - k := by
        rw [Nat.cast_sub hn1]; push_cast; ring
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      rw [hG]
      simp only [e1, e2]
      congr 1; push_cast; ring
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [hGz _ _ (by omega), mul_zero]
  have hfour : (∑ i ∈ Finset.range I, f (Y₁ p w₁ (YB q (Y₃ (r - 1 - i) w₃
      (mode (A₄.YM u) i w₄)) w₂))) = ∑ i ∈ Finset.range (N₄ + d),
        c2 (normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ w₂ w₃ (mode (A₄.YM u) i w₄) N₀
          (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (i + 1)))) m n := by
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_normalizedSeries, midNC_def]
    apply mid3_congr
    · rw [hp]
    · rw [hq]
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  rw [hout, hthree, hone, hfour]
  simp only [c2_smul]
  ring

/-- Reindexing `(a,b) ↔ (a+l, b+l)` for the outer move. -/
theorem sum_sq_reindex (l M N I K : ℕ) (hI : M + l < I) (hK : N + l < K) (F : ℤ → ℤ → ℂ)
    (hF : ∀ x y, x < 0 ∨ y < 0 → F x y = 0) :
    (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (N + 1),
      ((a + l).choose l : ℂ) * (a.choose b : ℂ) * F ((M : ℤ) - a) ((N : ℤ) - b)) =
    ∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K,
      (i.choose k : ℂ) * (k.choose l : ℂ) * F ((M : ℤ) + l - i) ((N : ℤ) + l - k) := by
  set L : ℕ → ℕ → ℂ := fun a b => ((a + l).choose l : ℂ) * (a.choose b : ℂ) *
    F ((M : ℤ) - a) ((N : ℤ) - b) with hL
  set R : ℕ → ℕ → ℂ := fun i k => (i.choose k : ℂ) * (k.choose l : ℂ) *
    F ((M : ℤ) + l - i) ((N : ℤ) + l - k) with hR
  have hval : ∀ a b : ℕ, L a b = R (a + l) (b + l) := by
    intro a b
    simp only [hL, hR]
    rw [show (M : ℤ) + l - ((a + l : ℕ) : ℤ) = (M : ℤ) - a by push_cast; ring,
      show (N : ℤ) + l - ((b + l : ℕ) : ℤ) = (N : ℤ) - b by push_cast; ring]
    have e2 := Nat.choose_mul (n := a + l) (k := b + l) (s := l) (by omega)
    rw [show a + l - l = a by omega, show b + l - l = b by omega] at e2
    have e3 : (((a + l).choose (b + l) : ℕ) : ℂ) * (((b + l).choose l : ℕ) : ℂ) =
        (((a + l).choose l : ℕ) : ℂ) * ((a.choose b : ℕ) : ℂ) := by
      exact_mod_cast e2
    rw [← e3]
  change ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (N + 1), L a b =
    ∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, R i k
  rw [← Finset.sum_product' (f := L), ← Finset.sum_product' (f := R)]
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x.1 + l, x.2 + l)) ?_ ?_ ?_ ?_
  · intro x hx _
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    omega
  · intro x _ _ y _ _ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  · intro y hy hne
    simp only [Finset.mem_product, Finset.mem_range] at hy
    have hkl : l ≤ y.2 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [Nat.choose_eq_zero_of_lt (n := y.2) (not_le.mp h)]
      simp
    have hik : y.2 ≤ y.1 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [Nat.choose_eq_zero_of_lt (n := y.1) (not_le.mp h)]
      simp
    have h1 : 0 ≤ (M : ℤ) + l - y.1 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [hF _ _ (Or.inl (by omega)), mul_zero]
    have h2 : 0 ≤ (N : ℤ) + l - y.2 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [hF _ _ (Or.inr (by omega)), mul_zero]
    have hy' : y = (y.1 - l + l, y.2 - l + l) := by ext <;> simp <;> omega
    refine ⟨(y.1 - l, y.2 - l), ?_, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · simp only
      rw [hval, show y.1 - l + l = y.1 by omega, show y.2 - l + l = y.2 by omega]
      exact hne
    · simp only
      exact hy'.symm
  · intro x _ _
    exact hval x.1 x.2

/-- **Outer slot move** of the middle chart (`u₋₁ w₁`). -/
theorem midSeries_one
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hYB : IsIntertwiningOperator A₅ A₂ A₆ YB)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₂ : IsLowestWeight A₂ h₂)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ (swap2 YB) Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f (mode (A₁.YM u) (-1) w₁) w₂ w₃ w₄ N₀ (N₀ + (N₁ + d) + N₂ + N₃ + N₄) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), X ^ (2 * d + i) * PowerSeries.C (X ^ (2 * d + i)) *
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + i))
        ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)
    + ∑ i ∈ Finset.range (N₂ + d), X ^ (i + 1) * PowerSeries.C (X ^ (i + 1)) *
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ (mode (A₂.YM u) i w₂) w₃ w₄ N₀
        (N₀ + N₁ + (N₂ + d - (i + 1)) + N₃ + N₄)
    + ∑ k ∈ Finset.range (N₄ + d),
      ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
          (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))
    + ∑ l ∈ Finset.range (N₃ + d),
      X ^ (l + 1) * PowerSeries.C (X ^ (l + 1)) * (ιm (HuangODEAlgebra.geom 1 ^ (l + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄)) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_add, c2_add, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, midNC_def]
  set s := N₀ + (N₁ + d) + N₂ + N₃ + N₄ with hs
  set p := C - ν - 2 * (N₀ : ℂ) + m with hp
  set q := ν - μ - (m : ℂ) + n with hq
  set r := μ + (s : ℂ) - n with hr
  obtain ⟨T₅, hT₅⟩ := A₅.truncation u (Y₃ r w₃ w₄)
  obtain ⟨T₁, hT₁⟩ := hY₁.truncation w₁ (YB q (Y₃ r w₃ w₄) w₂) p
  obtain ⟨T₆, hT₆⟩ := A₆.truncation u (YB q (Y₃ r w₃ w₄) w₂)
  have h5 := Int.self_le_toNat T₅
  have h1 := Int.self_le_toNat T₁
  have h6 := Int.self_le_toNat T₆
  set K := T₅.toNat + N₃ + N₄ + d + n + 1 with hK
  set I := T₁.toNat + T₆.toNat + N₀ + N₂ + N₃ + N₄ + d + m + n + 1 with hI
  rw [mid_one_mode hY₁ hYB hY₃ u f w₁ w₂ w₃ w₄ p q r K I
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun k hk => hT₅ k (by omega))
    (fun i hi => ⟨hT₁ i (by omega), hT₆ i (by omega)⟩)]
  simp only [mul_add, Finset.sum_add_distrib]
  have hout : (∑ i ∈ Finset.range I, f (mode (A₀.YM u) (-1 - (i : ℤ))
      (Y₁ (p + i) w₁ (YB q (Y₃ r w₃ w₄) w₂)))) =
      ∑ i ∈ Finset.range (N₀ + 1 - d), c2 (X ^ (2 * d + i) * PowerSeries.C (X ^ (2 * d + i)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ)))
          w₁ w₂ w₃ w₄ (N₀ - (d + i)) ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)) m n := by
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun i hi => by
      have hz := eq_zero_of_mem_weight_neg hl₀
        (mid_mem_weight hY₁ hYB hY₃ hw₁ hw₂ hw₃ hw₄ (p + i) q r)
        (j := (N₀ : ℤ) - d - i) (by rw [hp, hq, hr, hC, hs]; push_cast; ring) (by omega)
      rw [swap2_apply] at hz
      rw [hz, map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄, midNC_def, LinearMap.comp_apply]
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ)) v))
      (mid3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
    · rw [hp, Nat.cast_sub (by omega)]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i ≤ N₀ by omega)]
      push_cast; ring
  have hterm2 : (∑ i ∈ Finset.range I, f (Y₁ (p - 1 - i) w₁ (YB q (Y₃ r w₃ w₄)
      (mode (A₂.YM u) i w₂)))) = ∑ i ∈ Finset.range (N₂ + d),
        c2 (X ^ (i + 1) * PowerSeries.C (X ^ (i + 1)) *
          normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ (mode (A₂.YM u) i w₂) w₃ w₄ N₀
            (N₀ + N₁ + (N₂ + d - (i + 1)) + N₃ + N₄)) m n := by
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_monomial_normalizedSeries hB (by omega) (mode_mem_weight_nat hu hw₂ hi') hw₃ hw₄,
      midNC_def]
    apply mid3_congr
    · rw [hp]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₂ + d by omega)]
      push_cast; ring
  have hterm4 : (∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, cbz (i : ℤ) (k : ℤ) *
      f (Y₁ (p - 1 - i) w₁ (YB ((i : ℤ) + q - k) (Y₃ r w₃ (mode (A₄.YM u) k w₄)) w₂))) =
      ∑ k ∈ Finset.range (N₄ + d), c2 (ιx (X * HuangODEAlgebra.binomSeries 1 k) *
        (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
          normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
            (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))) m n := by
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun k hk => Finset.sum_eq_zero fun i _ => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_ιx_binom_normalized hB (by omega) hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hk')
      _ _ _ _ k (k + 1) m n I (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_nat, midNC_def]
    congr 1
    apply mid3_congr
    · rw [hp]; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  have hterm3 : (∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, cbz (i : ℤ) (k : ℤ) *
      ∑ l ∈ Finset.range K, cbz (k : ℤ) (l : ℤ) * f (Y₁ (p - 1 - i) w₁ (YB ((i : ℤ) + q - k)
        (Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄) w₂))) =
      ∑ l ∈ Finset.range (N₃ + d), c2 (X ^ (l + 1) * PowerSeries.C (X ^ (l + 1)) *
        (ιm (HuangODEAlgebra.geom 1 ^ (l + 1)) *
          normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
            (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄))) m n := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun l hl => Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun k _ => by
        rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    rw [c2_monomial_mul]
    set G : ℤ → ℤ → ℂ := fun x y => normalizedCoeff Y₁ (swap2 YB) Y₃ C ν μ f w₁ w₂
      (mode (A₃.YM u) l w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄)
        (x : ℂ) (y : ℂ) with hG
    have hGz : ∀ x y : ℤ, x < 0 ∨ y < 0 → G x y = 0 := fun x y hxy =>
      normalizedCoeff_neg' hB (by omega) hw₂ (mode_mem_weight_nat hu hw₃ hl') hw₄ C f _ N₀ x y
        hxy rfl rfl
    have hterm : ∀ i k : ℕ, cbz (i : ℤ) (k : ℤ) * (cbz (k : ℤ) (l : ℤ) *
        f (Y₁ (p - 1 - i) w₁ (YB ((i : ℤ) + q - k) (Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄)
          w₂))) = (i.choose k : ℂ) * (k.choose l : ℂ) *
            G ((m : ℤ) - 1 - i) ((n : ℤ) - 1 - k) := by
      intro i k
      rw [cbz_nat, cbz_nat]
      have e : f (Y₁ (p - 1 - i) w₁ (YB ((i : ℤ) + q - k) (Y₃ (k + r - l) (mode (A₃.YM u) l w₃)
          w₄) w₂)) = G ((m : ℤ) - 1 - i) ((n : ℤ) - 1 - k) := by
        rw [hG]; simp only; rw [midNC_def]
        apply mid3_congr
        · rw [hp]; push_cast; ring
        · rw [hq]; push_cast; ring
        · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show l + 1 ≤ N₃ + d by omega)]
          push_cast; ring
      rw [e]; ring
    simp only [hterm]
    split_ifs with hmn
    · obtain ⟨hm1, hn1⟩ := hmn
      have key := sum_sq_reindex l (m - (l + 1)) (n - (l + 1)) I K (by omega) (by omega) G hGz
      have hM : ((m - (l + 1) : ℕ) : ℤ) + l = (m : ℤ) - 1 := by omega
      have hN : ((n - (l + 1) : ℕ) : ℤ) + l = (n : ℤ) - 1 := by omega
      simp only [hM, hN] at key
      rw [c2_ιm_geom_normalized, ← key]
      have e1 : ((m - (l + 1) : ℕ) : ℂ) = (m : ℂ) - 1 - l := by
        rw [Nat.cast_sub hm1]; push_cast; ring
      have e2 : ((n - (l + 1) : ℕ) : ℂ) = (n : ℂ) - 1 - l := by
        rw [Nat.cast_sub hn1]; push_cast; ring
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      rw [hG]
      simp only
      congr 1; push_cast [Nat.cast_sub hm1, Nat.cast_sub hn1]; ring
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases hik : k ≤ i
      · by_cases hkl : l ≤ k
        · rw [hGz _ _ (by omega), mul_zero]
        · rw [Nat.choose_eq_zero_of_lt (not_le.mp hkl)]; simp
      · rw [Nat.choose_eq_zero_of_lt (not_le.mp hik)]; simp
  rw [hout, hterm2, hterm4, hterm3]
  ring

/-- **Dual move** of the middle chart (`f = g ∘ u₍₂ wt u - 1 + j₎`). -/
theorem midSeries_dual
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hYB : IsIntertwiningOperator A₅ A₂ A₆ YB)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₁ : IsLowestWeight A₁ h₁) (hl₂ : IsLowestWeight A₂ h₂)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ (swap2 YB) Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} (hd : 1 ≤ d) {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) (j : ℕ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      (f ∘ₗ mode (A₀.YM u) (2 * (d : ℤ) - 1 + j)) w₁ w₂ w₃ w₄
      (N₀ + d + j) (N₀ + d + j + N₁ + N₂ + N₃ + N₄) =
    (if d + j ≤ N₂ then X ^ (2 * (d + j)) * PowerSeries.C (X ^ (2 * (d + j))) *
      normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ (mode (A₂.YM u) (2 * (d : ℤ) - 1 + j) w₂) w₃ w₄ N₀
        (N₀ + N₁ + (N₂ - (d + j)) + N₃ + N₄) else 0)
    + ∑ k ∈ Finset.range (N₄ + d), (cbz (2 * (d : ℤ) - 1 + j) k) •
      (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
          (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))
    + ∑ k ∈ Finset.range (2 * d + j), ∑ l ∈ Finset.range (N₃ + d),
      (cbz (2 * (d : ℤ) - 1 + j) k * cbz (k : ℤ) (l : ℤ)) •
      (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄))
    + ∑ k ∈ Finset.range (N₁ + d), (cbz (2 * (d : ℤ) - 1 + j) k) •
      (X ^ (j + k + 1) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄)) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_add, c2_add, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, midNC_def,
    LinearMap.comp_apply]
  simp only [c2_sum]
  set s := N₀ + d + j + N₁ + N₂ + N₃ + N₄ with hs
  set p := C - ν - 2 * ((N₀ + d + j : ℕ) : ℂ) + m with hp
  set q := ν - μ - (m : ℂ) + n with hq
  set r := μ + (s : ℂ) - n with hr
  set M' : ℤ := 2 * (d : ℤ) - 1 + j with hM'
  obtain ⟨T₅, hT₅⟩ := A₅.truncation u (Y₃ r w₃ w₄)
  have h5 := Int.self_le_toNat T₅
  set K := T₅.toNat + N₁ + N₃ + N₄ + 2 * d + j + 1 with hK
  rw [mid_dual_mode hY₁ hYB hY₃ u f w₁ w₂ w₃ w₄ p q r M' K
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun k hk => hT₅ k (by omega))]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hM'n : M' = ((2 * d - 1 + j : ℕ) : ℤ) := by
    rw [hM']; push_cast [Nat.cast_sub (show 1 ≤ 2 * d by omega)]; ring
  have hcbzK : ∀ k : ℕ, 2 * d + j ≤ k → cbz M' (k : ℤ) = 0 := by
    intro k hk
    rw [hM'n, cbz_nat, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  have he : f (Y₁ p w₁ (YB q (Y₃ r w₃ w₄) (mode (A₂.YM u) M' w₂))) =
      c2 (if d + j ≤ N₂ then X ^ (2 * (d + j)) * PowerSeries.C (X ^ (2 * (d + j))) *
        normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ (mode (A₂.YM u) M' w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ - (d + j)) + N₃ + N₄) else 0) m n := by
    split_ifs with h2
    · have hw₂' : mode (A₂.YM u) M' w₂ ∈ A₂.weight (h₂ + ((N₂ - (d + j) : ℕ) : ℂ)) := by
        convert mode_mem_weight A₂ hu hw₂ M' using 1
        congr 1
        rw [hM', Nat.cast_sub h2]; push_cast; ring
      rw [c2_monomial_normalizedSeries hB (by omega) hw₂' hw₃ hw₄, midNC_def]
      apply mid3_congr
      · rw [hp]; push_cast; ring
      · rw [hq]; push_cast; ring
      · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h2]; push_cast; ring
    · rw [c2_zero, mode_eq_zero_of_le hl₂ hu hw₂ (by rw [hM']; omega)]
      simp
  have hc : (∑ k ∈ Finset.range K, cbz M' (k : ℤ) * f (Y₁ p w₁ (YB (M' + q - k)
      (Y₃ r w₃ (mode (A₄.YM u) k w₄)) w₂))) = ∑ k ∈ Finset.range (N₄ + d),
        c2 (cbz M' (k : ℤ) • (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (j + k + 1)) *
          normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
            (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))) m n := by
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃
      (mode_mem_weight_nat hu hw₄ hk'), midNC_def]
    congr 1
    apply mid3_congr
    · rw [hp]; push_cast; ring
    · rw [hq, hM']; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  have hb : (∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K, cbz M' (k : ℤ) *
      (cbz (k : ℤ) (l : ℤ) * f (Y₁ p w₁ (YB (M' + q - k) (Y₃ (k + r - l)
        (mode (A₃.YM u) l w₃) w₄) w₂)))) = ∑ k ∈ Finset.range (2 * d + j),
        ∑ l ∈ Finset.range (N₃ + d), c2 ((cbz M' (k : ℤ) * cbz (k : ℤ) (l : ℤ)) •
          (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (j + k + 1)) *
            normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
              (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄))) m n := by
    rw [sum_range_trim (J := 2 * d + j) (by omega) (fun k hk => Finset.sum_eq_zero fun l _ => by
      rw [hcbzK k hk, zero_mul])]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun l hl => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    rw [c2_smul, c2_monomial_normalizedSeries hB (by omega) hw₂
      (mode_mem_weight_nat hu hw₃ hl') hw₄, midNC_def, mul_assoc]
    congr 2
    apply mid3_congr
    · rw [hp]; push_cast; ring
    · rw [hq, hM']; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show l + 1 ≤ N₃ + d by omega)]
      push_cast; ring
  have ha : (∑ k ∈ Finset.range K, cbz M' (k : ℤ) * f (Y₁ (M' + p - k) (mode (A₁.YM u) k w₁)
      (YB q (Y₃ r w₃ w₄) w₂))) = ∑ k ∈ Finset.range (N₁ + d),
        c2 (cbz M' (k : ℤ) • (X ^ (j + k + 1) * PowerSeries.C (X ^ (j + k + 1)) *
          normalizedSeries Y₁ (swap2 YB) Y₃ C ν μ f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
            (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄))) m n := by
    rw [sum_range_trim (J := N₁ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄, midNC_def]
    congr 1
    apply mid3_congr
    · rw [hp, hM']; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₁ + d by omega)]
      push_cast; ring
  rw [he, hc, hb, ha]
  ring

end VOA.Huang.FivePointSep
