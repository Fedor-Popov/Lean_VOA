import VOA.Huang.HuangODEThreeSepPairModes
import VOA.Huang.HuangODEThreeSepPairRing

/-!
# The five moves of the pair (blow-up) chart

The C₁ relations for `f(𝒴_P(p) (𝒴_{XY}(r) x y) (𝒴_{ZT}(q) z t))` as identities of the
normalized double series `normalizedSeries pairY₁ (pairY₂ 𝒴_P 𝒴_{ZT}) 𝒴_{XY} …` (product slots
`(w₁, w₂, w₃, w₄) = (t, z, x, y)`), with coefficients in
`pairRing = ℂ[x, y, (1-x)⁻¹, (1+xy)⁻¹, (1-x(1-y))⁻¹]`. Every term on the right has strictly
smaller total external level. The vanishing of the normalized coefficients at negative indices
comes from `PairBase` (all four levels).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop PowerSeries VOA.Huang.HuangODEThree
open VOA.Huang.HuangODEProduct VOA.Huang.HuangODEModes
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {AU : OrdVModule W MU} {AV : OrdVModule W MV}
variable {P : IntertwiningModes MU MV M₀} {ZT : IntertwiningModes M₂ M₁ MV}
  {XY : IntertwiningModes M₃ M₄ MU}

theorem pair3_congr (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    {p p' q q' r r' : ℂ} (hp : p = p') (hq : q = q') (hr : r = r') :
    f (P p (XY r w₃ w₄) (ZT q w₂ w₁)) = f (P p' (XY r' w₃ w₄) (ZT q' w₂ w₁)) := by
  rw [hp, hq, hr]

theorem pair3_vec_congr (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    {p p' q q' r r' : ℂ} (hp : p = p') (hq : q = q') (hr : r = r') :
    P p (XY r w₃ w₄) (ZT q w₂ w₁) = P p' (XY r' w₃ w₄) (ZT q' w₂ w₁) := by
  rw [hp, hq, hr]

section Coeff
variable {h₁ h₂ h₃ h₄ ν μ : ℂ} (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
  {N₁ N₂ N₃ N₄ s : ℕ} (hs : N₁ + N₂ + N₃ + N₄ ≤ s) {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
  (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
  (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
include hB hs hw₁ hw₂ hw₃ hw₄

theorem c2_pair_monomial (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (N₀ a b m n : ℕ) :
    c2 (X ^ a * PowerSeries.C ((X : PowerSeries ℂ) ^ b) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    f (P (c - ν - 2 * N₀ + ((m : ℂ) - a)) (XY (μ + s - ((n : ℂ) - b)) w₃ w₄)
      (ZT (ν - μ - ((m : ℂ) - a) + ((n : ℂ) - b)) w₂ w₁)) :=
  c2_monomial_van (F := normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f
    w₁ w₂ w₃ w₄ N₀ s) (fun m n => c2_normalizedSeries _ _ _ _ _ _ _ _ _ _ m n)
    (pairNC_neg hB hs hw₁ hw₂ hw₃ hw₄ c f N₀) a b m n

theorem c2_pair_ιx (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (N₀ k b m n I : ℕ) (hI : m ≤ I) :
    c2 (ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ b) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s)) m n =
    ∑ i ∈ Finset.range I, (i.choose k : ℂ) *
      f (P (c - ν - 2 * N₀ + ((m : ℂ) - 1 - i)) (XY (μ + s - ((n : ℂ) - b)) w₃ w₄)
        (ZT (ν - μ - ((m : ℂ) - 1 - i) + ((n : ℂ) - b)) w₂ w₁)) :=
  c2_ιx_binom_van (F := normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f
    w₁ w₂ w₃ w₄ N₀ s) (fun m n => c2_normalizedSeries _ _ _ _ _ _ _ _ _ _ m n)
    (pairNC_neg hB hs hw₁ hw₂ hw₃ hw₄ c f N₀) k b m n I hI

theorem c2_pair_ιxy (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (N₀ k m n I : ℕ) (hI : m ≤ I) :
    c2 (ιxy (X * HuangODEAlgebra.binomSeries (-1) k) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    ∑ i ∈ Finset.range I, (i.choose k : ℂ) * (-1) ^ (i - k) *
      f (P (c - ν - 2 * N₀ + ((m : ℂ) - 1 - i)) (XY (μ + s - ((n : ℂ) - 1 - i)) w₃ w₄)
        (ZT (ν - μ - ((m : ℂ) - 1 - i) + ((n : ℂ) - 1 - i)) w₂ w₁)) :=
  c2_ιxy_binomNeg_van (F := normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f
    w₁ w₂ w₃ w₄ N₀ s) (fun m n => c2_normalizedSeries _ _ _ _ _ _ _ _ _ _ m n)
    (pairNC_neg hB hs hw₁ hw₂ hw₃ hw₄ c f N₀) k m n I hI

end Coeff

/-- **Terminal move** of the pair chart (`u₋₁ t`). -/
theorem pairSeries_terminal
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₂ : IsLowestWeight A₂ h₂)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f (mode (A₁.YM u) (-1) w₁) w₂ w₃ w₄ N₀ (N₀ + (N₁ + d) + N₂ + N₃ + N₄) =
    (if d ≤ N₀ then X ^ (2 * d) * PowerSeries.C (X ^ (2 * d)) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1)) w₁ w₂ w₃ w₄ (N₀ - d)
        ((N₀ - d) + N₁ + N₂ + N₃ + N₄) else 0)
    - ∑ k ∈ Finset.range (N₄ + d), (cbz (-1) k) •
      (X ^ (k + 1) * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
          (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))
    - ∑ l ∈ Finset.range (N₃ + d), ((-1 : ℂ) ^ l) •
      (ιxy (X * HuangODEAlgebra.binomSeries (-1) l) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄))
    - ∑ k ∈ Finset.range (N₂ + d), (cbz (-1) k) •
      (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄)) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_sub, c2_sub, c2_sub, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, pairNC_def]
  set s := N₀ + (N₁ + d) + N₂ + N₃ + N₄ with hs
  obtain ⟨T, hT⟩ := AU.truncation u (XY (μ + (s : ℂ) - n) w₃ w₄)
  have hT' := Int.self_le_toNat T
  set K := T.toNat + N₂ + N₃ + N₄ + d + m + n + 1 with hK
  rw [pair_terminal_mode hP hZT hXY u f w₁ w₂ w₃ w₄ _ _ _ K
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun k hk => hT k (by omega))]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show ∀ a b c e : ℂ, a - (b + c) - e = a - b - c - e from fun a b c e => by ring]
  refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) ?_ ?_) ?_) ?_
  · -- output
    split_ifs with hd
    · rw [c2_pair_monomial hB (by omega) hw₁ hw₂ hw₃ hw₄, LinearMap.comp_apply]
      refine congrArg (fun v => f (mode (A₀.YM u) (-1) v))
        (pair3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
      · rw [Nat.cast_sub hd]; push_cast; ring
      · push_cast; ring
      · rw [hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hd]; push_cast; ring
    · rw [c2_zero]
      have hz := eq_zero_of_mem_weight_neg hl₀
        (pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄ (C - ν - 2 * N₀ + m)
          (ν - μ - m + n) (μ + s - n))
        (j := (N₀ : ℤ) - d) (by rw [hC, hs]; push_cast; ring) (by omega)
      rw [hz, map_zero, map_zero]
  · -- fourth slot `y`
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_pair_monomial hB (by omega) hw₁ hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hk')]
    congr 1
    apply pair3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  · -- third slot `x`: a binomial line in `xy`
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun l hl => by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    rw [c2_smul, c2_pair_ιxy hB (by omega) hw₁ hw₂ (mode_mem_weight_nat hu hw₃ hl') hw₄
      _ _ _ l m n K (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cbz_neg_one_nat', cbz_nat]
    rcases lt_or_ge k l with hkl | hkl
    · rw [Nat.choose_eq_zero_of_lt hkl]; simp
    have hsign : (-1 : ℂ) ^ l * (-1) ^ (k - l) = (-1) ^ k := by
      rw [← pow_add, Nat.add_sub_cancel' hkl]
    have e : f (P (-1 + (C - ν - 2 * N₀ + m) - k)
        (XY (k + (μ + s - n) - l) (mode (A₃.YM u) l w₃) w₄) (ZT (ν - μ - m + n) w₂ w₁)) =
      f (P (C - ν - 2 * N₀ + ((m : ℂ) - 1 - k))
        (XY (μ + ((N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄ : ℕ) : ℂ) - ((n : ℂ) - 1 - k))
          (mode (A₃.YM u) l w₃) w₄)
          (ZT (ν - μ - ((m : ℂ) - 1 - k) + ((n : ℂ) - 1 - k)) w₂ w₁)) := by
      apply pair3_congr
      · ring
      · ring
      · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show l + 1 ≤ N₃ + d by omega)]
        push_cast; ring
    rw [e]
    calc (-1 : ℂ) ^ k * ((k.choose l : ℂ) * _) =
        (-1) ^ l * (-1) ^ (k - l) * ((k.choose l : ℂ) * _) := by rw [hsign]
      _ = _ := by ring
  · -- second slot `z`
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_pair_monomial hB (by omega) hw₁ (mode_mem_weight_nat hu hw₂ hk') hw₃ hw₄]
    congr 1
    apply pair3_congr
    · push_cast; ring
    · push_cast; ring
    · rw [hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₂ + d by omega)]
      push_cast; ring

theorem negOnePow_mul_cbz_neg_one (j : ℕ) : negOnePow (j : ℤ) * cbz (-1) (j : ℤ) = 1 := by
  have h := negOnePow_mul_cbz_neg_one_sub 0 j
  simpa using h

theorem negOnePow_neg_one' : negOnePow (-1 : ℤ) = -1 := by
  simp

/-- **Fourth slot move** of the pair chart (`u₋₁ y`). -/
theorem pairSeries_four
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃)
    (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ w₃ (mode (A₄.YM u) (-1) w₄) N₀ (N₀ + N₁ + N₂ + N₃ + (N₄ + d)) =
    ∑ j ∈ Finset.range (N₀ + 1 - d), X ^ (2 * d + j) * PowerSeries.C (X ^ (2 * d + j)) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1 - (j : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + j))
        ((N₀ - (d + j)) + N₁ + N₂ + N₃ + N₄)
    + ∑ j ∈ Finset.range (N₁ + d), X ^ (j + 1) * PowerSeries.C (X ^ (j + 1)) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f (mode (A₁.YM u) j w₁) w₂ w₃ w₄ N₀
        (N₀ + (N₁ + d - (j + 1)) + N₂ + N₃ + N₄)
    + ∑ k ∈ Finset.range (N₂ + d),
      ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
    - ∑ k ∈ Finset.range (N₃ + d), (cbz (-1) k) •
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ (mode (A₃.YM u) k w₃) w₄ N₀
        (N₀ + N₁ + N₂ + (N₃ + d - (k + 1)) + N₄) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_sub, c2_add, c2_add, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, pairNC_def]
  set s := N₀ + N₁ + N₂ + N₃ + (N₄ + d) with hs
  set p := C - ν - 2 * (N₀ : ℂ) + m with hp
  set q := ν - μ - (m : ℂ) + n with hq
  set r := μ + (s : ℂ) - n with hr
  obtain ⟨T, hT⟩ := AV.truncation u (ZT q w₂ w₁)
  have hT' := Int.self_le_toNat T
  set J := T.toNat + N₀ + N₁ + N₂ + d + m + n + 1 with hJ
  set K := N₂ + N₃ + d with hK
  have hJv : ∀ j : ℤ, (J : ℤ) ≤ j → P (p + j) (XY r w₃ w₄) (ZT q w₂ w₁) = 0 ∧
      mode (AV.YM u) j (ZT q w₂ w₁) = 0 := by
    intro j hj
    refine ⟨?_, hT j (by omega)⟩
    exact eq_zero_of_mem_weight_neg hl₀
      (pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄ (p + j) q r)
      (j := (N₀ : ℤ) - d - j) (by rw [hp, hq, hr, hC, hs]; push_cast; ring) (by omega)
  rw [pair_y_mode hP hZT hXY u f w₁ w₂ w₃ w₄ p q r K J
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega)) hJv]
  have e1 : ∀ (a b c : ℕ → ℂ), (∑ j ∈ Finset.range J, (negOnePow (j : ℤ) * cbz (-1) (j : ℤ)) *
      (a j - negOnePow (-1) * (b j + c j))) =
      ∑ j ∈ Finset.range J, a j + ∑ j ∈ Finset.range J, b j + ∑ j ∈ Finset.range J, c j := by
    intro a b c
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [negOnePow_mul_cbz_neg_one, negOnePow_neg_one']
    ring
  rw [e1]
  have hout : (∑ j ∈ Finset.range J, f (mode (A₀.YM u) (-1 - (j : ℤ))
      (P (p + j) (XY r w₃ w₄) (ZT q w₂ w₁)))) =
      ∑ j ∈ Finset.range (N₀ + 1 - d), c2 (X ^ (2 * d + j) * PowerSeries.C (X ^ (2 * d + j)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ
          (f ∘ₗ mode (A₀.YM u) (-1 - (j : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + j))
          ((N₀ - (d + j)) + N₁ + N₂ + N₃ + N₄)) m n := by
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun j hj => by
      have hz := eq_zero_of_mem_weight_neg hl₀
        (pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄ (p + j) q r)
        (j := (N₀ : ℤ) - d - j) (by rw [hp, hq, hr, hC, hs]; push_cast; ring) (by omega)
      rw [hz, map_zero, map_zero])]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [c2_pair_monomial hB (by omega) hw₁ hw₂ hw₃ hw₄, LinearMap.comp_apply]
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (j : ℤ)) v))
      (pair3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
    · rw [hp, Nat.cast_sub (by omega)]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + j ≤ N₀ by omega)]
      push_cast; ring
  have hone : (∑ j ∈ Finset.range J, f (P (-1 + p - j) (XY r w₃ w₄)
      (ZT q w₂ (mode (A₁.YM u) j w₁)))) =
      ∑ j ∈ Finset.range (N₁ + d), c2 (X ^ (j + 1) * PowerSeries.C (X ^ (j + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f (mode (A₁.YM u) j w₁)
          w₂ w₃ w₄ N₀ (N₀ + (N₁ + d - (j + 1)) + N₂ + N₃ + N₄)) m n := by
    rw [sum_range_trim (J := N₁ + d) (by omega) (fun j hj => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [c2_pair_monomial hB (by omega) (mode_mem_weight_nat hu hw₁ hj') hw₂ hw₃ hw₄]
    apply pair3_congr
    · rw [hp]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show j + 1 ≤ N₁ + d by omega)]
      push_cast; ring
  have htwo : (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K, cbz (j : ℤ) (k : ℤ) *
      f (P (-1 + p - j) (XY r w₃ w₄) (ZT ((j : ℂ) + q - k) (mode (A₂.YM u) k w₂) w₁))) =
      ∑ k ∈ Finset.range (N₂ + d), c2 (ιx (X * HuangODEAlgebra.binomSeries 1 k) *
        (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
          normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁
            (mode (A₂.YM u) k w₂) w₃ w₄ N₀ (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))) m n := by
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => Finset.sum_eq_zero fun j _ => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_pair_ιx hB (by omega) hw₁ (mode_mem_weight_nat hu hw₂ hk') hw₃ hw₄
      _ _ _ k (k + 1) m n J (by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cbz_nat]
    congr 1
    apply pair3_congr
    · rw [hp]; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₂ + d by omega)]
      push_cast; ring
  have hthree : (∑ k ∈ Finset.range K, cbz (-1) (k : ℤ) *
      f (P p (XY (-1 + r - k) (mode (A₃.YM u) k w₃) w₄) (ZT q w₂ w₁))) =
      ∑ k ∈ Finset.range (N₃ + d), c2 (cbz (-1) (k : ℤ) •
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁ w₂
          (mode (A₃.YM u) k w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d - (k + 1)) + N₄)) m n := by
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [c2_smul, c2_normalizedSeries, pairNC_def]
    congr 1
    apply pair3_congr
    · rw [hp]
    · rw [hq]
    · rw [hr, hs]; simp only [Nat.cast_add,
        Nat.cast_sub (show k + 1 ≤ N₃ + d by have := Finset.mem_range.mp hk; omega)]
      push_cast; ring
  rw [hout, hone, htwo, hthree]

theorem c2_pair_ιm' (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (N₀ s k m n : ℕ) :
    c2 (ιm' (HuangODEAlgebra.geom 1 ^ (k + 1)) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      ((i + k).choose k : ℂ) * ((i.choose j : ℂ) * (-1) ^ j) *
        normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s
          ((m : ℂ) - i) ((n : ℂ) - j) :=
  c2_ιm'_geom_van (F := normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f
    w₁ w₂ w₃ w₄ N₀ s) (fun m n => c2_normalizedSeries _ _ _ _ _ _ _ _ _ _ m n) k m n

/-- Reindexing `(a,b) ↔ (i,k) = (a-b, b+l)` for the second-slot move of the pair chart. -/
theorem sum_pairZ_reindex (l M N I K : ℕ) (hI : M < I) (hK : N + l < K) (F : ℤ → ℤ → ℂ)
    (hF : ∀ x y, x < 0 ∨ y < 0 → F x y = 0) :
    (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (N + 1),
      ((a + l).choose l : ℂ) * ((a.choose b : ℂ) * (-1) ^ b) * F ((M : ℤ) - a) ((N : ℤ) - b)) =
    ∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K,
      (-1 : ℂ) ^ (k + l) * ((i + k).choose k : ℂ) * (k.choose l : ℂ) *
        F ((M : ℤ) + l - i - k) ((N : ℤ) + l - k) := by
  set L : ℕ → ℕ → ℂ := fun a b => ((a + l).choose l : ℂ) * ((a.choose b : ℂ) * (-1) ^ b) *
    F ((M : ℤ) - a) ((N : ℤ) - b) with hL
  set R : ℕ → ℕ → ℂ := fun i k => (-1 : ℂ) ^ (k + l) * ((i + k).choose k : ℂ) *
    (k.choose l : ℂ) * F ((M : ℤ) + l - i - k) ((N : ℤ) + l - k) with hR
  have hval : ∀ a b : ℕ, b ≤ a → L a b = R (a - b) (b + l) := by
    intro a b hba
    simp only [hL, hR]
    rw [show (M : ℤ) + l - ((a - b : ℕ) : ℤ) - ((b + l : ℕ) : ℤ) = (M : ℤ) - a by
        push_cast [Nat.cast_sub hba]; ring,
      show (N : ℤ) + l - ((b + l : ℕ) : ℤ) = (N : ℤ) - b by push_cast; ring,
      show a - b + (b + l) = a + l by omega]
    have e2 := Nat.choose_mul (n := a + l) (k := b + l) (s := l) (by omega)
    rw [show a + l - l = a by omega, show b + l - l = b by omega] at e2
    have e3 : (((a + l).choose (b + l) : ℕ) : ℂ) * (((b + l).choose l : ℕ) : ℂ) =
        (((a + l).choose l : ℕ) : ℂ) * ((a.choose b : ℕ) : ℂ) := by
      exact_mod_cast e2
    have hsign : (-1 : ℂ) ^ (b + l + l) = (-1) ^ b := by
      rw [show b + l + l = b + 2 * l by ring, pow_add, pow_mul]; norm_num
    rw [hsign]
    linear_combination (-((-1 : ℂ) ^ b * F ((M : ℤ) - a) ((N : ℤ) - b))) * e3
  have hle : ∀ x : ℕ × ℕ, L x.1 x.2 ≠ 0 → x.2 ≤ x.1 := by
    intro x hne
    by_contra h
    apply hne
    simp only [hL]
    rw [Nat.choose_eq_zero_of_lt (not_le.mp h)]
    simp
  change ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (N + 1), L a b =
    ∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, R i k
  rw [← Finset.sum_product' (f := L), ← Finset.sum_product' (f := R)]
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x.1 - x.2, x.2 + l)) ?_ ?_ ?_ ?_
  · intro x hx hne
    have hb := hle x hne
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    omega
  · intro x _ hne y _ hne' h
    have hb := hle x hne
    have hb' := hle y hne'
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
    have h1 : 0 ≤ (M : ℤ) + l - y.1 - y.2 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [hF _ _ (Or.inl (by omega)), mul_zero]
    have h2 : 0 ≤ (N : ℤ) + l - y.2 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [hF _ _ (Or.inr (by omega)), mul_zero]
    have hy' : (y.1 + y.2 - l - (y.2 - l), y.2 - l + l) = y := by
      ext <;> simp <;> omega
    refine ⟨(y.1 + y.2 - l, y.2 - l), ?_, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · simp only
      rw [hval _ _ (by omega), show y.1 + y.2 - l - (y.2 - l) = y.1 by omega,
        show y.2 - l + l = y.2 by omega]
      exact hne
    · simp only
      exact hy'
  · intro x _ hne
    exact hval x.1 x.2 (hle x hne)

/-- **Second slot move** of the pair chart (`u₋₁ z`). -/
theorem pairSeries_two
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ (mode (A₂.YM u) (-1) w₂) w₃ w₄ N₀ (N₀ + N₁ + (N₂ + d) + N₃ + N₄) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), X ^ (2 * (d + i)) * PowerSeries.C (X ^ (2 * d + i)) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + i))
        ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)
    + ∑ i ∈ Finset.range (N₁ + d), X ^ 0 * PowerSeries.C (X ^ (i + 1)) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f (mode (A₁.YM u) i w₁) w₂ w₃ w₄ N₀
        (N₀ + (N₁ + d - (i + 1)) + N₂ + N₃ + N₄)
    - ∑ k ∈ Finset.range (N₄ + d), ((-1 : ℂ) ^ k) •
      (ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
          (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1)))))
    - ∑ l ∈ Finset.range (N₃ + d), ((-1 : ℂ) ^ l) •
      (X ^ (l + 1) * PowerSeries.C (X ^ (l + 1)) * (ιm' (HuangODEAlgebra.geom 1 ^ (l + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄))) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_sub, c2_sub, c2_add, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, pairNC_def]
  set s := N₀ + N₁ + (N₂ + d) + N₃ + N₄ with hs
  set p := C - ν - 2 * (N₀ : ℂ) + m with hp
  set q := ν - μ - (m : ℂ) + n with hq
  set r := μ + (s : ℂ) - n with hr
  obtain ⟨TU, hTU⟩ := AU.truncation u (XY r w₃ w₄)
  obtain ⟨TV, hTV⟩ := hZT.truncation w₂ w₁ q
  have hU' := Int.self_le_toNat TU
  have hV' := Int.self_le_toNat TV
  set K := TU.toNat + N₃ + N₄ + d + m + n + 1 with hK
  set I := TV.toNat + N₀ + N₁ + d + m + n + 1 with hI
  rw [pair_z_mode hP hZT hXY u f w₁ w₂ w₃ w₄ p q r K I
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun k hk => hTU k (by omega))
    (fun i hi => ⟨hTV i (by omega), mode_eq_zero_of_le hl₁ hu hw₁ (by omega)⟩)]
  have e1 : ∀ (a t : ℕ → ℂ) (w b c : ℕ → ℕ → ℂ),
      (∑ i ∈ Finset.range I, (a i - ∑ k ∈ Finset.range K, w i k * (b i k + c i k) + t i)) =
      ∑ i ∈ Finset.range I, a i - ∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, w i k * b i k
        - ∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, w i k * c i k
        + ∑ i ∈ Finset.range I, t i := by
    intro a t w b c
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [e1]
  have hout : (∑ i ∈ Finset.range I, f (mode (A₀.YM u) (-1 - (i : ℤ))
      (P p (XY r w₃ w₄) (ZT (q + i) w₂ w₁)))) =
      ∑ i ∈ Finset.range (N₀ + 1 - d), c2 (X ^ (2 * (d + i)) * PowerSeries.C (X ^ (2 * d + i)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ
          (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃ w₄ (N₀ - (d + i))
          ((N₀ - (d + i)) + N₁ + N₂ + N₃ + N₄)) m n := by
    rw [sum_range_trim (J := N₀ + 1 - d) (by omega) (fun i hi => by
      have hz := eq_zero_of_mem_weight_neg hl₀
        (pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄ p (q + i) r)
        (j := (N₀ : ℤ) - d - i) (by rw [hp, hq, hr, hC, hs]; push_cast; ring) (by omega)
      rw [hz, map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_pair_monomial hB (by omega) hw₁ hw₂ hw₃ hw₄, LinearMap.comp_apply]
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ)) v))
      (pair3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
    · rw [hp, Nat.cast_sub (by omega)]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i ≤ N₀ by omega)]
      push_cast; ring
  have hone : (∑ i ∈ Finset.range I, f (P p (XY r w₃ w₄)
      (ZT (q - 1 - i) w₂ (mode (A₁.YM u) i w₁)))) =
      ∑ i ∈ Finset.range (N₁ + d), c2 (X ^ 0 * PowerSeries.C (X ^ (i + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f (mode (A₁.YM u) i w₁)
          w₂ w₃ w₄ N₀ (N₀ + (N₁ + d - (i + 1)) + N₂ + N₃ + N₄)) m n := by
    rw [sum_range_trim (J := N₁ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_pair_monomial hB (by omega) (mode_mem_weight_nat hu hw₁ hi') hw₂ hw₃ hw₄]
    apply pair3_congr
    · rw [hp]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₁ + d by omega)]
      push_cast; ring
  have hfour : (∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, cbz (-1 - (i : ℤ)) (k : ℤ) *
      f (P ((-1 - i : ℤ) + p - k) (XY r w₃ (mode (A₄.YM u) k w₄)) (ZT (q + i) w₂ w₁))) =
      ∑ k ∈ Finset.range (N₄ + d), c2 (((-1 : ℂ) ^ k) •
        (ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
          normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁ w₂ w₃
            (mode (A₄.YM u) k w₄) N₀ (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1)))))) m n := by
    rw [Finset.sum_comm]
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun k hk => Finset.sum_eq_zero fun i _ => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_pair_ιx hB (by omega) hw₁ hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hk')
      _ _ _ k (k + 1) m n (k + I) (by omega), Finset.sum_range_add (n := k) (m := I),
      Finset.sum_eq_zero (s := Finset.range k) (fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj), Nat.cast_zero, zero_mul]),
      zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_neg_one_sub, add_comm i k, mul_assoc]
    congr 2
    apply pair3_congr
    · rw [hp]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  have hthree : (∑ i ∈ Finset.range I, ∑ k ∈ Finset.range K, cbz (-1 - (i : ℤ)) (k : ℤ) *
      ∑ l ∈ Finset.range K, cbz (k : ℤ) (l : ℤ) * f (P ((-1 - i : ℤ) + p - k)
        (XY (k + r - l) (mode (A₃.YM u) l w₃) w₄) (ZT (q + i) w₂ w₁))) =
      ∑ l ∈ Finset.range (N₃ + d), c2 (((-1 : ℂ) ^ l) • (X ^ (l + 1) *
        PowerSeries.C (X ^ (l + 1)) * (ιm' (HuangODEAlgebra.geom 1 ^ (l + 1)) *
          normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁ w₂
            (mode (A₃.YM u) l w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄)))) m n := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun l hl => Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun k _ => by
        rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    have hwl := mode_mem_weight_nat hu hw₃ hl'
    rw [c2_smul, c2_monomial_mul]
    set G : ℤ → ℤ → ℂ := fun x y => normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ
      f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄)
        (x : ℂ) (y : ℂ) with hG
    have hGz : ∀ x y : ℤ, x < 0 ∨ y < 0 → G x y = 0 := fun x y hxy =>
      pairNC_neg hB (by omega) hw₁ hw₂ hwl hw₄ C f N₀ x y hxy
    have hterm : ∀ i k : ℕ, cbz (-1 - (i : ℤ)) (k : ℤ) * (cbz (k : ℤ) (l : ℤ) *
        f (P ((-1 - i : ℤ) + p - k) (XY (k + r - l) (mode (A₃.YM u) l w₃) w₄)
          (ZT (q + i) w₂ w₁))) =
        (-1 : ℂ) ^ l * ((-1 : ℂ) ^ (k + l) * ((i + k).choose k : ℂ) * (k.choose l : ℂ) *
          G ((m : ℤ) - 1 - i - k) ((n : ℤ) - 1 - k)) := by
      intro i k
      rw [cbz_neg_one_sub, cbz_nat]
      have e : f (P ((-1 - i : ℤ) + p - k) (XY (k + r - l) (mode (A₃.YM u) l w₃) w₄)
          (ZT (q + i) w₂ w₁)) = G ((m : ℤ) - 1 - i - k) ((n : ℤ) - 1 - k) := by
        rw [hG]; simp only; rw [pairNC_def]
        apply pair3_congr
        · rw [hp]; push_cast; ring
        · rw [hq]; push_cast; ring
        · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show l + 1 ≤ N₃ + d by omega)]
          push_cast; ring
      have hsg : (-1 : ℂ) ^ k = (-1) ^ l * (-1) ^ (k + l) := by
        rw [← pow_add, show l + (k + l) = k + 2 * l by ring, pow_add, pow_mul]; norm_num
      rw [e, hsg]; ring
    simp only [hterm, ← Finset.mul_sum]
    congr 1
    split_ifs with hmn
    · obtain ⟨hm1, hn1⟩ := hmn
      have key := sum_pairZ_reindex l (m - (l + 1)) (n - (l + 1)) I K (by omega) (by omega)
        G hGz
      have hM : ((m - (l + 1) : ℕ) : ℤ) + l = (m : ℤ) - 1 := by omega
      have hN : ((n - (l + 1) : ℕ) : ℤ) + l = (n : ℤ) - 1 := by omega
      simp only [hM, hN] at key
      rw [c2_pair_ιm', ← key]
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      rw [hG]
      push_cast
      rfl
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases hkl : l ≤ k
      · rw [hGz _ _ (by omega), mul_zero]
      · rw [Nat.choose_eq_zero_of_lt (not_le.mp hkl)]; simp
  rw [hout, hone, hfour, hthree]
  ring

/-- Reindexing `(a,b) ↔ (i,j) = (b, a-b+k)` for the third-slot move of the pair chart. -/
theorem sum_pairX_reindex (k M N I J : ℕ) (M' N' : ℤ) (hM : M' = M + k) (hN : N' = N)
    (hI : N < I) (hJ : M + k < J) (F : ℤ → ℤ → ℂ)
    (hF : ∀ x y, x < 0 ∨ y < 0 → F x y = 0) :
    (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (N + 1),
      ((a + k).choose k : ℂ) * ((a.choose b : ℂ) * (-1) ^ b) * F ((M : ℤ) - a) ((N : ℤ) - b)) =
    ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
      (-1 : ℂ) ^ i * ((i + j).choose j : ℂ) * (j.choose k : ℂ) * F (M' - i - j) (N' - i) := by
  subst hM hN
  set L : ℕ → ℕ → ℂ := fun a b => ((a + k).choose k : ℂ) * ((a.choose b : ℂ) * (-1) ^ b) *
    F ((M : ℤ) - a) ((N : ℤ) - b) with hL
  set R : ℕ → ℕ → ℂ := fun i j => (-1 : ℂ) ^ i * ((i + j).choose j : ℂ) *
    (j.choose k : ℂ) * F ((M : ℤ) + k - i - j) ((N : ℤ) - i) with hR
  have hval : ∀ a b : ℕ, b ≤ a → L a b = R b (a - b + k) := by
    intro a b hba
    simp only [hL, hR]
    rw [show (M : ℤ) + k - (b : ℤ) - ((a - b + k : ℕ) : ℤ) = (M : ℤ) - a by
        push_cast [Nat.cast_sub hba]; ring,
      show b + (a - b + k) = a + k by omega]
    have e2 := Nat.choose_mul (n := a + k) (k := a - b + k) (s := k) (by omega)
    rw [show a + k - k = a by omega, show a - b + k - k = a - b by omega,
      Nat.choose_symm hba] at e2
    have e3 : (((a + k).choose (a - b + k) : ℕ) : ℂ) * (((a - b + k).choose k : ℕ) : ℂ) =
        (((a + k).choose k : ℕ) : ℂ) * ((a.choose b : ℕ) : ℂ) := by
      exact_mod_cast e2
    linear_combination (-((-1 : ℂ) ^ b * F ((M : ℤ) - a) ((N : ℤ) - b))) * e3
  have hle : ∀ x : ℕ × ℕ, L x.1 x.2 ≠ 0 → x.2 ≤ x.1 := by
    intro x hne
    by_contra h
    apply hne
    simp only [hL]
    rw [Nat.choose_eq_zero_of_lt (not_le.mp h)]
    simp
  change ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (N + 1), L a b =
    ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, R i j
  rw [← Finset.sum_product' (f := L), ← Finset.sum_product' (f := R)]
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x.2, x.1 - x.2 + k)) ?_ ?_ ?_ ?_
  · intro x hx hne
    have hb := hle x hne
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    omega
  · intro x _ hne y _ hne' h
    have hb := hle x hne
    have hb' := hle y hne'
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  · intro y hy hne
    simp only [Finset.mem_product, Finset.mem_range] at hy
    have hkj : k ≤ y.2 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [Nat.choose_eq_zero_of_lt (n := y.2) (not_le.mp h)]
      simp
    have h1 : 0 ≤ (M : ℤ) + k - y.1 - y.2 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [hF _ _ (Or.inl (by omega)), mul_zero]
    have h2 : 0 ≤ (N : ℤ) - y.1 := by
      by_contra h
      apply hne
      simp only [hR]
      rw [hF _ _ (Or.inr (by omega)), mul_zero]
    refine ⟨(y.1 + y.2 - k, y.1), ?_, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · simp only
      rw [hval _ _ (by omega), show y.1 + y.2 - k - y.1 + k = y.2 by omega]
      exact hne
    · simp only
      ext
      · simp
      · simp; omega
  · intro x _ hne
    exact hval x.1 x.2 (hle x hne)

/-- **Third slot move** of the pair chart (`u₋₁ x`): the two-dimensional coefficients
`(xy)^{1+j}(1+xy)^{-1-j}` and `x^{k+1}y^{k+1}(1 - x(1-y))^{-k-1}` appear. -/
theorem pairSeries_three
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ (mode (A₃.YM u) (-1) w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d) + N₄) =
    ∑ i ∈ Finset.range (N₀ + 1 - d), ∑ j ∈ Finset.range (N₀ + 1 - d - i),
      ((i + j).choose j : ℂ) • (X ^ (2 * d + 2 * i + j) *
        PowerSeries.C (X ^ (2 * d + 2 * i + j)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ) - j)) w₁ w₂ w₃ w₄ (N₀ - (d + i + j))
          ((N₀ - (d + i + j)) + N₁ + N₂ + N₃ + N₄))
    + ∑ j ∈ Finset.range (N₁ + d),
      ιxy (X * HuangODEAlgebra.binomSeries (-1) j) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) j w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (j + 1)) + N₂ + N₃ + N₄)
    + ∑ k ∈ Finset.range (N₂ + d),
      X ^ (k + 1) * PowerSeries.C (X ^ (k + 1)) * (ιm' (HuangODEAlgebra.geom 1 ^ (k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
    + ∑ i ∈ Finset.range (N₄ + d),
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ w₃ (mode (A₄.YM u) i w₄) N₀
        (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (i + 1))) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_add, c2_add, c2_sum, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, pairNC_def]
  simp only [c2_sum]
  set s := N₀ + N₁ + N₂ + (N₃ + d) + N₄ with hs
  set p := C - ν - 2 * (N₀ : ℂ) + m with hp
  set q := ν - μ - (m : ℂ) + n with hq
  set r := μ + (s : ℂ) - n with hr
  obtain ⟨TX, hTX⟩ := hXY.truncation w₃ w₄ r
  obtain ⟨TV, hTV⟩ := AV.truncation u (ZT q w₂ w₁)
  have hX' := Int.self_le_toNat TX
  have hV' := Int.self_le_toNat TV
  set I := TX.toNat + N₀ + N₄ + d + m + n + 1 with hI
  set J := TV.toNat + N₀ + N₁ + d + m + n + 1 with hJ
  set K := N₂ + d with hK
  have hJv : ∀ i : ℕ, i < I → ∀ j : ℤ, (J : ℤ) ≤ j →
      P (p + j) (XY (r + i) w₃ w₄) (ZT q w₂ w₁) = 0 ∧ mode (AV.YM u) j (ZT q w₂ w₁) = 0 := by
    intro i _ j hj
    refine ⟨?_, hTV j (by omega)⟩
    exact eq_zero_of_mem_weight_neg hl₀
      (pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄ (p + j) q (r + i))
      (j := (N₀ : ℤ) - d - i - j) (by rw [hp, hq, hr, hC, hs]; push_cast; ring) (by omega)
  rw [pair_x_mode hP hZT hXY u f w₁ w₂ w₃ w₄ p q r K I J
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun i hi => ⟨hTX i (by omega), mode_eq_zero_of_le hl₄ hu hw₄ (by omega)⟩) hJv]
  have e1 : ∀ (y : ℕ → ℂ) (v : ℕ → ℂ) (w a b c : ℕ → ℕ → ℂ),
      (∑ i ∈ Finset.range I, (∑ j ∈ Finset.range J, w i j * (a i j - v i * (b i j + c i j))
        + y i)) =
      ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, w i j * a i j
        - ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, w i j * (v i * b i j)
        - ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, w i j * (v i * c i j)
        + ∑ i ∈ Finset.range I, y i := by
    intro y v w a b c
    simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [e1]
  have hout : (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, negOnePow (j : ℤ) *
      cbz (-1 - (i : ℤ)) (j : ℤ) * f (mode (A₀.YM u) (-1 - (i : ℤ) - j)
        (P (p + j) (XY (r + i) w₃ w₄) (ZT q w₂ w₁)))) =
      ∑ i ∈ Finset.range (N₀ + 1 - d), ∑ j ∈ Finset.range (N₀ + 1 - d - i),
        c2 (((i + j).choose j : ℂ) • (X ^ (2 * d + 2 * i + j) *
          PowerSeries.C (X ^ (2 * d + 2 * i + j)) *
          normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ
            (f ∘ₗ mode (A₀.YM u) (-1 - (i : ℤ) - j)) w₁ w₂ w₃ w₄ (N₀ - (d + i + j))
            ((N₀ - (d + i + j)) + N₁ + N₂ + N₃ + N₄))) m n := by
    have hvan : ∀ i j : ℕ, N₀ + 1 - d ≤ i + j → f (mode (A₀.YM u) (-1 - (i : ℤ) - j)
        (P (p + j) (XY (r + i) w₃ w₄) (ZT q w₂ w₁))) = 0 := by
      intro i j hij
      have hz := eq_zero_of_mem_weight_neg hl₀
        (pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄ (p + j) q (r + i))
        (j := (N₀ : ℤ) - d - i - j) (by rw [hp, hq, hr, hC, hs]; push_cast; ring) (by omega)
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
      c2_pair_monomial hB (by omega) hw₁ hw₂ hw₃ hw₄, LinearMap.comp_apply]
    congr 1
    refine congrArg (fun v => f (mode (A₀.YM u) (-1 - (i : ℤ) - j) v))
      (pair3_vec_congr w₁ w₂ w₃ w₄ ?_ ?_ ?_)
    · rw [hp, Nat.cast_sub (by omega)]; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show d + i + j ≤ N₀ by omega)]
      push_cast; ring
  have hone : (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, negOnePow (j : ℤ) *
      cbz (-1 - (i : ℤ)) (j : ℤ) * (negOnePow (-1 - (i : ℤ)) *
        f (P ((-1 - i : ℤ) + p - j) (XY (r + i) w₃ w₄) (ZT q w₂ (mode (A₁.YM u) j w₁))))) =
      -∑ j ∈ Finset.range (N₁ + d), c2 (ιxy (X * HuangODEAlgebra.binomSeries (-1) j) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f (mode (A₁.YM u) j w₁)
          w₂ w₃ w₄ N₀ (N₀ + (N₁ + d - (j + 1)) + N₂ + N₃ + N₄)) m n := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    rw [sum_range_trim (J := N₁ + d) (by omega) (fun j hj => Finset.sum_eq_zero fun i _ => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [c2_pair_ιxy hB (by omega) (mode_mem_weight_nat hu hw₁ hj') hw₂ hw₃ hw₄
      _ _ _ j m n (j + I) (by omega), Finset.sum_range_add (n := j) (m := I),
      Finset.sum_eq_zero (s := Finset.range j) (fun t ht => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp ht), Nat.cast_zero, zero_mul,
          zero_mul]), zero_add, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [negOnePow_mul_cbz_neg_one_sub, negOnePow_neg_one_sub_nat,
      show j + i - j = i by omega]
    have e : f (P ((-1 - i : ℤ) + p - j) (XY (r + i) w₃ w₄) (ZT q w₂ (mode (A₁.YM u) j w₁))) =
        f (P (C - ν - 2 * N₀ + ((m : ℂ) - 1 - ((j + i : ℕ) : ℂ)))
          (XY (μ + ((N₀ + (N₁ + d - (j + 1)) + N₂ + N₃ + N₄ : ℕ) : ℂ) -
            ((n : ℂ) - 1 - ((j + i : ℕ) : ℂ))) w₃ w₄)
          (ZT (ν - μ - ((m : ℂ) - 1 - ((j + i : ℕ) : ℂ)) + ((n : ℂ) - 1 - ((j + i : ℕ) : ℂ)))
            w₂ (mode (A₁.YM u) j w₁))) := by
      apply pair3_congr
      · rw [hp]; push_cast; ring
      · rw [hq]; push_cast; ring
      · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show j + 1 ≤ N₁ + d by omega)]
        push_cast; ring
    rw [e, add_comm i j]
    ring
  have htwo : (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, negOnePow (j : ℤ) *
      cbz (-1 - (i : ℤ)) (j : ℤ) * (negOnePow (-1 - (i : ℤ)) *
        ∑ k ∈ Finset.range K, cbz (j : ℤ) (k : ℤ) * f (P ((-1 - i : ℤ) + p - j)
          (XY (r + i) w₃ w₄) (ZT ((j : ℂ) + q - k) (mode (A₂.YM u) k w₂) w₁)))) =
      -∑ k ∈ Finset.range (N₂ + d), c2 (X ^ (k + 1) * PowerSeries.C (X ^ (k + 1)) *
        (ιm' (HuangODEAlgebra.geom 1 ^ (k + 1)) *
          normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁
            (mode (A₂.YM u) k w₂) w₃ w₄ N₀ (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))) m n := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hwk := mode_mem_weight_nat hu hw₂ hk'
    rw [c2_monomial_mul]
    set G : ℤ → ℤ → ℂ := fun x y => normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ
      f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀ (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄)
        (x : ℂ) (y : ℂ) with hG
    have hGz : ∀ x y : ℤ, x < 0 ∨ y < 0 → G x y = 0 := fun x y hxy =>
      pairNC_neg hB (by omega) hw₁ hwk hw₃ hw₄ C f N₀ x y hxy
    have hterm : ∀ i j : ℕ, negOnePow (j : ℤ) * cbz (-1 - (i : ℤ)) (j : ℤ) *
        (negOnePow (-1 - (i : ℤ)) * (cbz (j : ℤ) (k : ℤ) * f (P ((-1 - i : ℤ) + p - j)
          (XY (r + i) w₃ w₄) (ZT ((j : ℂ) + q - k) (mode (A₂.YM u) k w₂) w₁)))) =
        -((-1 : ℂ) ^ i * ((i + j).choose j : ℂ) * (j.choose k : ℂ) *
          G ((m : ℤ) - 1 - i - j) ((n : ℤ) - 1 - k - i)) := by
      intro i j
      rw [negOnePow_mul_cbz_neg_one_sub, negOnePow_neg_one_sub_nat, cbz_nat]
      have e : f (P ((-1 - i : ℤ) + p - j) (XY (r + i) w₃ w₄)
          (ZT ((j : ℂ) + q - k) (mode (A₂.YM u) k w₂) w₁)) =
          G ((m : ℤ) - 1 - i - j) ((n : ℤ) - 1 - k - i) := by
        rw [hG]; simp only; rw [pairNC_def]
        apply pair3_congr
        · rw [hp]; push_cast; ring
        · rw [hq]; push_cast; ring
        · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₂ + d by omega)]
          push_cast; ring
      rw [e]; ring
    simp only [hterm, Finset.sum_neg_distrib]
    congr 1
    split_ifs with hmn
    · obtain ⟨hm1, hn1⟩ := hmn
      have key := sum_pairX_reindex k (m - (k + 1)) (n - (k + 1)) I J ((m : ℤ) - 1)
        ((n : ℤ) - 1 - k) (by omega) (by omega) (by omega) (by omega) G hGz
      rw [c2_pair_ιm', ← key]
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      rw [hG]
      push_cast
      rfl
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hkj : k ≤ j
      · rw [hGz _ _ (by omega), mul_zero]
      · rw [Nat.choose_eq_zero_of_lt (not_le.mp hkj)]; simp
  have hfour : (∑ i ∈ Finset.range I, f (P p (XY (r - 1 - i) w₃ (mode (A₄.YM u) i w₄))
      (ZT q w₂ w₁))) = ∑ i ∈ Finset.range (N₄ + d),
        c2 (normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁ w₂ w₃
          (mode (A₄.YM u) i w₄) N₀ (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (i + 1)))) m n := by
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [c2_normalizedSeries, pairNC_def]
    apply pair3_congr
    · rw [hp]
    · rw [hq]
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show i + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  rw [hout, hone, htwo, hfour]
  ring

/-- **Dual move** of the pair chart (`f = g ∘ u₍₂ wt u - 1 + j₎`). -/
theorem pairSeries_dual
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₁ : IsLowestWeight A₁ h₁) (hl₂ : IsLowestWeight A₂ h₂)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    {d : ℕ} (hd : 1 ≤ d) {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) (j : ℕ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      (f ∘ₗ mode (A₀.YM u) (2 * (d : ℤ) - 1 + j)) w₁ w₂ w₃ w₄
      (N₀ + d + j) (N₀ + d + j + N₁ + N₂ + N₃ + N₄) =
    (if d + j ≤ N₁ then X ^ (2 * (d + j)) * PowerSeries.C (X ^ (2 * (d + j))) *
      normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f (mode (A₁.YM u) (2 * (d : ℤ) - 1 + j) w₁) w₂ w₃ w₄ N₀
        (N₀ + (N₁ - (d + j)) + N₂ + N₃ + N₄) else 0)
    + ∑ k ∈ Finset.range (N₂ + d), (cbz (2 * (d : ℤ) - 1 + j) k) •
      (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
    + ∑ k ∈ Finset.range (N₄ + d), (cbz (2 * (d : ℤ) - 1 + j) k) •
      (X ^ (j + k + 1) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ (mode (A₄.YM u) k w₄) N₀
          (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))
    + ∑ k ∈ Finset.range (2 * d + j), ∑ l ∈ Finset.range (N₃ + d),
      (cbz (2 * (d : ℤ) - 1 + j) k * cbz (k : ℤ) (l : ℤ)) •
      (X ^ (j + k + 1) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) l w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄)) := by
  classical
  refine PS2.ext fun m n => ?_
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  rw [c2_add, c2_add, c2_add, c2_sum, c2_sum, c2_sum, c2_normalizedSeries, pairNC_def,
    LinearMap.comp_apply]
  simp only [c2_sum]
  set s := N₀ + d + j + N₁ + N₂ + N₃ + N₄ with hs
  set p := C - ν - 2 * ((N₀ + d + j : ℕ) : ℂ) + m with hp
  set q := ν - μ - (m : ℂ) + n with hq
  set r := μ + (s : ℂ) - n with hr
  set M' : ℤ := 2 * (d : ℤ) - 1 + j with hM'
  obtain ⟨TU, hTU⟩ := AU.truncation u (XY r w₃ w₄)
  have hU' := Int.self_le_toNat TU
  set K := TU.toNat + N₂ + N₃ + N₄ + 2 * d + j + 1 with hK
  rw [pair_dual_mode hP hZT hXY u f w₁ w₂ w₃ w₄ p q r M' K
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))
    (fun k hk => hTU k (by omega))]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hM'n : M' = ((2 * d - 1 + j : ℕ) : ℤ) := by
    rw [hM']; push_cast [Nat.cast_sub (show 1 ≤ 2 * d by omega)]; ring
  have hcbzK : ∀ k : ℕ, 2 * d + j ≤ k → cbz M' (k : ℤ) = 0 := by
    intro k hk
    rw [hM'n, cbz_nat, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  have he : f (P p (XY r w₃ w₄) (ZT q w₂ (mode (A₁.YM u) M' w₁))) =
      c2 (if d + j ≤ N₁ then X ^ (2 * (d + j)) * PowerSeries.C (X ^ (2 * (d + j))) *
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f
          (mode (A₁.YM u) M' w₁) w₂ w₃ w₄ N₀ (N₀ + (N₁ - (d + j)) + N₂ + N₃ + N₄) else 0) m n := by
    split_ifs with h1
    · have hw₁' : mode (A₁.YM u) M' w₁ ∈ A₁.weight (h₁ + ((N₁ - (d + j) : ℕ) : ℂ)) := by
        convert mode_mem_weight A₁ hu hw₁ M' using 1
        congr 1
        rw [hM', Nat.cast_sub h1]; push_cast; ring
      rw [c2_pair_monomial hB (by omega) hw₁' hw₂ hw₃ hw₄]
      apply pair3_congr
      · rw [hp]; push_cast; ring
      · rw [hq]; push_cast; ring
      · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1]; push_cast; ring
    · rw [c2_zero, mode_eq_zero_of_le hl₁ hu hw₁ (by rw [hM']; omega)]
      simp
  have hz : (∑ k ∈ Finset.range K, cbz M' (k : ℤ) * f (P p (XY r w₃ w₄)
      (ZT (M' + q - k) (mode (A₂.YM u) k w₂) w₁))) = ∑ k ∈ Finset.range (N₂ + d),
        c2 (cbz M' (k : ℤ) • (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (j + k + 1)) *
          normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁
            (mode (A₂.YM u) k w₂) w₃ w₄ N₀ (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))) m n := by
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_pair_monomial hB (by omega) hw₁ (mode_mem_weight_nat hu hw₂ hk') hw₃ hw₄]
    congr 1
    apply pair3_congr
    · rw [hp]; push_cast; ring
    · rw [hq, hM']; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₂ + d by omega)]
      push_cast; ring
  have hy : (∑ k ∈ Finset.range K, cbz M' (k : ℤ) * f (P (M' + p - k)
      (XY r w₃ (mode (A₄.YM u) k w₄)) (ZT q w₂ w₁))) = ∑ k ∈ Finset.range (N₄ + d),
        c2 (cbz M' (k : ℤ) • (X ^ (j + k + 1) * PowerSeries.C (X ^ (j + k + 1)) *
          normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁ w₂ w₃
            (mode (A₄.YM u) k w₄) N₀ (N₀ + N₁ + N₂ + N₃ + (N₄ + d - (k + 1))))) m n := by
    rw [sum_range_trim (J := N₄ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [c2_smul, c2_pair_monomial hB (by omega) hw₁ hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hk')]
    congr 1
    apply pair3_congr
    · rw [hp, hM']; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show k + 1 ≤ N₄ + d by omega)]
      push_cast; ring
  have hx : (∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K, cbz M' (k : ℤ) *
      (cbz (k : ℤ) (l : ℤ) * f (P (M' + p - k) (XY (k + r - l)
        (mode (A₃.YM u) l w₃) w₄) (ZT q w₂ w₁)))) = ∑ k ∈ Finset.range (2 * d + j),
        ∑ l ∈ Finset.range (N₃ + d), c2 ((cbz M' (k : ℤ) * cbz (k : ℤ) (l : ℤ)) •
          (X ^ (j + k + 1) * PowerSeries.C (X ^ (j + k + 1)) *
            normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C ν μ f w₁ w₂
              (mode (A₃.YM u) l w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + d - (l + 1)) + N₄))) m n := by
    rw [sum_range_trim (J := 2 * d + j) (by omega) (fun k hk => Finset.sum_eq_zero fun l _ => by
      rw [hcbzK k hk, zero_mul])]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [sum_range_trim (J := N₃ + d) (by omega) (fun l hl => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]; simp)]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    rw [c2_smul, c2_pair_monomial hB (by omega) hw₁ hw₂ (mode_mem_weight_nat hu hw₃ hl') hw₄,
      mul_assoc]
    congr 2
    apply pair3_congr
    · rw [hp, hM']; push_cast; ring
    · rw [hq]; push_cast; ring
    · rw [hr, hs]; simp only [Nat.cast_add, Nat.cast_sub (show l + 1 ≤ N₃ + d by omega)]
      push_cast; ring
  rw [he, hz, hy, hx]
  simp only [mul_add]
  ring

end VOA.Huang.FivePointSep
