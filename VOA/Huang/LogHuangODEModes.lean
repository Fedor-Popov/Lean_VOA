import VOA.Huang.HuangODEModes
import VOA.Modules.LogTensorPzJacobiModes

/-! Genuine Huang mode relations for logarithmic coefficients.
Only Jacobi and truncation are used in the four-slot weight reduction.
No semisimple L(0) or ordinary-module hypothesis is imposed. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEModes
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.HuangODEModes
open VOA.Huang.MatrixCoeffIterate
open scoped BigOperators
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

/-- Every actual logarithmic coefficient is a genuine truncated Jacobi family. -/
theorem logCoefficient_isJacobi {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (k : ℕ) :
    IsJacobiFamily A₁ A₂ A₃ (fun n => Y n k) where
  truncation := by
    intro x y n
    obtain ⟨K,hK⟩ := hY.truncation x y n
    exact ⟨K,fun j hj => hK j hj k⟩
  jacobi := fun u x y ell m n => hY.jacobi u x y ell m n k

/-- The **commutator formula** (Jacobi at `ℓ = 0`), at every log degree `k`:
`u₍ₘ₎ (w₁)_{n;k} w₂ − (w₁)_{n;k} u₍ₘ₎ w₂ = ∑ᵢ C(m,i) (u₍ᵢ₎ w₁)_{m+n−i;k} w₂`. -/
theorem jacobi_commutator {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsJacobiFamily A₁ A₂ A₃ Y)
    (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (m : ℤ) (n : ℂ) :
    mode (A₃.YM u) m (Y n w₁ w₂) - Y n w₁ (mode (A₂.YM u) m w₂)
      = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) (mode (A₁.YM u) i w₁) w₂ := by
  have h := hY.jacobi u w₁ w₂ 0 m n
  rw [finsum_eq_single _ (0 : ℤ)] at h
  · simpa [cbz_zero_left, negOnePow] using h
  · intro i hi
    simp [cbz_zero_left, hi]

/-- **The `u₋₁`-iterate formula** (Jacobi at `(ℓ, m) = (−1, 0)`):
`(u₋₁ w₁)₍ₙ₎ w₂ = Σ_{i ≥ 0} (u₋₁₋ᵢ (w₁)₍ₙ₊ᵢ₎ w₂ + (w₁)₍ₙ₋₁₋ᵢ₎ uᵢ w₂)`. -/
theorem mode_neg_one_left {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsJacobiFamily A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (n : ℂ) :
    Y n (mode (A₁.YM u) (-1) w₁) w₂
      = ∑ᶠ i : ℤ, if 0 ≤ i then
          mode (A₃.YM u) (-1 - i) (Y (n + i) w₁ w₂) + Y (n - 1 - i) w₁ (mode (A₂.YM u) i w₂)
        else 0 := by
  have h := hY.jacobi u w₁ w₂ (-1) 0 n
  rw [finsum_eq_single (fun i : ℤ => cbz 0 i • Y (((0 : ℤ) : ℂ) + n - i)
      (mode (A₁.YM u) (-1 + i) w₁) w₂) 0 (fun i hi => by simp [cbz_zero_left, hi])] at h
  simp only [cbz_zero, one_smul, Int.cast_zero, zero_add, sub_zero, add_zero] at h
  rw [← h]
  refine finsum_congr fun i => ?_
  split_ifs with hi
  · rw [cbz_neg_one_mul_negOnePow hi, one_smul]
    have e2 : ((-1 : ℤ) : ℂ) + n - i = n - 1 - (i : ℂ) := by push_cast; ring
    have e3 : negOnePow (-1) = -1 := by
      rw [negOnePow, if_neg]
      exact Int.not_even_iff_odd.mpr ⟨-1, by ring⟩
    simp only [e3, neg_one_smul, sub_neg_eq_add, e2]
  · simp [cbz_apply_neg _ (not_le.mp hi)]

section Moves

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
  {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {Y : IntertwiningModes M₁ M₂ M₃}

/-- The commutator formula with a `Finset.range` sum. -/
theorem comm_range (hY : IsJacobiFamily A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (m : ℤ) (n : ℂ) (K : ℕ) (hK : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0) :
    Y n w₁ (mode (A₂.YM u) m w₂)
      = mode (A₃.YM u) m (Y n w₁ w₂)
        - ∑ k ∈ Finset.range K, cbz m k • Y (m + n - k) (mode (A₁.YM u) k w₁) w₂ := by
  have h := jacobi_commutator hY u w₁ w₂ m n
  rw [finsum_eq_sum_range _ K (fun i hi => by
    rcases hi with hi | hi
    · simp [cbz_apply_neg m hi]
    · rw [hK i hi]; simp)] at h
  simp only [Int.cast_natCast] at h
  rw [← h]; abel

/-- The `u₋₁`-iterate formula with a `Finset.range` sum (`I` beyond both truncations). -/
theorem negOneLeft_range (hY : IsJacobiFamily A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (n : ℂ) (I : ℕ)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y (n + i) w₁ w₂ = 0 ∧ mode (A₂.YM u) i w₂ = 0) :
    Y n (mode (A₁.YM u) (-1) w₁) w₂
      = ∑ i ∈ Finset.range I, (mode (A₃.YM u) (-1 - i) (Y (n + i) w₁ w₂)
          + Y (n - 1 - i) w₁ (mode (A₂.YM u) i w₂)) := by
  rw [mode_neg_one_left hY]
  rw [finsum_eq_sum_range _ I (fun i hi => by
    rcases hi with hi | hi
    · simp [not_le.mpr hi]
    · obtain ⟨h1, h2⟩ := hI i hi
      rw [h1, h2]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_pos (by positivity)]
  simp only [Int.cast_natCast]

/-- The iterate formula `(u₍ℓ₎ w₁)₍ₙ₎ w₂` (Jacobi at `m = 0`) with `Finset.range` sums. -/
theorem iterate_range (hY : IsJacobiFamily A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ : ℤ) (n : ℂ) (I : ℕ)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y (n + i) w₁ w₂ = 0 ∧ mode (A₂.YM u) i w₂ = 0) :
    Y n (mode (A₁.YM u) ℓ w₁) w₂
      = ∑ i ∈ Finset.range I, (negOnePow i * cbz ℓ i) •
          (mode (A₃.YM u) (ℓ - i) (Y (n + i) w₁ w₂)
            - negOnePow ℓ • Y (ℓ + n - i) w₁ (mode (A₂.YM u) i w₂)) := by
  have h := hY.jacobi u w₁ w₂ ℓ 0 n
  rw [finsum_eq_single (fun i : ℤ => cbz 0 i • Y (((0 : ℤ) : ℂ) + n - i)
      (mode (A₁.YM u) (ℓ + i) w₁) w₂) 0 (fun i hi => by simp [cbz_zero_left, hi])] at h
  simp only [cbz_zero, one_smul, Int.cast_zero, zero_add, sub_zero, add_zero] at h
  rw [← h]
  rw [finsum_eq_sum_range _ I (fun i hi => by
    rcases hi with hi | hi
    · simp [cbz_apply_neg ℓ hi]
    · obtain ⟨h1, h2⟩ := hI i hi
      rw [h1, h2]; simp)]
  simp only [Int.cast_natCast]

end Moves

/-! ## Products -/

section Product

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {A₄ : WeakModule W M₄} {A₅ : WeakModule W M₅}
  {Y₁ : IntertwiningModes M₁ M₅ M₄} {Y₂ : IntertwiningModes M₂ M₃ M₅}

/-- **Slot 3 (`𝒞`)**: `u₋₁` on `w₃` moves onto `f`, `w₁`, `w₂` (two commutators). -/
theorem prod_slot3 (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (p q : ℂ) (K : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0) :
    f (Y₁ p w₁ (Y₂ q w₂ (mode (A₃.YM u) (-1) w₃)))
      = f (mode (A₄.YM u) (-1) (Y₁ p w₁ (Y₂ q w₂ w₃)))
        - ∑ k ∈ Finset.range K, cbz (-1) k * f (Y₁ (-1 + p - k) (mode (A₁.YM u) k w₁)
            (Y₂ q w₂ w₃))
        - ∑ k ∈ Finset.range K, cbz (-1) k * f (Y₁ p w₁ (Y₂ (-1 + q - k)
            (mode (A₂.YM u) k w₂) w₃)) := by
  rw [comm_range hY₂ u w₂ w₃ (-1) q K hK₂, map_sub, comm_range hY₁ u w₁ _ (-1) p K hK₁]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  push_cast
  abel

/-- **Slot 2 (`ℬ`)**: `u₋₁` on `w₂` (iterate formula for `𝒴₂`, then a commutator through
`𝒴₁` with the mode `u₍₋₁₋ᵢ₎`). -/
theorem prod_slot2 (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (p q : ℂ) (K I : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₂ (q + i) w₂ w₃ = 0 ∧ mode (A₃.YM u) i w₃ = 0) :
    f (Y₁ p w₁ (Y₂ q (mode (A₂.YM u) (-1) w₂) w₃))
      = ∑ i ∈ Finset.range I, (f (mode (A₄.YM u) (-1 - i) (Y₁ p w₁ (Y₂ (q + i) w₂ w₃)))
          - ∑ k ∈ Finset.range K, cbz (-1 - i) k * f (Y₁ ((-1 - i : ℤ) + p - k)
              (mode (A₁.YM u) k w₁) (Y₂ (q + i) w₂ w₃))
          + f (Y₁ p w₁ (Y₂ (q - 1 - i) w₂ (mode (A₃.YM u) i w₃)))) := by
  rw [negOneLeft_range hY₂ u w₂ w₃ q I hI, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_add, comm_range hY₁ u w₁ _ (-1 - i) p K hK₁]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]

/-- **Slot 1 (`𝒜`)**: `u₋₁` on `w₁` (iterate formula for `𝒴₁`, then the commutator of `uᵢ`,
`i ≥ 0`, through `𝒴₂`). -/
theorem prod_slot1 (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (p q : ℂ) (K I : ℕ) (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₁ (p + i) w₁ (Y₂ q w₂ w₃) = 0 ∧
      mode (A₅.YM u) i (Y₂ q w₂ w₃) = 0) :
    f (Y₁ p (mode (A₁.YM u) (-1) w₁) (Y₂ q w₂ w₃))
      = ∑ i ∈ Finset.range I, (f (mode (A₄.YM u) (-1 - i) (Y₁ (p + i) w₁ (Y₂ q w₂ w₃)))
          + f (Y₁ (p - 1 - i) w₁ (Y₂ q w₂ (mode (A₃.YM u) i w₃)))
          + ∑ k ∈ Finset.range K, cbz i k * f (Y₁ (p - 1 - i) w₁
              (Y₂ ((i : ℤ) + q - k) (mode (A₂.YM u) k w₂) w₃))) := by
  rw [negOneLeft_range hY₁ u w₁ _ p I hI, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc := comm_range hY₂ u w₂ w₃ (i : ℤ) q K hK₂
  rw [eq_sub_iff_add_eq] at hc
  rw [map_add, ← hc]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  push_cast
  ring

end Product

end VOA.Huang.LogHuangODEModes
