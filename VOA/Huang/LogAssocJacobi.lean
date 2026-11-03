import VOA.Huang.LogHuangODEConvergence
import VOA.Huang.LogHuangODEModes
import VOA.Huang.AssocAssociator

/-! Actual product Jacobi identities on arbitrary weak modules. Each
true logarithmic coefficient is a truncated Jacobi family; all mode
cosets have genuine absolute convergence under C2-cofiniteness. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocJacobi
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.MatrixCoeff
open VOA.Huang.AssocCommutator (prodTermZ prodValueZ finsum_eq_sum_Ico cpow_shift
  summable_prodTermZ_of_base summable_prodTermZ_shift_iff)
open VOA.Huang.LogHuangODEModes (jacobi_commutator logCoefficient_isJacobi)
open VOA.Huang.LogHuangODEProduct
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {A₄ : WeakModule W M₄} {A₅ : WeakModule W M₅}

theorem prodCoeff_commutator {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (v : V) (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {N : ℤ} (hN₁ : ∀ i, N ≤ i → mode (A₁.YM v) i w₁ = 0)
    (hN₂ : ∀ i, N ≤ i → mode (A₂.YM v) i w₂ = 0) (n₁ n₂ : ℂ) :
    prodCoeff Y₁ Y₂ (f ∘ₗ mode (A₄.YM v) m) w₁ w₂ w₃ n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ (mode (A₃.YM v) m w₃) n₁ n₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i
            * prodCoeff Y₁ Y₂ f (mode (A₁.YM v) i w₁) w₂ w₃ (m + n₁ - i) n₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i
            * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM v) i w₂) w₃ n₁ (m + n₂ - i) := by
  have c₁ := jacobi_commutator hY₁ v w₁ (Y₂ n₂ w₂ w₃) m n₁
  have c₂ := jacobi_commutator hY₂ v w₂ w₃ m n₂
  rw [finsum_eq_sum_Ico (N := N) (fun i hi => by simp [cbz_apply_neg m hi])
    (fun i hi => by rw [hN₁ i hi, map_zero, LinearMap.zero_apply, smul_zero])] at c₁
  rw [finsum_eq_sum_Ico (N := N) (fun i hi => by simp [cbz_apply_neg m hi])
    (fun i hi => by rw [hN₂ i hi, map_zero, LinearMap.zero_apply, smul_zero])] at c₂
  have e₁ := congrArg f c₁
  have e₂ := congrArg (fun q => f (Y₁ n₁ w₁ q)) c₂
  simp only [map_sub, map_sum, map_smul, smul_eq_mul] at e₁ e₂
  simp only [prodCoeff, LinearMap.comp_apply]
  linear_combination e₁ + e₂


theorem prodTermZ_commutator {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (v : V) (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {N : ℤ} (hN₁ : ∀ i, N ≤ i → mode (A₁.YM v) i w₁ = 0)
    (hN₂ : ∀ i, N ≤ i → mode (A₂.YM v) i w₂ = 0) (S ν : ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0)
    (hz₂ : z₂ ≠ 0) (k : ℤ) :
    prodTermZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM v) m) w₁ w₂ w₃ S ν z₁ z₂ k
      = prodTermZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM v) m w₃) S ν z₁ z₂ k
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * z₁ ^ ((m - i : ℤ) : ℂ)
            * prodTermZ Y₁ Y₂ f (mode (A₁.YM v) i w₁) w₂ w₃ (S + (m - i : ℤ)) ν z₁ z₂ k
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * z₂ ^ ((m - i : ℤ) : ℂ)
            * prodTermZ Y₁ Y₂ f w₁ (mode (A₂.YM v) i w₂) w₃ (S + (m - i : ℤ))
                (ν + (m - i : ℤ)) z₁ z₂ k := by
  unfold prodTermZ
  rw [prodCoeff_commutator hY₁ hY₂ v m f w₁ w₂ w₃ hN₁ hN₂, add_mul, add_mul, add_mul, add_mul,
    Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (m : ℂ) + (S - ν + k) - i = S + ((m - i : ℤ) : ℂ) - ν + k := by push_cast; ring
    rw [e1]
    have hp := cpow_shift hz₁ (S - ν + k) (m - i)
    have e2 : S + ((m - i : ℤ) : ℂ) - ν + k = S - ν + k + ((m - i : ℤ) : ℂ) := by ring
    rw [e2] at ⊢
    rw [← hp]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (m : ℂ) + (ν - k) - i = ν + ((m - i : ℤ) : ℂ) - k := by push_cast; ring
    have e3 : S + ((m - i : ℤ) : ℂ) - (ν + ((m - i : ℤ) : ℂ)) + k = S - ν + k := by ring
    rw [e1, e3]
    have hp := cpow_shift hz₂ (ν - k) (m - i)
    have e2 : ν + ((m - i : ℤ) : ℂ) - k = ν - k + ((m - i : ℤ) : ℂ) := by ring
    rw [e2]
    rw [← hp]
    ring

/-- **The commutator identity for values** (given summability of the right-hand series). -/
theorem prodValueZ_commutator {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (v : V) (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {N : ℤ} (hN₁ : ∀ i, N ≤ i → mode (A₁.YM v) i w₁ = 0)
    (hN₂ : ∀ i, N ≤ i → mode (A₂.YM v) i w₂ = 0) (S ν : ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0)
    (hz₂ : z₂ ≠ 0)
    (s₃ : Summable (prodTermZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM v) m w₃) S ν z₁ z₂))
    (s₁ : ∀ i ∈ Finset.Ico 0 N,
      Summable (prodTermZ Y₁ Y₂ f (mode (A₁.YM v) i w₁) w₂ w₃ (S + (m - i : ℤ)) ν z₁ z₂))
    (s₂ : ∀ i ∈ Finset.Ico 0 N,
      Summable (prodTermZ Y₁ Y₂ f w₁ (mode (A₂.YM v) i w₂) w₃ (S + (m - i : ℤ))
        (ν + (m - i : ℤ)) z₁ z₂)) :
    prodValueZ Y₁ Y₂ (f ∘ₗ mode (A₄.YM v) m) w₁ w₂ w₃ S ν z₁ z₂
      = prodValueZ Y₁ Y₂ f w₁ w₂ (mode (A₃.YM v) m w₃) S ν z₁ z₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * z₁ ^ ((m - i : ℤ) : ℂ)
            * prodValueZ Y₁ Y₂ f (mode (A₁.YM v) i w₁) w₂ w₃ (S + (m - i : ℤ)) ν z₁ z₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * z₂ ^ ((m - i : ℤ) : ℂ)
            * prodValueZ Y₁ Y₂ f w₁ (mode (A₂.YM v) i w₂) w₃ (S + (m - i : ℤ))
                (ν + (m - i : ℤ)) z₁ z₂ := by
  unfold prodValueZ
  have t₁ : Summable fun k => ∑ i ∈ Finset.Ico 0 N, cbz m i * z₁ ^ ((m - i : ℤ) : ℂ)
      * prodTermZ Y₁ Y₂ f (mode (A₁.YM v) i w₁) w₂ w₃ (S + (m - i : ℤ)) ν z₁ z₂ k :=
    summable_sum fun i hi => (s₁ i hi).mul_left _
  have t₂ : Summable fun k => ∑ i ∈ Finset.Ico 0 N, cbz m i * z₂ ^ ((m - i : ℤ) : ℂ)
      * prodTermZ Y₁ Y₂ f w₁ (mode (A₂.YM v) i w₂) w₃ (S + (m - i : ℤ))
          (ν + (m - i : ℤ)) z₁ z₂ k :=
    summable_sum fun i hi => (s₂ i hi).mul_left _
  rw [tsum_congr fun k => prodTermZ_commutator hY₁ hY₂ v m f w₁ w₂ w₃ hN₁ hN₂ S ν hz₁ hz₂ k,
    (s₃.add t₁).tsum_add t₂, s₃.tsum_add t₁,
    Summable.tsum_finsetSum (fun i hi => (s₁ i hi).mul_left _),
    Summable.tsum_finsetSum (fun i hi => (s₂ i hi).mul_left _)]
  simp only [tsum_mul_left]


end VOA.Huang.LogAssocJacobi
