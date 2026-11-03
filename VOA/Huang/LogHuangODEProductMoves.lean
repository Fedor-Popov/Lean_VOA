import VOA.Huang.LogHuangODEProductWeights
import VOA.Huang.LogHuangODEProductAlgebra

/-! Huang's regular four-slot product moves for genuine graded Jacobi families.
The modules are grading-restricted generalized modules, and the individual
logarithmic coefficients are never assigned an ordinary derivative law. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEProduct
open VOA VOA.C2Rigid PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEModes VOA.Huang.MatrixCoeff
open VOA.Huang.HuangODEProduct (sum_range_trim)
open VOA.Huang.HuangODEModes (cbz_nat cbz_neg_one_sub)
open scoped BigOperators
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Product

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : GWModule W M₁} {A₂ : GWModule W M₂} {A₃ : GWModule W M₃}
  {A₄ : GWModule W M₄} {A₅ : GWModule W M₅}
  {Y₁ : IntertwiningModes M₁ M₅ M₄} {Y₂ : IntertwiningModes M₂ M₃ M₅}

/-- `Σ_n f(𝒴₁(w₁)₍ₐ₊ₙ₎ 𝒴₂(w₂)₍ᵦ₋ₙ₎ w₃) xⁿ`. -/
noncomputable def prodQ (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (a b : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => f (Y₁ (a + n) w₁ (Y₂ (b - n) w₂ w₃))

theorem coeff_prodQ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (a b : ℂ) (n : ℕ) :
    coeff n (prodQ Y₁ Y₂ f w₁ w₂ w₃ a b) = f (Y₁ (a + n) w₁ (Y₂ (b - n) w₂ w₃)) :=
  coeff_mk _ _

/-- Coefficients of `xᵉ · prodQ`, given a base at `b`. -/
theorem coeff_X_pow_mul_prodQ {f : M₄ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {a b : ℂ}
    (hb : IsBase Y₂ w₂ w₃ b) (e n : ℕ) :
    coeff n (X ^ e * prodQ Y₁ Y₂ f w₁ w₂ w₃ a b)
      = f (Y₁ (a + n - e) w₁ (Y₂ (b - n + e) w₂ w₃)) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_prodQ]
    have e1 : a + ((n - e : ℕ) : ℂ) = a + n - e := by rw [Nat.cast_sub h]; ring
    have e2 : b - ((n - e : ℕ) : ℂ) = b - n + e := by rw [Nat.cast_sub h]; ring
    rw [e1, e2]
  · have e3 : b - n + e = b + (((e - n - 1 : ℕ) : ℂ) + 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e3, hb, map_zero, map_zero]

/-- Coefficients of `x · (Σ_i C(i,k) xⁱ) · prodQ` as a finite sum, given a base at `b`. -/
theorem coeff_X_mul_binom_mul_prodQ {f : M₄ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {a b : ℂ}
    (hb : IsBase Y₂ w₂ w₃ b) (k n I : ℕ) (hI : n < I) :
    coeff n (X * HuangODEAlgebra.binomSeries 1 k * prodQ Y₁ Y₂ f w₁ w₂ w₃ a b)
      = ∑ i ∈ Finset.range I, (i.choose k : ℂ) *
          f (Y₁ (a + n - 1 - i) w₁ (Y₂ (b - n + 1 + i) w₂ w₃)) := by
  have e : X * HuangODEAlgebra.binomSeries 1 k * prodQ Y₁ Y₂ f w₁ w₂ w₃ a b
      = HuangODEAlgebra.binomSeries 1 k * X ^ 1 * prodQ Y₁ Y₂ f w₁ w₂ w₃ a b := by ring
  rw [e, HuangODEAlgebra.binomSeries, coeff_conv _ _ _ hI]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [one_pow, mul_one, coeff_prodQ]
    have e1 : a + ((n - 1 - i : ℕ) : ℂ) = a + n - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : b - ((n - 1 - i : ℕ) : ℂ) = b - n + 1 + i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2]
  · have e3 : b - n + 1 + i = b + (((i - n : ℕ) : ℂ) + 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e3, hb, map_zero, map_zero, mul_zero]

theorem prodQ_congr {f : M₄ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {p p' q q' : ℂ}
    (hp : p = p') (hq : q = q') :
    f (Y₁ p w₁ (Y₂ q w₂ w₃)) = f (Y₁ p' w₁ (Y₂ q' w₂ w₃)) := by
  rw [hp, hq]

/-- The vector of a product lies on one weight. -/
theorem prod_mem_weight (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) {α₁ α₂ α₃ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (h₃ : w₃ ∈ A₃.weight α₃) (p q : ℂ) :
    Y₁ p w₁ (Y₂ q w₂ w₃) ∈ A₄.weight (α₁ + α₂ + α₃ - p - q - 2) := by
  have hin := hY₂.mem_weight h₂ h₃ q
  have hout := hY₁.mem_weight h₁ hin p
  have e : α₁ + (α₂ + α₃ - q - 1) - p - 1 = α₁ + α₂ + α₃ - p - q - 2 := by ring
  rw [e] at hout
  exact hout

/-- **Uniform base**: `ν + N₂ + N₃` is a base of `𝒴₂` at every pair of homogeneous vectors of
levels `N₂, N₃` (holds for `Re ν ≫ 0` since `M₅` is bounded below: `exists_unifBase`). -/
def UnifBase (A₂ : GWModule W M₂) (A₃ : GWModule W M₃) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (h₂ h₃ ν : ℂ) : Prop :=
  ∀ (N₂ N₃ : ℕ) (w₂ : M₂) (w₃ : M₃), w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
    IsBase Y₂ w₂ w₃ (ν + N₂ + N₃)

theorem UnifBase.base {h₂ h₃ ν : ℂ} (hUB : UnifBase A₂ A₃ Y₂ h₂ h₃ ν) {N₂ N₃ : ℕ} {w₂ : M₂}
    {w₃ : M₃} (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂)) (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) {s : ℕ}
    (hs : N₂ + N₃ ≤ s) : IsBase Y₂ w₂ w₃ (ν + s) := by
  have hb := (hUB N₂ N₃ w₂ w₃ hw₂ hw₃).add_nat (s - (N₂ + N₃))
  have e : ν + (N₂ : ℂ) + N₃ + ((s - (N₂ + N₃) : ℕ) : ℂ) = ν + s := by
    rw [Nat.cast_sub hs]; push_cast; ring
  rwa [e] at hb

/-- The normalized series of the tuple `(f, w₁, w₂, w₃)` at levels `(N₁, N₂, N₃, N₄)`, total level
`s = N₁ + N₂ + N₃ + N₄`: `Σ_n f(𝒴₁(w₁)₍c−ν−2N₄+n₎ 𝒴₂(w₂)₍ν+s−n₎ w₃) xⁿ`
(`c = h₁ + h₂ + h₃ − h₄ − 2`).  It is `x^{s+K}` times the coset series `prodSeries`. -/
noncomputable def QT (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (c ν : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (N₄ s : ℕ) : PowerSeries ℂ :=
  prodQ Y₁ Y₂ f w₁ w₂ w₃ (c - ν - 2 * N₄) (ν + s)

section Moves

variable {h₁ h₂ h₃ h₄ ν : ℂ}

/-- **Move `𝒜`** (outer vector `u₋₁w₁`, Huang's `𝒜`): a regular relation. -/
theorem moveA (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) (hl₂ : CosetBase A₂ h₂)
    (hl₃ : CosetBase A₃ h₃) (hl₄ : CosetBase A₄ h₄)
    (hUB : UnifBase A₂ A₃ Y₂ h₂ h₃ ν) {d : ℕ} {u : 𝒱} (hu : u ∈ W.grading (d : ℤ))
    (f : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f (mode (A₁.YM u) (-1) w₁) w₂ w₃ N₄
        (N₁ + d + N₂ + N₃ + N₄)
      = ∑ i ∈ Finset.range (N₄ + 1 - d), X ^ (2 * d + i) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν (f ∘ₗ mode (A₄.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃
            (N₄ - (d + i)) (N₁ + N₂ + N₃ + (N₄ - (d + i)))
        + ∑ i ∈ Finset.range (N₃ + d), X ^ (i + 1) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ (mode (A₃.YM u) (i : ℤ) w₃) N₄
            (N₁ + N₂ + (N₃ + d - (i + 1)) + N₄)
        + ∑ k ∈ Finset.range (N₂ + d), X * HuangODEAlgebra.binomSeries 1 k *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ (mode (A₂.YM u) (k : ℤ) w₂) w₃ N₄
            (N₁ + (N₂ + d - (k + 1)) + N₃ + N₄) := by
  ext n
  rw [map_add, map_add, map_sum, map_sum, map_sum, QT, coeff_prodQ]
  obtain ⟨T₁, hT₁⟩ := hY₁.truncation w₁
    (Y₂ (ν + ((N₁ + d + N₂ + N₃ + N₄ : ℕ) : ℂ) - n) w₂ w₃)
    (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n)
  obtain ⟨T₂, hT₂⟩ := A₅.truncation u (Y₂ (ν + ((N₁ + d + N₂ + N₃ + N₄ : ℕ) : ℂ) - n) w₂ w₃)
  have hT₁' := Int.self_le_toNat T₁
  have hT₂' := Int.self_le_toNat T₂
  rw [prod_slot1 hY₁.toIsJacobiFamily hY₂.toIsJacobiFamily u f w₁ w₂ w₃ _ _ (N₂ + d) (T₁.toNat + T₂.toNat + n + N₄ + N₃ + d + 1)
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by push_cast at hk ⊢; omega))
    (fun i hi => ⟨hT₁ i (by push_cast at hi; omega), hT₂ i (by push_cast at hi; omega)⟩)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · rw [sum_range_trim (J := N₄ + 1 - d) (by omega) (fun i hi => by
      rw [eq_zero_of_mem_weight_neg hl₄ (prod_mem_weight hY₁ hY₂ hw₁ hw₂ hw₃ _ _)
        (j := (N₄ : ℤ) - d - i) (by push_cast; ring) (by omega), map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [QT, coeff_X_pow_mul_prodQ (hUB.base hw₂ hw₃ (by omega)), LinearMap.comp_apply]
    obtain ⟨r, rfl⟩ : ∃ r, N₄ = d + i + r := ⟨N₄ - (d + i), by omega⟩
    have e : d + i + r - (d + i) = r := by omega
    rw [e]
    congr 3 <;> push_cast <;> ring
  · rw [sum_range_trim (J := N₃ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega), map_zero, map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [QT, coeff_X_pow_mul_prodQ (hUB.base hw₂ (mode_mem_weight_nat hu hw₃ hi) (by omega))]
    obtain ⟨r, hr⟩ : ∃ r, N₃ + d = i + 1 + r := ⟨N₃ + d - (i + 1), by omega⟩
    have e : N₃ + d - (i + 1) = r := by omega
    rw [e]
    have hr' : (N₃ : ℂ) + d = i + 1 + r := by exact_mod_cast hr
    exact prodQ_congr (by push_cast; ring) (by push_cast; linear_combination hr')
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [QT, coeff_X_mul_binom_mul_prodQ (hUB.base (mode_mem_weight_nat hu hw₂ hk) hw₃
      (by omega)) k n (T₁.toNat + T₂.toNat + n + N₄ + N₃ + d + 1) (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_nat]
    obtain ⟨r, hr⟩ : ∃ r, N₂ + d = k + 1 + r := ⟨N₂ + d - (k + 1), by omega⟩
    have e : N₂ + d - (k + 1) = r := by omega
    rw [e]
    have hr' : (N₂ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    exact congrArg _ (prodQ_congr (by push_cast; ring) (by push_cast; linear_combination hr'))

/-- **Move `ℬ`** (inner vector `u₋₁w₂`, Huang's `ℬ`): a regular relation. -/
theorem moveB (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) (hl₁ : CosetBase A₁ h₁)
    (hl₃ : CosetBase A₃ h₃) (hl₄ : CosetBase A₄ h₄)
    (hUB : UnifBase A₂ A₃ Y₂ h₂ h₃ ν) {d : ℕ} {u : 𝒱} (hu : u ∈ W.grading (d : ℤ))
    (f : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ (mode (A₂.YM u) (-1) w₂) w₃ N₄
        (N₁ + N₂ + d + N₃ + N₄)
      = ∑ i ∈ Finset.range (N₄ + 1 - d), X ^ (2 * d + 2 * i) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν (f ∘ₗ mode (A₄.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃
            (N₄ - (d + i)) (N₁ + N₂ + N₃ + (N₄ - (d + i)))
        - ∑ k ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ k) • (X * HuangODEAlgebra.binomSeries 1 k *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f (mode (A₁.YM u) (k : ℤ) w₁) w₂ w₃ N₄
            (N₁ + d - (k + 1) + N₂ + N₃ + N₄))
        + ∑ i ∈ Finset.range (N₃ + d),
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ (mode (A₃.YM u) (i : ℤ) w₃) N₄
            (N₁ + N₂ + (N₃ + d - (i + 1)) + N₄) := by
  ext n
  rw [map_add, map_sub, map_sum, map_sum, map_sum, QT, coeff_prodQ]
  obtain ⟨T, hT⟩ := hY₂.truncation w₂ w₃ (ν + ((N₁ + N₂ + d + N₃ + N₄ : ℕ) : ℂ) - n)
  have hT' := Int.self_le_toNat T
  rw [prod_slot2 hY₁.toIsJacobiFamily hY₂.toIsJacobiFamily u f w₁ w₂ w₃ _ _ (N₁ + d) (T.toNat + n + N₄ + N₃ + d + 1)
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by push_cast at hk ⊢; omega))
    (fun i hi => ⟨hT i (by push_cast at hi; omega),
      mode_eq_zero_of_le hl₃ hu hw₃ (by push_cast at hi ⊢; omega)⟩)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· - ·) ?_ ?_) ?_
  · rw [sum_range_trim (J := N₄ + 1 - d) (by omega) (fun i hi => by
      rw [eq_zero_of_mem_weight_neg hl₄ (prod_mem_weight hY₁ hY₂ hw₁ hw₂ hw₃ _ _)
        (j := (N₄ : ℤ) - d - i) (by push_cast; ring) (by omega), map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [QT, coeff_X_pow_mul_prodQ (hUB.base hw₂ hw₃ (by omega)), LinearMap.comp_apply]
    obtain ⟨r, rfl⟩ : ∃ r, N₄ = d + i + r := ⟨N₄ - (d + i), by omega⟩
    have e : d + i + r - (d + i) = r := by omega
    rw [e]
    congr 3 <;> push_cast <;> ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [map_smul, QT, coeff_X_mul_binom_mul_prodQ (hUB.base hw₂ hw₃ (by omega)) k n
      (k + (T.toNat + n + N₄ + N₃ + d + 1)) (by omega),
      Finset.sum_range_add _ k (T.toNat + n + N₄ + N₃ + d + 1)]
    rw [Finset.sum_eq_zero (s := Finset.range k) (fun j hj => by
      simp only [Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul]), zero_add, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cbz_neg_one_sub, add_comm k i, mul_assoc]
    obtain ⟨r, hr⟩ : ∃ r, N₁ + d = k + 1 + r := ⟨N₁ + d - (k + 1), by omega⟩
    have e : N₁ + d - (k + 1) = r := by omega
    rw [e]
    have hr' : (N₁ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    exact congrArg _ (congrArg _ (prodQ_congr (by push_cast; ring)
      (by push_cast; linear_combination hr')))
  · rw [sum_range_trim (J := N₃ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega), map_zero, map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [QT, coeff_prodQ]
    obtain ⟨r, hr⟩ : ∃ r, N₃ + d = i + 1 + r := ⟨N₃ + d - (i + 1), by omega⟩
    have e : N₃ + d - (i + 1) = r := by omega
    rw [e]
    have hr' : (N₃ : ℂ) + d = i + 1 + r := by exact_mod_cast hr
    exact prodQ_congr (by push_cast; ring) (by push_cast; linear_combination hr')

theorem cbz_neg_one_nat (k : ℕ) : cbz (-1) (k : ℤ) = (-1 : ℂ) ^ k := by
  have h := cbz_neg_one_sub 0 k
  simpa using h

/-- **Move `𝒞`** (innermost vector `u₋₁w₃`, Huang's `𝒞`): a regular relation. -/
theorem moveC (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) (hl₁ : CosetBase A₁ h₁)
    (hl₂ : CosetBase A₂ h₂) (hl₄ : CosetBase A₄ h₄)
    (hUB : UnifBase A₂ A₃ Y₂ h₂ h₃ ν) {d : ℕ} {u : 𝒱} (hu : u ∈ W.grading (d : ℤ))
    (f : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ (mode (A₃.YM u) (-1) w₃) N₄
        (N₁ + N₂ + N₃ + d + N₄)
      = (if d ≤ N₄ then X ^ (2 * d) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν (f ∘ₗ mode (A₄.YM u) (-1)) w₁ w₂ w₃
            (N₄ - d) (N₁ + N₂ + N₃ + (N₄ - d)) else 0)
        - ∑ k ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ k) • (X ^ (k + 1) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f (mode (A₁.YM u) (k : ℤ) w₁) w₂ w₃ N₄
            (N₁ + d - (k + 1) + N₂ + N₃ + N₄))
        - ∑ k ∈ Finset.range (N₂ + d), ((-1 : ℂ) ^ k) •
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ (mode (A₂.YM u) (k : ℤ) w₂) w₃ N₄
            (N₁ + (N₂ + d - (k + 1)) + N₃ + N₄) := by
  ext n
  rw [map_sub, map_sub, map_sum, map_sum, QT, coeff_prodQ]
  rw [prod_slot3 hY₁.toIsJacobiFamily hY₂.toIsJacobiFamily u f w₁ w₂ w₃ _ _ (N₁ + N₂ + d)
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by push_cast at hk ⊢; omega))
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by push_cast at hk ⊢; omega))]
  refine congrArg₂ (· - ·) (congrArg₂ (· - ·) ?_ ?_) ?_
  · split_ifs with hd
    · rw [QT, coeff_X_pow_mul_prodQ (hUB.base hw₂ hw₃ (by omega)), LinearMap.comp_apply]
      obtain ⟨r, rfl⟩ : ∃ r, N₄ = d + r := ⟨N₄ - d, by omega⟩
      have e : d + r - d = r := by omega
      rw [e]
      congr 3 <;> push_cast <;> ring
    · rw [map_zero, eq_zero_of_mem_weight_neg hl₄ (prod_mem_weight hY₁ hY₂ hw₁ hw₂ hw₃ _ _)
        (j := (N₄ : ℤ) - d) (by push_cast; ring) (by omega), map_zero, map_zero]
  · rw [sum_range_trim (J := N₁ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega), map_zero, LinearMap.zero_apply,
        map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [map_smul, QT, coeff_X_pow_mul_prodQ (hUB.base hw₂ hw₃ (by omega)), cbz_neg_one_nat,
      smul_eq_mul]
    obtain ⟨r, hr⟩ : ∃ r, N₁ + d = k + 1 + r := ⟨N₁ + d - (k + 1), by omega⟩
    have e : N₁ + d - (k + 1) = r := by omega
    rw [e]
    have hr' : (N₁ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    exact congrArg _ (prodQ_congr (by push_cast; ring) (by push_cast; linear_combination hr'))
  · rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega), map_zero, LinearMap.zero_apply,
        map_zero, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [map_smul, QT, coeff_prodQ, cbz_neg_one_nat, smul_eq_mul]
    obtain ⟨r, hr⟩ : ∃ r, N₂ + d = k + 1 + r := ⟨N₂ + d - (k + 1), by omega⟩
    have e : N₂ + d - (k + 1) = r := by omega
    rw [e]
    have hr' : (N₂ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    exact congrArg _ (prodQ_congr (by push_cast; ring) (by push_cast; linear_combination hr'))

/-- The mode identity behind Huang's `𝒟`: a mode `u₍ₘ₎` on the functional moves through both
operators (two commutator formulas). -/
theorem prod_slot0 (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (g : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (p q : ℂ) (m : ℤ) (K : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0) :
    g (mode (A₄.YM u) m (Y₁ p w₁ (Y₂ q w₂ w₃)))
      = g (Y₁ p w₁ (Y₂ q w₂ (mode (A₃.YM u) m w₃)))
        + ∑ k ∈ Finset.range K, cbz m k * g (Y₁ p w₁ (Y₂ (m + q - k) (mode (A₂.YM u) k w₂) w₃))
        + ∑ k ∈ Finset.range K, cbz m k * g (Y₁ (m + p - k) (mode (A₁.YM u) k w₁)
            (Y₂ q w₂ w₃)) := by
  have h1 := comm_range hY₁.toIsJacobiFamily u w₁ (Y₂ q w₂ w₃) m p K hK₁
  have h2 := comm_range hY₂.toIsJacobiFamily u w₂ w₃ m q K hK₂
  have h1' : mode (A₄.YM u) m (Y₁ p w₁ (Y₂ q w₂ w₃))
      = Y₁ p w₁ (mode (A₅.YM u) m (Y₂ q w₂ w₃))
        + ∑ k ∈ Finset.range K, cbz m k • Y₁ (m + p - k) (mode (A₁.YM u) k w₁) (Y₂ q w₂ w₃) := by
    rw [h1]; abel
  have h2' : mode (A₅.YM u) m (Y₂ q w₂ w₃)
      = Y₂ q w₂ (mode (A₃.YM u) m w₃)
        + ∑ k ∈ Finset.range K, cbz m k • Y₂ (m + q - k) (mode (A₂.YM u) k w₂) w₃ := by
    rw [h2]; abel
  rw [h1', h2']
  simp only [map_add, map_sum, map_smul, smul_eq_mul]

/-- **Move `𝒟`** (the functional is `g ∘ u₍ₘ₎` with `m ≥ 2 wt u − 1`, the shape of the
contragredient `u₋₁`, Huang's `𝒟`): a regular relation. -/
theorem moveD (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) (hl₁ : CosetBase A₁ h₁)
    (hl₂ : CosetBase A₂ h₂) (hl₃ : CosetBase A₃ h₃)
    (hUB : UnifBase A₂ A₃ Y₂ h₂ h₃ ν) {d m : ℕ} (hm : 2 * d ≤ m + 1) {u : 𝒱}
    (hu : u ∈ W.grading (d : ℤ)) (g : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂}
    {w₃ : M₃} (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν (g ∘ₗ mode (A₄.YM u) (m : ℤ)) w₁ w₂ w₃
        (N₄ + (m + 1 - d)) (N₁ + N₂ + N₃ + N₄ + (m + 1 - d))
      = (if m + 1 - d ≤ N₃ then X ^ (2 * (m + 1 - d)) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν g w₁ w₂ (mode (A₃.YM u) (m : ℤ) w₃) N₄
            (N₁ + N₂ + (N₃ - (m + 1 - d)) + N₄) else 0)
        + ∑ j ∈ Finset.range (N₂ + d), ((m.choose j : ℂ)) • (X ^ (2 * (m + 1 - d)) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν g w₁ (mode (A₂.YM u) (j : ℤ) w₂) w₃ N₄
            (N₁ + (N₂ + d - (j + 1)) + N₃ + N₄))
        + ∑ j ∈ Finset.range (N₁ + d), ((m.choose j : ℂ)) • (X ^ (m + 2 + j - 2 * d) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν g (mode (A₁.YM u) (j : ℤ) w₁) w₂ w₃ N₄
            (N₁ + d - (j + 1) + N₂ + N₃ + N₄)) := by
  ext n
  rw [map_add, map_add, map_sum, map_sum, QT, coeff_prodQ, LinearMap.comp_apply]
  rw [prod_slot0 hY₁ hY₂ u g w₁ w₂ w₃ _ _ (m : ℤ) (N₁ + N₂ + d)
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by push_cast at hk ⊢; omega))
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by push_cast at hk ⊢; omega))]
  obtain ⟨e₀, he₀⟩ : ∃ e₀, m + 1 = d + e₀ := ⟨m + 1 - d, by omega⟩
  have hme : m + 1 - d = e₀ := by omega
  have he₀' : (m : ℂ) + 1 = d + e₀ := by exact_mod_cast he₀
  simp only [hme]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · split_ifs with h3
    · rw [QT, coeff_X_pow_mul_prodQ (hUB.base hw₂
        (by
          have hm3 := C2Rigid.mode_mem_weight A₃ hu hw₃ (m : ℤ)
          have e : h₃ + (N₃ : ℂ) + ((d : ℤ) : ℂ) - ((m : ℤ) : ℂ) - 1
              = h₃ + ((N₃ - e₀ : ℕ) : ℂ) := by
            rw [Nat.cast_sub h3]; push_cast; linear_combination -he₀'
          rw [e] at hm3
          exact hm3) (by omega))]
      obtain ⟨r, rfl⟩ : ∃ r, N₃ = e₀ + r := ⟨N₃ - e₀, by omega⟩
      have e : e₀ + r - e₀ = r := by omega
      rw [e]
      exact prodQ_congr (by push_cast; ring) (by push_cast; ring)
    · rw [map_zero, mode_eq_zero_of_le hl₃ hu hw₃ (by push_cast; omega), map_zero, map_zero,
        map_zero]
  · rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega), map_zero, LinearMap.zero_apply,
        map_zero, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [map_smul, QT, coeff_X_pow_mul_prodQ (hUB.base (mode_mem_weight_nat hu hw₂ hk) hw₃
      (by omega)), cbz_nat, smul_eq_mul]
    obtain ⟨r, hr⟩ : ∃ r, N₂ + d = k + 1 + r := ⟨N₂ + d - (k + 1), by omega⟩
    have e : N₂ + d - (k + 1) = r := by omega
    rw [e]
    have hr' : (N₂ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    exact congrArg _ (prodQ_congr (by push_cast; ring)
      (by push_cast; linear_combination hr' + he₀'))
  · rw [sum_range_trim (J := N₁ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega), map_zero, LinearMap.zero_apply,
        map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [map_smul, QT, coeff_X_pow_mul_prodQ (hUB.base hw₂ hw₃ (by omega)), cbz_nat,
      smul_eq_mul]
    obtain ⟨r, hr⟩ : ∃ r, N₁ + d = k + 1 + r := ⟨N₁ + d - (k + 1), by omega⟩
    have e : N₁ + d - (k + 1) = r := by omega
    obtain ⟨t, ht⟩ : ∃ t, m + 2 + k = 2 * d + t := ⟨m + 2 + k - 2 * d, by omega⟩
    have e' : m + 2 + k - 2 * d = t := by omega
    rw [e, e']
    have hr' : (N₁ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    have ht' : (m : ℂ) + 2 + k = 2 * d + t := by exact_mod_cast ht
    exact congrArg _ (prodQ_congr (by push_cast; linear_combination -ht' + 2 * he₀')
      (by push_cast; linear_combination hr' + ht' - he₀'))

end Moves

/-! ## Linearity of the normalized series -/

section Linear

variable (c ν : ℂ) (N₄ s : ℕ)

theorem QT_add_f (f f' : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν (f + f') w₁ w₂ w₃ N₄ s = QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s
      + QT Y₁ Y₂ c ν f' w₁ w₂ w₃ N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_smul_f (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν (a • f) w₁ w₂ w₃ N₄ s = a • QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_zero_f (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν (0 : M₄ →ₗ[ℂ] ℂ) w₁ w₂ w₃ N₄ s = 0 := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_add_w₁ (f : M₄ →ₗ[ℂ] ℂ) (w₁ w₁' : M₁) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν f (w₁ + w₁') w₂ w₃ N₄ s = QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s
      + QT Y₁ Y₂ c ν f w₁' w₂ w₃ N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_smul_w₁ (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν f (a • w₁) w₂ w₃ N₄ s = a • QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_zero_w₁ (f : M₄ →ₗ[ℂ] ℂ) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν f (0 : M₁) w₂ w₃ N₄ s = 0 := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_add_w₂ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ w₂' : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν f w₁ (w₂ + w₂') w₃ N₄ s = QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s
      + QT Y₁ Y₂ c ν f w₁ w₂' w₃ N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_smul_w₂ (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν f w₁ (a • w₂) w₃ N₄ s = a • QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_zero_w₂ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₃ : M₃) :
    QT Y₁ Y₂ c ν f w₁ (0 : M₂) w₃ N₄ s = 0 := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_add_w₃ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ w₃' : M₃) :
    QT Y₁ Y₂ c ν f w₁ w₂ (w₃ + w₃') N₄ s = QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s
      + QT Y₁ Y₂ c ν f w₁ w₂ w₃' N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_smul_w₃ (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QT Y₁ Y₂ c ν f w₁ w₂ (a • w₃) N₄ s = a • QT Y₁ Y₂ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QT, coeff_prodQ]

theorem QT_zero_w₃ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) :
    QT Y₁ Y₂ c ν f w₁ w₂ (0 : M₃) N₄ s = 0 := by
  ext n; simp [QT, coeff_prodQ]

end Linear

/-- `QT` only sees the functional on the weight space `h₄ + N₄`. -/
theorem QT_congr_f {h₁ h₂ h₃ h₄ ν : ℂ} (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂}
    {w₃ : M₃} (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) {f f' : M₄ →ₗ[ℂ] ℂ}
    (hff : f.domRestrict (A₄.weight (h₄ + N₄)) = f'.domRestrict (A₄.weight (h₄ + N₄))) :
    QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
      = QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f' w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) := by
  ext n
  rw [QT, QT, coeff_prodQ, coeff_prodQ]
  have hx := prod_mem_weight hY₁ hY₂ hw₁ hw₂ hw₃
    (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n) (ν + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) - n)
  have e : h₁ + N₁ + (h₂ + N₂) + (h₃ + N₃) - (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n)
      - (ν + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) - n) - 2 = h₄ + N₄ := by push_cast; ring
  rw [e] at hx
  exact LinearMap.congr_fun hff ⟨_, hx⟩


end Product
end VOA.Huang.LogHuangODEProduct
