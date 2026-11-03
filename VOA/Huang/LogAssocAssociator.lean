import VOA.Huang.LogAssocJacobi

/-! Both actual associator forms of the product Jacobi identity, for
arbitrary weak modules and hence every genuine logarithmic coefficient.
Geometric resummation retains its actual convergent integer mode coset. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocAssociator
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.MatrixCoeff
open VOA.Huang.AssocCommutator (prodTermZ prodValueZ cpow_shift)
open VOA.Huang.AssocAssociator (finsum_eq_sum_range sum_range_eq_of_vanish
  hasSum_assocCoeff hasSum_assocCoeff_right tsum_conv cbz_swap cbz_trinomial
  hasSum_cbz_pow prod_range_falling_add)
open VOA.Huang.LogHuangODEModes (jacobi_commutator)
open scoped BigOperators
universe u
section Coeff

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {A₄ : WeakModule W M₄} {A₅ : WeakModule W M₅}

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
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
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
    have c := jacobi_commutator hY₂ u w₂ w₃ i n₂
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
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
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
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
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
    have c := jacobi_commutator hY₁ u w₁ (Y₂ (n₂ + i) w₂ w₃) (ℓ - i) n
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
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsJacobiFamily A₂ A₃ A₅ Y₂) (u : 𝒱) (ℓ : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
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
end VOA.Huang.LogAssocAssociator
