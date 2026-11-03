/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocTarget

/-!
# The commutator identity for products of intertwiners

The transfer of identities to expansion coefficients (`AssocCoeffRules`) needs the identities
expressing the
action of `v ∈ V` on the *outside* vectors `f, w₃` of a product
`⟨f, 𝒴₁(w₁, z₁) 𝒴₂(w₂, z₂) w₃⟩` through actions on the *inside* vectors `w₁, w₂`.  In the
Huang–Lepowsky orientation (functionals on `P₁ ⊗ P₂` indexed by `(f, w₃)`) this is what makes the
`P(z₀)`-action on the coefficient functionals lower-truncated and computable.

The identity, for `v ∈ V`, `m ∈ ℤ`, `|z₁| > |z₂| > 0`:
`⟨f∘v_m, 𝒴₁𝒴₂w₃⟩ = ⟨f, 𝒴₁𝒴₂ v_m w₃⟩ + Σᵢ C(m,i) z₁^{m−i} ⟨f, 𝒴₁(vᵢw₁)𝒴₂ w₃⟩
  + Σᵢ C(m,i) z₂^{m−i} ⟨f, 𝒴₁ 𝒴₂(vᵢw₂) w₃⟩`
(finite in `i`), proved here coefficientwise (from the commutator formula of both intertwiners)
and then for the convergent values.

To make index shifts harmless the values are summed over **all** `k ∈ ℤ` (`prodValueZ`); on a
base they agree with the library's `prodValue` (`prodValueZ_eq_prodValue`), and they are invariant
under integer shifts of the base (`prodValueZ_shift`).

## Main results
* `prodTermZ`, `prodValueZ`, `prodValueZ_shift`, `summable_prodTermZ_shift_iff`,
  `prodValueZ_eq_prodValue`, `summable_prodTermZ_of_base`.
* `prodCoeff_commutator` (coefficientwise identity, any intertwiners, any modules).
* `prodTermZ_commutator`, `prodValueZ_commutator` (values, given summability).
* `summable_prodTermZ_holds` (every integer-shifted canonical coset converges);
  `prodValueZ_commutator_holds`: the identity for homogeneous vectors of irreducible modules
  of a strongly rational `V`, with all summability discharged (canonical cosets).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.AssocCommutator

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-! ## Values summed over `ℤ` -/

/-- The `k`-th term (`k ∈ ℤ`) of the product on the line `n₁ + n₂ = S`, coset `ν − ℤ`. -/
noncomputable def prodTermZ (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν z₁ z₂ : ℂ) (k : ℤ) : ℂ :=
  prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (S - ν + k) (ν - k) * z₁ ^ (-(S - ν + k) - 1) * z₂ ^ (-(ν - k) - 1)

/-- The product value summed over all `k ∈ ℤ`. -/
noncomputable def prodValueZ (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν z₁ z₂ : ℂ) : ℂ :=
  ∑' k : ℤ, prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ k

theorem prodTermZ_shift (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν z₁ z₂ : ℂ) (d k : ℤ) :
    prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S (ν + d) z₁ z₂ (k + d)
      = prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ k := by
  unfold prodTermZ
  push_cast
  ring_nf

/-- Integer shifts of the base do not change the value. -/
theorem prodValueZ_shift (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν z₁ z₂ : ℂ) (d : ℤ) :
    prodValueZ Y₁ Y₂ f w₁ w₂ w₃ S (ν + d) z₁ z₂ = prodValueZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ := by
  unfold prodValueZ
  rw [← (Equiv.addRight d).tsum_eq]
  exact tsum_congr fun k => prodTermZ_shift Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ d k

theorem summable_prodTermZ_shift_iff (Y₁ : IntertwiningModes M₁ M₅ M₄)
    (Y₂ : IntertwiningModes M₂ M₃ M₅) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (S ν z₁ z₂ : ℂ) (d : ℤ) :
    Summable (prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S (ν + d) z₁ z₂)
      ↔ Summable (prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂) := by
  rw [← (Equiv.addRight d).summable_iff]
  have : (prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S (ν + d) z₁ z₂ ∘ (Equiv.addRight d))
      = prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ :=
    funext fun k => prodTermZ_shift Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ d k
  rw [this]

/-- On a base `ν`, the terms with `k < 0` vanish. -/
theorem prodTermZ_neg_of_base {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) {w₂ : M₂} {w₃ : M₃}
    {S ν : ℂ} (z₁ z₂ : ℂ) (hb : IsBase Y₂ w₂ w₃ ν) {k : ℤ} (hk : k < 0) :
    prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ k = 0 := by
  have hj := hb (-k - 1).toNat
  have e : ν + (((-k - 1).toNat : ℕ) + 1 : ℂ) = ν - k := by
    have : (((-k - 1).toNat : ℕ) : ℤ) = -k - 1 := Int.toNat_of_nonneg (by omega)
    have : (((-k - 1).toNat : ℕ) : ℂ) = ((-k - 1 : ℤ) : ℂ) := by exact_mod_cast this
    rw [this]; push_cast; ring
  rw [e] at hj
  simp [prodTermZ, prodCoeff, hj]

theorem support_prodTermZ_subset {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) {w₂ : M₂} {w₃ : M₃}
    {S ν : ℂ} (z₁ z₂ : ℂ) (hb : IsBase Y₂ w₂ w₃ ν) :
    Function.support (prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂) ⊆ Set.range (Nat.cast : ℕ → ℤ) := by
  intro k hk
  by_contra hn
  apply hk
  refine prodTermZ_neg_of_base f w₁ z₁ z₂ hb ?_
  by_contra hk0
  exact hn ⟨k.toNat, Int.toNat_of_nonneg (by omega)⟩

/-- On a base, `prodValueZ` is the library's `prodValue`. -/
theorem prodValueZ_eq_prodValue {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) {w₂ : M₂} {w₃ : M₃}
    {S ν : ℂ} (z₁ z₂ : ℂ) (hb : IsBase Y₂ w₂ w₃ ν) :
    prodValueZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ = prodValue Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂ := by
  unfold prodValueZ prodValue
  rw [← Nat.cast_injective.tsum_eq (support_prodTermZ_subset f w₁ z₁ z₂ hb)]
  rfl

theorem summable_prodTermZ_of_base {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) {w₂ : M₂} {w₃ : M₃}
    {S ν : ℂ} (z₁ z₂ : ℂ) (hb : IsBase Y₂ w₂ w₃ ν)
    (h : Summable fun k : ℕ => prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (S - ν + k) (ν - k)
        * z₁ ^ (-(S - ν + k) - 1) * z₂ ^ (-(ν - k) - 1)) :
    Summable (prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂) := by
  rw [← Nat.cast_injective.summable_iff (fun k hk => by
    by_contra hne
    exact hk (support_prodTermZ_subset f w₁ z₁ z₂ hb hne))]
  exact h

/-! ## The coefficientwise commutator identity -/

section Commutator

variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}

/-- A truncation bound for the commutator sums: all `vᵢ w` vanish for `i ≥ N`. -/
theorem finsum_eq_sum_Ico {X : Type*} [AddCommMonoid X] {g : ℤ → X} {N : ℤ}
    (hneg : ∀ i < 0, g i = 0)
    (hbig : ∀ i, N ≤ i → g i = 0) : ∑ᶠ i : ℤ, g i = ∑ i ∈ Finset.Ico 0 N, g i := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_Ico, Set.mem_Ico]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hi (hneg i (by omega))
  · by_contra h; exact hi (hbig i (by omega))

/-- **The commutator identity, coefficientwise.**
`⟨f∘v_m, (w₁)_{n₁}(w₂)_{n₂}w₃⟩ = ⟨f, (w₁)_{n₁}(w₂)_{n₂} v_m w₃⟩
  + Σᵢ C(m,i) ⟨f, (vᵢw₁)_{m+n₁−i}(w₂)_{n₂}w₃⟩ + Σᵢ C(m,i) ⟨f, (w₁)_{n₁}(vᵢw₂)_{m+n₂−i}w₃⟩`,
the sums over `0 ≤ i < N` for any `N` past the truncation of `v` on `w₁` and `w₂`. -/
theorem prodCoeff_commutator {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (v : 𝒱) (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {N : ℤ} (hN₁ : ∀ i, N ≤ i → mode (A₁.YM v) i w₁ = 0)
    (hN₂ : ∀ i, N ≤ i → mode (A₂.YM v) i w₂ = 0) (n₁ n₂ : ℂ) :
    prodCoeff Y₁ Y₂ (f ∘ₗ mode (A₄.YM v) m) w₁ w₂ w₃ n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ (mode (A₃.YM v) m w₃) n₁ n₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i
            * prodCoeff Y₁ Y₂ f (mode (A₁.YM v) i w₁) w₂ w₃ (m + n₁ - i) n₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i
            * prodCoeff Y₁ Y₂ f w₁ (mode (A₂.YM v) i w₂) w₃ n₁ (m + n₂ - i) := by
  have c₁ := hY₁.commutator v w₁ (Y₂ n₂ w₂ w₃) m n₁
  have c₂ := hY₂.commutator v w₂ w₃ m n₂
  rw [finsum_eq_sum_Ico (N := N) (fun i hi => by simp [cbz_apply_neg m hi])
    (fun i hi => by rw [hN₁ i hi, map_zero, LinearMap.zero_apply, smul_zero])] at c₁
  rw [finsum_eq_sum_Ico (N := N) (fun i hi => by simp [cbz_apply_neg m hi])
    (fun i hi => by rw [hN₂ i hi, map_zero, LinearMap.zero_apply, smul_zero])] at c₂
  have e₁ := congrArg f c₁
  have e₂ := congrArg (fun q => f (Y₁ n₁ w₁ q)) c₂
  simp only [map_sub, map_sum, map_smul, smul_eq_mul] at e₁ e₂
  simp only [prodCoeff, LinearMap.comp_apply]
  linear_combination e₁ + e₂

end Commutator

/-! ## The identity for values -/

section Values

variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}

theorem cpow_shift {z : ℂ} (hz : z ≠ 0) (a : ℂ) (d : ℤ) :
    z ^ (-(a + d) - 1) * z ^ (d : ℂ) = z ^ (-a - 1) := by
  rw [← Complex.cpow_add _ _ hz]; congr 1; ring

/-- The commutator identity term by term. -/
theorem prodTermZ_commutator {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (v : 𝒱) (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
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
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (v : 𝒱) (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
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

end Values

/-! ## Summability discharged (strongly rational `V`) -/

section Holds

/-- **Every integer-shifted canonical coset is summable** (irreducible modules, strongly
rational `V`, `0 < ‖z₂‖ < ‖z₁‖`). -/
theorem summable_prodTermZ_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {S ν : ℂ} (hS : S = α₁ + α₂ + α₃ - h₄ - 2) (d : ℤ) (hν : ν = α₂ + α₃ - 1 - Q.h + d)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    Summable (prodTermZ Y₁ Y₂ f w₁ w₂ w₃ S ν z₁ z₂) := by
  subst hS hν
  exact (summable_prodTermZ_shift_iff _ _ _ _ _ _ _ _ _ _ d).2
    (summable_prodTermZ_of_base f w₁ z₁ z₂ (isBase_canonical Q hY₂ h₂ h₃)
      (summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf hz₂ hz))

/-- **The commutator identity for values**, all summability discharged: irreducible
modules of a strongly rational `V`, homogeneous `v ∈ V_β`, `wᵢ ∈ Pᵢ(αᵢ)`, `f` supported at `h₄`,
`0 < ‖z₂‖ < ‖z₁‖`.  The left side lives on the line `S = σ + β − m − 1` (the canonical line of
`f ∘ v_m`); every term is on its own canonical line and an integer shift of its canonical base. -/
theorem prodValueZ_commutator_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β) (m : ℤ)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    ∃ N : ℤ,
    prodValueZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM v) m) w₁ w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h) z₁ z₂
      = prodValueZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM v) m w₃)
          (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h) z₁ z₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * z₁ ^ ((m - i : ℤ) : ℂ)
            * prodValueZ Y₁ Y₂ f (mode (P₁.isMod.YM v) i w₁) w₂ w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ)) (α₂ + α₃ - 1 - Q.h) z₁ z₂
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * z₂ ^ ((m - i : ℤ) : ℂ)
            * prodValueZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM v) i w₂) w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ))
                (α₂ + α₃ - 1 - Q.h + (m - i : ℤ)) z₁ z₂ := by
  obtain ⟨N₁, hN₁⟩ := P₁.isMod.truncation v w₁
  obtain ⟨N₂, hN₂⟩ := P₂.isMod.truncation v w₂
  have hz₁ : z₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact absurd hz (not_lt.mpr (norm_nonneg _))
  refine ⟨max N₁ N₂, prodValueZ_commutator hY₁ hY₂ v m f w₁ w₂ w₃
    (fun i hi => hN₁ i (le_of_max_le_left hi)) (fun i hi => hN₂ i (le_of_max_le_right hi))
    _ _ hz₁ hz₂ ?_ ?_ ?_⟩
  · exact summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hv h₃ m) hf (by ring) (m + 1 - β)
      (by push_cast; ring) hz₂ hz
  · intro i _
    exact summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂
      (VOA.mode_mem_weight P₁.isMod hv h₁ i) h₂ h₃ hf (by push_cast; ring) 0
      (by push_cast; ring) hz₂ hz
  · intro i _
    exact summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁
      (VOA.mode_mem_weight P₂.isMod hv h₂ i) h₃ hf (by push_cast; ring) (m + 1 - β)
      (by push_cast; ring) hz₂ hz

end Holds

end VOA.Huang.AssocCommutator
