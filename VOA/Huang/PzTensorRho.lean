/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Translation
import VOA.Foundations.IotaZExpansion

/-!
# The transposed coproduct on honest bilinear forms

For two weak `V`-modules `M₁, M₂` (the insertion points `1` and `0`) and a bilinear form
`β : M₁ × M₂ → ℂ` (an element of `(M₁ ⊗ M₂)*`), the **transposed `w₂`-centred coproduct** is

`ρ(a,p) β (y₁, y₂) = β(y₁, a_p y₂) + Σ_{r ≥ 0} C(p,r) β(a_r y₁, y₂)`,

the transpose of `Δ(a_p) = 1 ⊗ a_p + Σ_r C(p,r) a_r ⊗ 1` (the residue of `x^p Y(a,x)` around the
two points `0` and `1`).  This is `PzTensorAction.copT` without the homogeneous-pair bookkeeping:
here `ρ(a,p)` is defined for every state and every bilinear form, it is linear in both, and it is
translation covariant.

The **compatibility slices** `Out = InL + InR` (`SliceAt a m L`) are the coefficient form of
the residue theorem for `x^m (x−1)^L` on the sphere with the three points `0, 1, ∞`:

`Σ_k (−1)^k C(L,k) ρ(a, m+L−k) β`
`  = Σ_r C(m,r) β(a_{L+r} ·, ·) + Σ_j C(L,j)(−1)^{L−j} β(·, a_{m+j} ·)`.

For `L = 0` it is the definition of `ρ` (`slice_L_zero`); for `m = 0` it is the HLZ `P(1)`-
compatibility condition.  `slice_holds`: a lower-truncated form satisfying the `m = 0` slices
satisfies **all** slices (the two families are related by the Pascal recurrence
`S(m+1, L) = S(m, L+1) + S(m, L)` on all three sides).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorRho

open VOA
open Module (End)
open scoped BigOperators

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v} [AddCommGroup M₁] [Module ℂ M₁]
variable {M₂ : Type w} [AddCommGroup M₂] [Module ℂ M₂]

/-! ## Finite-support bookkeeping for `ℤ`-indexed sums -/

/-- A family vanishing outside `[lo, hi]` has finite support. -/
theorem fin_of_bound {X : Type*} [Zero X] (f : ℤ → X) (lo hi : ℤ)
    (h : ∀ i, f i ≠ 0 → lo ≤ i ∧ i ≤ hi) : (Function.support f).Finite :=
  (Set.finite_Icc lo hi).subset fun i hi' => h i hi'

/-- A finsum over `ℤ` as a finite sum over a box containing the support. -/
theorem finsum_eq_Icc {X : Type*} [AddCommMonoid X] (f : ℤ → X) (lo hi : ℤ)
    (h : ∀ i, f i ≠ 0 → lo ≤ i ∧ i ≤ hi) : ∑ᶠ i, f i = ∑ i ∈ Finset.Icc lo hi, f i := by
  apply finsum_eq_sum_of_support_subset
  intro i hi'
  simpa using h i hi'

/-- Shift of a finsum over `ℤ`. -/
theorem finsum_shift {X : Type*} [AddCommMonoid X] (f : ℤ → X) (c : ℤ) :
    ∑ᶠ i, f (i + c) = ∑ᶠ i, f i :=
  finsum_comp_equiv (Equiv.addRight c)

/-- `cbz` vanishes on negative lower index (restated). -/
theorem cbz_neg {n k : ℤ} (hk : k < 0) : cbz n k = 0 := cbz_apply_neg n hk

/-! ## The translated modes `E(a,p) = Σ_r C(p,r) a_r` on `M₁` -/

section Emode

variable (A₁ : WeakModule W M₁)

theorem mode_eventually_zero (a : 𝒱) (y : M₁) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (A₁.YM a) n y = 0 := A₁.truncation a y

theorem cbz_mode_support (a : 𝒱) (p : ℤ) (y : M₁) :
    (Function.support fun r : ℤ => cbz p r • mode (A₁.YM a) r y).Finite := by
  obtain ⟨N, hN⟩ := A₁.truncation a y
  refine fin_of_bound _ 0 N fun r hr => ⟨?_, ?_⟩
  · by_contra h; exact hr (by rw [cbz_neg (by omega), zero_smul])
  · by_contra h; exact hr (by rw [hN r (by omega), smul_zero])

/-- The translated mode `E(a,p) y = Σ_r C(p,r) a_r y` (finite sum). -/
noncomputable def Emode (a : 𝒱) (p : ℤ) : M₁ →ₗ[ℂ] M₁ where
  toFun y := ∑ᶠ r : ℤ, cbz p r • mode (A₁.YM a) r y
  map_add' y y' := by
    rw [← finsum_add_distrib (cbz_mode_support A₁ a p y) (cbz_mode_support A₁ a p y')]
    exact finsum_congr fun r => by rw [map_add, smul_add]
  map_smul' c y := by
    rw [RingHom.id_apply, smul_finsum' c (cbz_mode_support A₁ a p y)]
    exact finsum_congr fun r => by rw [map_smul, smul_comm]

theorem Emode_apply (a : 𝒱) (p : ℤ) (y : M₁) :
    Emode A₁ a p y = ∑ᶠ r : ℤ, cbz p r • mode (A₁.YM a) r y := rfl

end Emode

/-! ## The transposed coproduct `ρ(a,p)` on bilinear forms -/

section Rho

variable (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)

/-- **The transposed coproduct** `ρ(a,p)β = β(·, a_p ·) + β(E(a,p) ·, ·)`. -/
noncomputable def rhoL (a : 𝒱) (p : ℤ) :
    (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) →ₗ[ℂ] (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) where
  toFun β := β.compl₂ (mode (A₂.YM a) p) + β ∘ₗ Emode A₁ a p
  map_add' β β' := by
    ext y₁ y₂
    simp only [LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply]
    ring
  map_smul' c β := by
    ext y₁ y₂
    simp only [LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- Pairing a bilinear form with the translated modes. -/
theorem bil_Emode (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (a : 𝒱) (p : ℤ) (y₁ : M₁) (y₂ : M₂) :
    β (Emode A₁ a p y₁) y₂ = ∑ᶠ r : ℤ, cbz p r * β (mode (A₁.YM a) r y₁) y₂ := by
  rw [Emode_apply]
  have := map_finsum (β.flip y₂) (cbz_mode_support A₁ a p y₁)
  simp only [LinearMap.flip_apply, map_smul, smul_eq_mul] at this
  exact this

theorem rhoL_apply (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (a : 𝒱) (p : ℤ) (y₁ : M₁) (y₂ : M₂) :
    rhoL A₁ A₂ a p β y₁ y₂
      = β y₁ (mode (A₂.YM a) p y₂) + ∑ᶠ r : ℤ, cbz p r * β (mode (A₁.YM a) r y₁) y₂ := by
  change (β.compl₂ (mode (A₂.YM a) p) + β ∘ₗ Emode A₁ a p) y₁ y₂ = _
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
    bil_Emode]

/-- The `M₁`-sum of `ρ` as a finite sum over `[0, N)` once `a_r y₁ = 0` for `r ≥ N`. -/
theorem left_sum_eq_Icc (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (a : 𝒱) (p : ℤ) (y₁ : M₁) (y₂ : M₂)
    {N : ℤ} (hN : ∀ n : ℤ, N ≤ n → mode (A₁.YM a) n y₁ = 0) :
    ∑ᶠ r : ℤ, cbz p r * β (mode (A₁.YM a) r y₁) y₂
      = ∑ r ∈ Finset.Icc 0 N, cbz p r * β (mode (A₁.YM a) r y₁) y₂ := by
  apply finsum_eq_Icc
  intro r hr
  refine ⟨?_, ?_⟩
  · by_contra h; exact hr (by rw [cbz_neg (by omega), zero_mul])
  · by_contra h; exact hr (by rw [hN r (by omega), map_zero, LinearMap.zero_apply, mul_zero])

/-- Support finiteness of the `M₁`-sum. -/
theorem left_sum_fin (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (a : 𝒱) (p : ℤ) (y₁ : M₁) (y₂ : M₂) :
    (Function.support fun r : ℤ => cbz p r * β (mode (A₁.YM a) r y₁) y₂).Finite := by
  obtain ⟨N, hN⟩ := A₁.truncation a y₁
  refine fin_of_bound _ 0 N fun r hr => ⟨?_, ?_⟩
  · by_contra h; exact hr (by rw [cbz_neg (by omega), zero_mul])
  · by_contra h; exact hr (by rw [hN r (by omega), map_zero, LinearMap.zero_apply, mul_zero])

/-! ### Linearity in the state -/

theorem rhoL_add_state (a a' : 𝒱) (p : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    rhoL A₁ A₂ (a + a') p β y₁ y₂ = rhoL A₁ A₂ a p β y₁ y₂ + rhoL A₁ A₂ a' p β y₁ y₂ := by
  rw [rhoL_apply, rhoL_apply, rhoL_apply]
  simp only [map_add, mode_add, LinearMap.add_apply]
  rw [finsum_congr (fun r => show cbz p r * (β (mode (A₁.YM a) r y₁) y₂
        + β (mode (A₁.YM a') r y₁) y₂)
      = cbz p r * β (mode (A₁.YM a) r y₁) y₂ + cbz p r * β (mode (A₁.YM a') r y₁) y₂ by ring),
    finsum_add_distrib (left_sum_fin A₁ β a p y₁ y₂) (left_sum_fin A₁ β a' p y₁ y₂)]
  ring

theorem rhoL_smul_state (c : ℂ) (a : 𝒱) (p : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁)
    (y₂ : M₂) : rhoL A₁ A₂ (c • a) p β y₁ y₂ = c * rhoL A₁ A₂ a p β y₁ y₂ := by
  rw [rhoL_apply, rhoL_apply]
  simp only [map_smul, mode_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [mul_add, mul_finsum]
  congr 1
  exact finsum_congr fun r => by ring

/-- `ρ(·, p)β(y₁, y₂)` as a linear functional on the states. -/
noncomputable def rhoState (p : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    𝒱 →ₗ[ℂ] ℂ where
  toFun a := rhoL A₁ A₂ a p β y₁ y₂
  map_add' a a' := rhoL_add_state A₁ A₂ a a' p β y₁ y₂
  map_smul' c a := rhoL_smul_state A₁ A₂ c a p β y₁ y₂

@[simp] theorem rhoState_apply (p : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) (a : 𝒱) :
    rhoState A₁ A₂ p β y₁ y₂ a = rhoL A₁ A₂ a p β y₁ y₂ := rfl

theorem rhoL_zero_state (p : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) : rhoL A₁ A₂ 0 p β = 0 := by
  ext y₁ y₂
  have := (rhoState A₁ A₂ p β y₁ y₂).map_zero
  simpa using this

/-! ### Translation covariance -/

/-- Absorption: `(r+1)·C(n,r+1) = n·C(n−1,r)`. -/
theorem cbz_succ_absorb' (n : ℤ) (r : ℕ) :
    ((r : ℂ) + 1) * cbz n ((r : ℤ) + 1) = (n : ℂ) * cbz (n - 1) r := by
  rw [show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) from by push_cast; ring,
    cbz_apply_nonneg _ (by positivity), cbz_apply_nonneg _ (by positivity),
    Int.toNat_natCast, Int.toNat_natCast]
  have hfac : ((r.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have h1 := gBinom_mul_factorial n (r + 1)
  have h2 := gBinom_mul_factorial (n - 1) r
  rw [Finset.prod_range_succ'] at h1
  have hprod : (∏ i ∈ Finset.range r, ((n : ℂ) - ((i + 1 : ℕ) : ℂ)))
      = ∏ i ∈ Finset.range r, (((n - 1 : ℤ) : ℂ) - (i : ℂ)) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    push_cast; ring
  rw [hprod, ← h2, Nat.factorial_succ] at h1
  push_cast at h1
  refine mul_left_cancel₀ hfac ?_
  linear_combination h1

/-- Absorption `C(p,r)·r = p·C(p−1,r−1)` for all integers. -/
theorem cbz_absorb (p r : ℤ) : cbz p r * (r : ℂ) = (p : ℂ) * cbz (p - 1) (r - 1) := by
  rcases lt_or_ge r 1 with hr | hr
  · rcases lt_or_ge r 0 with hr' | hr'
    · rw [cbz_neg hr', zero_mul, cbz_neg (by omega), mul_zero]
    · have : r = 0 := by omega
      subst this
      rw [cbz_neg (by omega : (0:ℤ) - 1 < 0)]; simp
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = (s : ℤ) + 1 := ⟨(r - 1).toNat, by omega⟩
    have h := cbz_succ_absorb' p s
    rw [show ((s : ℤ) + 1 - 1) = (s : ℤ) by ring]
    push_cast
    rw [← h]
    ring

theorem rhoL_translation (a : 𝒱) (p : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    rhoL A₁ A₂ (W.L (-1) a) p β y₁ y₂ = -(p : ℂ) * rhoL A₁ A₂ a (p - 1) β y₁ y₂ := by
  rw [rhoL_apply, rhoL_apply]
  have h2 := act_T_covariance A₂ a p y₂
  simp only [WeakModule.act_def] at h2
  rw [h2, LinearMap.map_smul, smul_eq_mul]
  have hL : ∀ r : ℤ, cbz p r * β (mode (A₁.YM (W.L (-1) a)) r y₁) y₂
      = -(p : ℂ) * (cbz (p - 1) (r - 1) * β (mode (A₁.YM a) (r - 1) y₁) y₂) := by
    intro r
    have h1 := act_T_covariance A₁ a r y₁
    simp only [WeakModule.act_def] at h1
    rw [h1, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have := cbz_absorb p r
    linear_combination (-(β (mode (A₁.YM a) (r - 1) y₁) y₂)) * this
  have hs : ∑ᶠ r : ℤ, cbz (p - 1) (r - 1) * β (mode (A₁.YM a) (r - 1) y₁) y₂
      = ∑ᶠ r : ℤ, cbz (p - 1) r * β (mode (A₁.YM a) r y₁) y₂ := by
    have := finsum_shift (fun r => cbz (p - 1) r * β (mode (A₁.YM a) r y₁) y₂) (-1)
    simpa [sub_eq_add_neg] using this
  rw [finsum_congr hL, ← mul_finsum, hs]
  ring

end Rho

/-! ## The compatibility slices -/

section Slices

variable (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)

/-- Lower truncation of `β` under `ρ(a, ·)`. -/
def TruncAt (a : 𝒱) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) : Prop :=
  ∃ P : ℤ, ∀ p : ℤ, p ≤ P → rhoL A₁ A₂ a p β = 0

/-- The outside side `Σ_k (−1)^k C(L,k) ρ(a, m+L−k)β` (the `∞`-expansion of `x^m(x−1)^L`). -/
noncomputable def Out (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) : ℂ :=
  ∑ᶠ k : ℤ, (negOnePow k * cbz L k) * rhoL A₁ A₂ a (m + L - k) β y₁ y₂

/-- The local side at the point `1`: `Σ_r C(m,r) β(a_{L+r} y₁, y₂)`. -/
noncomputable def InL (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) : ℂ :=
  ∑ᶠ r : ℤ, cbz m r * β (mode (A₁.YM a) (L + r) y₁) y₂

/-- The local side at the point `0`: `Σ_j C(L,j)(−1)^{L−j} β(y₁, a_{m+j} y₂)`. -/
noncomputable def InR (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) : ℂ :=
  ∑ᶠ j : ℤ, (cbz L j * negOnePow (L - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂)

/-- The slice defect. -/
noncomputable def Dsl (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) : ℂ :=
  Out A₁ A₂ a m L β y₁ y₂ - InL A₁ a m L β y₁ y₂ - InR A₂ a m L β y₁ y₂

theorem Out_fin {a : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (htr : TruncAt A₁ A₂ a β) (m L : ℤ)
    (y₁ : M₁) (y₂ : M₂) :
    (Function.support fun k : ℤ =>
      (negOnePow k * cbz L k) * rhoL A₁ A₂ a (m + L - k) β y₁ y₂).Finite := by
  obtain ⟨P, hP⟩ := htr
  refine fin_of_bound _ 0 (m + L - P) fun k hk => ⟨?_, ?_⟩
  · by_contra h; exact hk (by rw [cbz_neg (by omega), mul_zero, zero_mul])
  · by_contra h
    exact hk (by rw [hP _ (by omega), LinearMap.zero_apply, LinearMap.zero_apply, mul_zero])

theorem InL_fin (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    (Function.support fun r : ℤ => cbz m r * β (mode (A₁.YM a) (L + r) y₁) y₂).Finite := by
  obtain ⟨N, hN⟩ := A₁.truncation a y₁
  refine fin_of_bound _ 0 (N - L) fun r hr => ⟨?_, ?_⟩
  · by_contra h; exact hr (by rw [cbz_neg (by omega), zero_mul])
  · by_contra h; exact hr (by rw [hN _ (by omega), map_zero, LinearMap.zero_apply, mul_zero])

theorem InR_fin (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    (Function.support fun j : ℤ =>
      (cbz L j * negOnePow (L - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂)).Finite := by
  obtain ⟨N, hN⟩ := A₂.truncation a y₂
  refine fin_of_bound _ 0 (N - m) fun j hj => ⟨?_, ?_⟩
  · by_contra h; exact hj (by rw [cbz_neg (by omega), zero_mul, zero_mul])
  · by_contra h; exact hj (by rw [hN _ (by omega), map_zero, mul_zero])

/-! ### Pascal recurrences -/

theorem Out_rec {a : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (htr : TruncAt A₁ A₂ a β) (m L : ℤ)
    (y₁ : M₁) (y₂ : M₂) :
    Out A₁ A₂ a (m + 1) L β y₁ y₂ = Out A₁ A₂ a m (L + 1) β y₁ y₂ + Out A₁ A₂ a m L β y₁ y₂ := by
  -- expand `Out m (L+1)` by Pascal in the upper index
  have hsplit : Out A₁ A₂ a m (L + 1) β y₁ y₂
      = Out A₁ A₂ a (m + 1) L β y₁ y₂
        + ∑ᶠ k : ℤ, (negOnePow k * cbz L (k - 1)) * rhoL A₁ A₂ a (m + 1 + L - k) β y₁ y₂ := by
    unfold Out
    have h2 : (Function.support fun k : ℤ =>
        (negOnePow k * cbz L (k - 1)) * rhoL A₁ A₂ a (m + 1 + L - k) β y₁ y₂).Finite := by
      have := (Out_fin A₁ A₂ htr m L y₁ y₂).image (fun k => k + 1)
      refine this.subset fun k hk => ⟨k - 1, ?_, by ring⟩
      simp only [Function.mem_support] at hk ⊢
      rw [show m + L - (k - 1) = m + 1 + L - k by ring, negOnePow_pred]
      intro h; apply hk; linear_combination -h
    rw [← finsum_add_distrib (by
        have := Out_fin A₁ A₂ htr (m + 1) L y₁ y₂
        exact this) h2]
    refine finsum_congr fun k => ?_
    rw [cbz_pascal_up, show m + (L + 1) - k = m + 1 + L - k by ring]
    ring
  have hshift : ∑ᶠ k : ℤ, (negOnePow k * cbz L (k - 1)) * rhoL A₁ A₂ a (m + 1 + L - k) β y₁ y₂
      = - Out A₁ A₂ a m L β y₁ y₂ := by
    unfold Out
    rw [← finsum_shift _ 1, ← neg_one_mul, mul_finsum]
    refine finsum_congr fun k => ?_
    rw [show k + 1 - 1 = k by ring, show m + 1 + L - (k + 1) = m + L - k by ring, negOnePow_succ]
    ring
  rw [hsplit, hshift]
  ring

theorem InL_rec (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    InL A₁ a (m + 1) L β y₁ y₂ = InL A₁ a m (L + 1) β y₁ y₂ + InL A₁ a m L β y₁ y₂ := by
  unfold InL
  have h2 : (Function.support fun r : ℤ =>
      cbz m (r - 1) * β (mode (A₁.YM a) (L + r) y₁) y₂).Finite := by
    have := (InL_fin A₁ a m (L + 1) β y₁ y₂).image (fun r => r + 1)
    refine this.subset fun r hr => ⟨r - 1, ?_, by ring⟩
    simp only [Function.mem_support] at hr ⊢
    rwa [show L + 1 + (r - 1) = L + r by ring]
  rw [finsum_congr (fun r => show cbz (m + 1) r * β (mode (A₁.YM a) (L + r) y₁) y₂
      = cbz m r * β (mode (A₁.YM a) (L + r) y₁) y₂
        + cbz m (r - 1) * β (mode (A₁.YM a) (L + r) y₁) y₂ by rw [cbz_pascal_up]; ring),
    finsum_add_distrib (InL_fin A₁ a m L β y₁ y₂) h2, add_comm]
  congr 1
  rw [← finsum_shift _ 1]
  exact finsum_congr fun r => by
    rw [show r + 1 - 1 = r by ring, show L + (r + 1) = L + 1 + r by ring]

theorem InR_rec (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    InR A₂ a (m + 1) L β y₁ y₂ = InR A₂ a m (L + 1) β y₁ y₂ + InR A₂ a m L β y₁ y₂ := by
  have hsplit : InR A₂ a m (L + 1) β y₁ y₂
      = - InR A₂ a m L β y₁ y₂
        + ∑ᶠ j : ℤ, (cbz L (j - 1) * negOnePow (L + 1 - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂) := by
    unfold InR
    have h1 : (Function.support fun j : ℤ =>
        (cbz L j * negOnePow (L + 1 - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂)).Finite := by
      refine (InR_fin A₂ a m L β y₁ y₂).subset fun j hj => ?_
      simp only [Function.mem_support] at hj ⊢
      rw [show L + 1 - j = (L - j) + 1 by ring, negOnePow_succ] at hj
      intro h; apply hj; linear_combination -h
    have h2 : (Function.support fun j : ℤ =>
        (cbz L (j - 1) * negOnePow (L + 1 - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂)).Finite := by
      have := (InR_fin A₂ a (m + 1) L β y₁ y₂).image (fun j => j + 1)
      refine this.subset fun j hj => ⟨j - 1, ?_, by ring⟩
      simp only [Function.mem_support] at hj ⊢
      rwa [show L - (j - 1) = L + 1 - j by ring, show m + 1 + (j - 1) = m + j by ring]
    rw [finsum_congr (fun j => show (cbz (L + 1) j * negOnePow (L + 1 - j))
          * β y₁ (mode (A₂.YM a) (m + j) y₂)
        = (cbz L j * negOnePow (L + 1 - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂)
          + (cbz L (j - 1) * negOnePow (L + 1 - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂) by
        rw [cbz_pascal_up]; ring),
      finsum_add_distrib h1 h2]
    congr 1
    rw [← neg_one_mul, mul_finsum]
    refine finsum_congr fun j => ?_
    rw [show L + 1 - j = (L - j) + 1 by ring, negOnePow_succ]
    ring
  have hshift : ∑ᶠ j : ℤ, (cbz L (j - 1) * negOnePow (L + 1 - j))
      * β y₁ (mode (A₂.YM a) (m + j) y₂) = InR A₂ a (m + 1) L β y₁ y₂ := by
    unfold InR
    rw [← finsum_shift _ 1]
    refine finsum_congr fun j => ?_
    rw [show j + 1 - 1 = j by ring, show L + 1 - (j + 1) = L - j by ring,
      show m + (j + 1) = m + 1 + j by ring]
  rw [hsplit, hshift]
  ring

theorem Dsl_rec {a : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (htr : TruncAt A₁ A₂ a β) (m L : ℤ)
    (y₁ : M₁) (y₂ : M₂) :
    Dsl A₁ A₂ a (m + 1) L β y₁ y₂ = Dsl A₁ A₂ a m (L + 1) β y₁ y₂ + Dsl A₁ A₂ a m L β y₁ y₂ := by
  unfold Dsl
  rw [Out_rec A₁ A₂ htr, InL_rec, InR_rec]
  ring

/-- The `L = 0` slice is the definition of `ρ`. -/
theorem Dsl_L_zero (a : 𝒱) (m : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    Dsl A₁ A₂ a m 0 β y₁ y₂ = 0 := by
  unfold Dsl Out InL InR
  have h1 : ∑ᶠ k : ℤ, (negOnePow k * cbz 0 k) * rhoL A₁ A₂ a (m + 0 - k) β y₁ y₂
      = rhoL A₁ A₂ a m β y₁ y₂ := by
    rw [finsum_eq_single _ 0 (fun k hk => by rw [cbz_zero_left, if_neg hk]; ring)]
    simp [negOnePow]
  have h2 : ∑ᶠ j : ℤ, (cbz 0 j * negOnePow (0 - j)) * β y₁ (mode (A₂.YM a) (m + j) y₂)
      = β y₁ (mode (A₂.YM a) m y₂) := by
    rw [finsum_eq_single _ 0 (fun j hj => by rw [cbz_zero_left, if_neg hj]; ring)]
    simp [negOnePow]
  rw [h1, h2, rhoL_apply]
  simp only [zero_add]
  ring

/-- An abstract Pascal propagation: a function on `ℤ × ℤ` with `f(m+1,L) = f(m,L+1) + f(m,L)`,
vanishing on the line `m = 0` and on the line `L = 0`, vanishes identically. -/
theorem pascal_vanish (f : ℤ → ℤ → ℂ) (hrec : ∀ m L, f (m + 1) L = f m (L + 1) + f m L)
    (h0 : ∀ L, f 0 L = 0) (hL : ∀ m, f m 0 = 0) : ∀ m L, f m L = 0 := by
  have hpos : ∀ n : ℕ, ∀ L, f n L = 0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => intro L; push_cast; rw [hrec, ih, ih, add_zero]
  have hneg : ∀ n : ℕ, ∀ L, f (-(n : ℤ)) L = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have hstep : ∀ L, f (-((n + 1 : ℕ) : ℤ)) (L + 1) = - f (-((n + 1 : ℕ) : ℤ)) L := by
        intro L
        have := hrec (-((n + 1 : ℕ) : ℤ)) L
        rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, ih] at this
        linear_combination -this
      intro L
      induction L using Int.induction_on with
      | zero => exact hL _
      | succ k ihk => rw [hstep, ihk, neg_zero]
      | pred k ihk =>
        have := hstep (-(k : ℤ) - 1)
        rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ihk] at this
        linear_combination this
  intro m L
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    exact hpos n L
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨(-m).toNat, by omega⟩
    exact hneg n L

/-- The compatibility condition (the `m = 0` slices) for the state `a`. -/
def CompatAt (a : 𝒱) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ (L : ℤ) (y₁ : M₁) (y₂ : M₂), Dsl A₁ A₂ a 0 L β y₁ y₂ = 0

/-- **All slices from the `m = 0` slices.** -/
theorem slice_holds {a : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (htr : TruncAt A₁ A₂ a β)
    (hc : CompatAt A₁ A₂ a β) (m L : ℤ) (y₁ : M₁) (y₂ : M₂) :
    Out A₁ A₂ a m L β y₁ y₂ = InL A₁ a m L β y₁ y₂ + InR A₂ a m L β y₁ y₂ := by
  have := pascal_vanish (fun m L => Dsl A₁ A₂ a m L β y₁ y₂)
    (fun m L => Dsl_rec A₁ A₂ htr m L y₁ y₂) (fun L => hc L y₁ y₂)
    (fun m => Dsl_L_zero A₁ A₂ a m β y₁ y₂) m L
  simp only [Dsl] at this
  linear_combination this

end Slices

end VOA.Huang.PzTensorRho
