/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArOppModes
import VOA.Modules.LogTensorPzJacobiModes
import VOA.Huang.LiConverseExtract

/-! # Genuine opposite Jacobi for generalized logarithmic modules

The first module is an actual graded weak module, the other two are arbitrary
weak modules, and the original coefficient family has genuine Jacobi and
truncation. The finite L(1) comultiplication transports its actual Jacobi identity.
No ordinary L(0) action or logarithmic derivative is assumed.
-/
namespace VOA.LogTensor.Ar
open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiRegular
open scoped BigOperators
open Pz
universe u

section Summands
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

noncomputable def jacL (A₂ : WeakModule W M₂) (A₃ : WeakModule W M₃)
    (Y : IntertwiningModes M₁ M₂ M₃) (u : V) (x : M₁) (y : M₂) (ell m : ℤ)
    (n : ℂ) (i : ℤ) : M₃ :=
  (negOnePow i * cbz ell i) •
    (mode (A₃.YM u) (ell+m-i) (Y (n+i) x y) -
      negOnePow ell • Y (ell+n-i) x (mode (A₂.YM u) (m+i) y))
noncomputable def jacR (A₁ : WeakModule W M₁) (Y : IntertwiningModes M₁ M₂ M₃)
    (u : V) (x : M₁) (y : M₂) (ell m : ℤ) (n : ℂ) (i : ℤ) : M₃ :=
  cbz m i • Y (m+n-i) (mode (A₁.YM u) (ell+i) x) y

theorem jacL_support_finite {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
    {Y : IntertwiningModes M₁ M₂ M₃} (htr : ModeTruncated Y)
    (u : V) (x : M₁) (y : M₂) (ell m : ℤ) (n : ℂ) :
    (Function.support (jacL A₂ A₃ Y u x y ell m n)).Finite := by
  change (Function.support (IsLogIntertwining.jacL A₂ A₃ (liftModes Y) u x y ell m n 0)).Finite
  apply IsLogIntertwining.jacL_support_finite
  intro x y n
  obtain ⟨K,hK⟩ := htr x y n
  exact ⟨K,fun j hj _ => hK j hj⟩

theorem jacR_support_finite {A₁ : WeakModule W M₁}
    (Y : IntertwiningModes M₁ M₂ M₃) (u : V) (x : M₁) (y : M₂)
    (ell m : ℤ) (n : ℂ) : (Function.support (jacR A₁ Y u x y ell m n)).Finite :=
  IsLogIntertwining.jacR_support_finite (liftModes Y) u x y ell m n 0
end Summands

/-! ## The statePhase `e^{πiβ}` -/

/-- `e^{πiβ}`. -/
noncomputable def statePhase (β : ℂ) : ℂ := Complex.exp (↑Real.pi * Complex.I * β)

theorem statePhase_ne_zero (β : ℂ) : statePhase β ≠ 0 := Complex.exp_ne_zero _

theorem statePhase_add_int (β : ℂ) (k : ℤ) : statePhase (β + k) = (-1 : ℂ) ^ k * statePhase β := by
  rw [statePhase, statePhase, mul_add, Complex.exp_add, mul_comm (Complex.exp _)]
  congr 1
  rw [show ↑Real.pi * Complex.I * (k : ℂ) = k * (↑Real.pi * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem statePhase_add_one (β : ℂ) : statePhase (β + 1) = -statePhase β := by
  have h := statePhase_add_int β 1
  simpa using h

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

/-! ## The twisted modes -/

section Twist

variable (A₁ : C2Rigid.GWModule W M₁)

theorem L1w_pow_eventually (w : M₁) : ∃ J : ℕ, ∀ t, J ≤ t → (L1w A₁.toWeakModule ^ t) w = 0 := by
  obtain ⟨J, hJ⟩ := Contra.L1_locallyNilpotent A₁ w
  exact ⟨J, fun t ht => pow_apply_eq_zero_of_le hJ ht⟩

/-- The `t`-th term of the twisted modes. -/
noncomputable def twTerm (Y : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) (w : M₁) (t : ℕ) :
    M₂ →ₗ[ℂ] M₃ :=
  ((t.factorial : ℂ)⁻¹) • Y (2 * β - n - 2 - t) ((L1w A₁.toWeakModule ^ t) w)

theorem twTerm_support (Y : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) (w : M₁) {J : ℕ}
    (hJ : ∀ t, J ≤ t → (L1w A₁.toWeakModule ^ t) w = 0) :
    Function.support (twTerm A₁ Y β n w) ⊆ (Finset.range J : Set ℕ) := by
  intro t ht
  rw [Function.mem_support] at ht
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact ht (by rw [twTerm, hJ t (by omega), map_zero, smul_zero])

theorem twTerm_support_finite (Y : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) (w : M₁) :
    (Function.support (twTerm A₁ Y β n w)).Finite := by
  obtain ⟨J, hJ⟩ := L1w_pow_eventually A₁ w
  exact (Finset.range J).finite_toSet.subset (twTerm_support A₁ Y β n w hJ)

/-- **The twisted (opposite) intertwiner modes** with weight parameter `β`:
`twI Y β n w = e^{πiβ} Σ_t (t!)⁻¹ 𝒴_{2β−n−2−t}(L(1)ᵗ w)`. On `w ∈ (M₁)_β` this is FHL's
`𝒴°ₙ(w)`. -/
noncomputable def twI (Y : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃ where
  toFun w := statePhase β • ∑ᶠ t : ℕ, twTerm A₁ Y β n w t
  map_add' w w' := by
    rw [← smul_add, ← finsum_add_distrib (twTerm_support_finite A₁ Y β n w)
      (twTerm_support_finite A₁ Y β n w')]
    congr 1
    refine finsum_congr (fun t => ?_)
    simp only [twTerm, map_add, smul_add]
  map_smul' c w := by
    rw [RingHom.id_apply, smul_comm c (statePhase β), smul_finsum' c (twTerm_support_finite A₁ Y β n w)]
    congr 1
    refine finsum_congr (fun t => ?_)
    simp only [twTerm, map_smul]
    rw [smul_comm]

/-- `twI` as an explicit finite sum, for any tower bound `J`. -/
theorem twI_apply_eq_sum (Y : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) {w : M₁} {J : ℕ}
    (hJ : ∀ t, J ≤ t → (L1w A₁.toWeakModule ^ t) w = 0) (y : M₂) :
    twI A₁ Y β n w y = statePhase β • ∑ t ∈ Finset.range J,
      ((t.factorial : ℂ)⁻¹) • Y (2 * β - n - 2 - t) ((L1w A₁.toWeakModule ^ t) w) y := by
  change (statePhase β • ∑ᶠ t : ℕ, twTerm A₁ Y β n w t) y = _
  rw [finsum_eq_sum_of_support_subset _ (twTerm_support A₁ Y β n w hJ)]
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, twTerm]

/-- `twI` with the `t`-sum as a `finsum` of vectors. -/
theorem twI_apply_finsum (Y : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) (w : M₁) (y : M₂) :
    twI A₁ Y β n w y = statePhase β • ∑ᶠ t : ℕ,
      ((t.factorial : ℂ)⁻¹) • Y (2 * β - n - 2 - t) ((L1w A₁.toWeakModule ^ t) w) y := by
  obtain ⟨J, hJ⟩ := L1w_pow_eventually A₁ w
  rw [twI_apply_eq_sum A₁ Y β n hJ y]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range J) (fun t ht => by
    rw [Function.mem_support] at ht
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact ht (by rw [hJ t (by omega), map_zero, LinearMap.zero_apply, smul_zero]))]

theorem twI_add_Y (Y Y' : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) (w : M₁) (y : M₂) :
    twI A₁ (Y + Y') β n w y = twI A₁ Y β n w y + twI A₁ Y' β n w y := by
  obtain ⟨J, hJ⟩ := L1w_pow_eventually A₁ w
  rw [twI_apply_eq_sum A₁ _ β n hJ, twI_apply_eq_sum A₁ _ β n hJ, twI_apply_eq_sum A₁ _ β n hJ,
    ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [Pi.add_apply, LinearMap.add_apply, smul_add]

theorem twI_smul_Y (c : ℂ) (Y : IntertwiningModes M₁ M₂ M₃) (β n : ℂ) (w : M₁) (y : M₂) :
    twI A₁ (c • Y) β n w y = c • twI A₁ Y β n w y := by
  obtain ⟨J, hJ⟩ := L1w_pow_eventually A₁ w
  rw [twI_apply_eq_sum A₁ _ β n hJ, twI_apply_eq_sum A₁ _ β n hJ, Finset.smul_sum, Finset.smul_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [Pi.smul_apply, LinearMap.smul_apply]
  rw [smul_comm c, smul_comm c]

end Twist

/-! ## The opposite Jacobi identity: left side -/

section OppLeft

variable {A₁ : C2Rigid.GWModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {Y : IntertwiningModes M₁ M₂ M₃}

theorem oppB_apply_homog {M : Type u} [AddCommGroup M] [Module ℂ M] (N : WeakModule W M)
    {p : ℤ} {u : V} (hu : u ∈ W.grading p) (k : ℤ) (z : M) :
    oppB N u k z = (-1 : ℂ) ^ p • ∑ a ∈ Finset.range (p.toNat + 1),
      ((a.factorial : ℂ)⁻¹) • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - k - 2 - (a : ℤ)) z := by
  rw [oppB_homog N hu]
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

/-- A sign flip: `k(cX₁ − s cX₂) = (c(−s)) k(X₂ − sX₁)` when `s² = 1`. -/
theorem sign_flip {E : Type*} [AddCommGroup E] [Module ℂ E] (c k s : ℂ) (hs : s * s = 1)
    (X₁ X₂ : E) : k • (c • X₁ - s • c • X₂) = (c * -s) • (k • (X₂ - s • X₁)) := by
  have h : (c * -s) • (k • (X₂ - s • X₁)) = (c * k) • ((s * s) • X₁) - (c * k * s) • X₂ := by
    module
  rw [h, hs, one_smul]
  module

/-- First product expanded in the towers. -/
theorem lhs_expand₁ {p : ℤ} {u : V} (hu : u ∈ W.grading p) (α : ℂ) {w : M₁} {J : ℕ}
    (hJ : ∀ t, J ≤ t → (L1w A₁.toWeakModule ^ t) w = 0) (y : M₂) (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    twI A₁ Y α (n + i) w (oppB A₂ u (ℓ + m - i) y)
      = ∑ a ∈ Finset.range (p.toNat + 1), ∑ b ∈ Finset.range J,
          (statePhase α * (-1 : ℂ) ^ p * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹)) •
            Y ((ℓ : ℂ) + (2 * α - ℓ - n - 2 - b) - i) ((L1w A₁.toWeakModule ^ b) w)
              (mode (A₂.YM ((W.L 1 ^ a) u)) ((2 * p - ℓ - m - 2 - (a : ℤ)) + i) y) := by
  rw [twI_apply_eq_sum A₁ Y α _ hJ, oppB_apply_homog A₂ hu]
  simp only [map_smul, map_sum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  congr 1
  · ring
  · congr 2
    · congr 1; ring
    · congr 1; ring

/-- Second product expanded in the towers. -/
theorem lhs_expand₂ {p : ℤ} {u : V} (hu : u ∈ W.grading p) (α : ℂ) {w : M₁} {J : ℕ}
    (hJ : ∀ t, J ≤ t → (L1w A₁.toWeakModule ^ t) w = 0) (y : M₂) (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    oppB A₃ u (m + i) (twI A₁ Y α (ℓ + n - i) w y)
      = ∑ a ∈ Finset.range (p.toNat + 1), ∑ b ∈ Finset.range J,
          (statePhase α * (-1 : ℂ) ^ p * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹)) •
            mode (A₃.YM ((W.L 1 ^ a) u)) (ℓ + (2 * p - ℓ - m - 2 - (a : ℤ)) - i)
              (Y ((2 * α - ℓ - n - 2 - b) + i) ((L1w A₁.toWeakModule ^ b) w) y) := by
  rw [twI_apply_eq_sum A₁ Y α _ hJ, oppB_apply_homog A₃ hu]
  simp only [map_smul, map_sum, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  congr 1
  · ring
  · congr 2
    · ring
    · congr 2; ring

/-- **Left side of the opposite Jacobi identity, per `i`**: a combination of left sides of the
Jacobi identity of `𝒴` for the tower pairs `(L(1)ᵃu, L(1)ᵇw)`. -/
theorem lhs_term {p : ℤ} {u : V} (hu : u ∈ W.grading p) (α : ℂ) {w : M₁} {J : ℕ}
    (hJ : ∀ t, J ≤ t → (L1w A₁.toWeakModule ^ t) w = 0) (y : M₂) (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    (negOnePow i * cbz ℓ i) • (twI A₁ Y α (n + i) w (oppB A₂ u (ℓ + m - i) y)
        - negOnePow ℓ • oppB A₃ u (m + i) (twI A₁ Y α (ℓ + n - i) w y))
      = ∑ a ∈ Finset.range (p.toNat + 1), ∑ b ∈ Finset.range J,
          (statePhase α * (-1 : ℂ) ^ p * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * -negOnePow ℓ) •
            jacL A₂ A₃ Y ((W.L 1 ^ a) u) ((L1w A₁.toWeakModule ^ b) w) y ℓ
              (2 * p - ℓ - m - 2 - (a : ℤ)) (2 * α - ℓ - n - 2 - b) i := by
  rw [lhs_expand₁ hu α hJ y ℓ m n i, lhs_expand₂ hu α hJ y ℓ m n i, Finset.smul_sum,
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [jacL]
  exact sign_flip _ _ _ (negOnePow_mul_self ℓ) _ _

end OppLeft

/-! ## The opposite Jacobi identity: right side -/

section OppRight

variable {A₁ : C2Rigid.GWModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {Y : IntertwiningModes M₁ M₂ M₃}

/-- The common family `𝒴_{κ−a−b−r}((L(1)ᵃu)_{ℓ+r} L(1)ᵇw) y` of both sides. -/
noncomputable def vecV (A₁ : C2Rigid.GWModule W M₁) (Y : IntertwiningModes M₁ M₂ M₃) (u : V) (w : M₁)
    (y : M₂) (κ : ℂ) (ℓ : ℤ) (a b : ℕ) (r : ℤ) : M₃ :=
  Y (κ - a - b - r) (mode (A₁.YM ((W.L 1 ^ a) u)) (ℓ + r) ((L1w A₁.toWeakModule ^ b) w)) y

/-- **Right side of the opposite Jacobi identity, per `i`** (via `comul_sum`). -/
theorem rhs_term {p : ℤ} {u : V} (hu : u ∈ W.grading p) (α : ℂ) {w : M₁} (y : M₂)
    (ℓ m : ℤ) (n : ℂ) {P C J : ℕ}
    (hP : ∀ a, P ≤ a → (W.L 1 ^ a) u = 0) (hJ : ∀ b, J ≤ b → (L1w A₁.toWeakModule ^ b) w = 0)
    (hC : ∀ (a b : ℕ) (k : ℤ), ℓ + (C : ℤ) ≤ k →
      mode (A₁.YM ((W.L 1 ^ a) u)) k ((L1w A₁.toWeakModule ^ b) w) = 0) (i : ℤ) :
    cbz m i • twI A₁ Y (α + p - (ℓ + i) - 1) (m + n - i) (mode (A₁.YM u) (ℓ + i) w) y
      = ∑ a ∈ Finset.range P, ∑ c ∈ Finset.range C, ∑ b ∈ Finset.range J,
          (cbz m i * ((-1 : ℂ) ^ (p - (ℓ + i) - 1) * statePhase α) * comulCoeff p (ℓ + i) a c b) •
            vecV A₁ Y u w y (2 * p + 2 * α - 2 * ℓ - m - n - 4) ℓ a b (i + c) := by
  rcases lt_or_ge i 0 with hi | hi
  · simp only [cbz_apply_neg m hi, zero_mul, zero_smul, Finset.sum_const_zero]
  rw [twI_apply_finsum]
  set β : ℂ := α + p - (ℓ + i) - 1 with hβ
  have hph : statePhase β = (-1 : ℂ) ^ (p - (ℓ + i) - 1) * statePhase α := by
    rw [show β = α + ((p - (ℓ + i) - 1 : ℤ) : ℂ) by rw [hβ]; push_cast; ring, statePhase_add_int]
  set G : ℕ → M₁ →ₗ[ℂ] M₃ := fun t => (Y (2 * β - (m + n - i) - 2 - t)).flip y with hG
  have hsum := comul_sum A₁.toWeakModule (E := M₃) hu (ℓ + i) w G P C J hP hJ (fun a b c hc => hC a b _
    (by omega))
  have hl : (∑ᶠ t : ℕ, ((t.factorial : ℂ)⁻¹) •
      Y (2 * β - (m + n - i) - 2 - t) ((L1w A₁.toWeakModule ^ t) (mode (A₁.YM u) (ℓ + i) w)) y)
      = ∑ᶠ t : ℕ, ((t.factorial : ℂ)⁻¹) • G t ((L1w A₁.toWeakModule ^ t) (mode (A₁.YM u) (ℓ + i) w)) := rfl
  rw [hl, hsum, hph, smul_smul]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ =>
    Finset.sum_congr rfl (fun b _ => ?_)))
  congr 1
  rw [hG, vecV, LinearMap.flip_apply]
  congr 2
  · rw [hβ]; push_cast; ring_nf
  · congr 1; ring_nf

end OppRight

/-! ## Bookkeeping -/

section Bookkeeping

/-- A `finsum` over `ℤ` supported in `[0, C)` is a sum over `range C`. -/
theorem finsum_int_eq_sum_range {E : Type*} [AddCommGroup E] (f : ℤ → E) (C : ℕ)
    (h0 : ∀ i : ℤ, i < 0 → f i = 0)
    (hC : ∀ i : ℤ, (C : ℤ) ≤ i → f i = 0) :
    ∑ᶠ i : ℤ, f i = ∑ i ∈ Finset.range C, f (i : ℤ) := by
  rw [VOA.Huang.FusionTop.finsum_int_eq_range f C (fun i hi => by
    rcases hi with hi | hi
    · exact h0 i hi
    · exact hC i (by omega)), Finset.sum_range_succ, hC C le_rfl, add_zero]

/-- Antidiagonal reindexing of a box sum. -/
theorem diag_sum {E : Type*} [AddCommGroup E] [Module ℂ E] (h : ℕ → ℕ → ℂ) (V : ℕ → E) (C : ℕ)
    (hV : ∀ r, C ≤ r → V r = 0) :
    ∑ c ∈ Finset.range C, ∑ i ∈ Finset.range C, h i c • V (i + c)
      = ∑ r ∈ Finset.range C, (∑ c ∈ Finset.range (r + 1), h (r - c) c) • V r := by
  have hR : ∀ r ∈ Finset.range C, (∑ c ∈ Finset.range (r + 1), h (r - c) c) • V r
      = ∑ c ∈ Finset.range (r + 1), (fun c i => h i c • V (i + c)) c (r - c) := by
    intro r _
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hc
    simp only
    rw [Nat.sub_add_cancel hc]
  rw [Finset.sum_congr rfl hR, Finset.sum_range_diag_flip C (fun c i => h i c • V (i + c))]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [Finset.mem_range] at hc
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le C c)) (fun i hi hi' => ?_)
  rw [Finset.mem_range] at hi hi'
  rw [hV (i + c) (by omega), smul_zero]

/-- **The coefficient identity** (Vandermonde): the left and right coefficients of
`𝒴_{κ−a−b−r}((L(1)ᵃu)_{ℓ+r} L(1)ᵇw) y` agree. -/
theorem coeff_match (p ℓ m : ℤ) (α : ℂ) (a b r : ℕ) :
    statePhase α * (-1 : ℂ) ^ p * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * -negOnePow ℓ
        * cbz (2 * p - ℓ - m - 2 - (a : ℤ)) r
      = ∑ c ∈ Finset.range (r + 1), cbz m ((r - c : ℕ) : ℤ)
          * ((-1 : ℂ) ^ (p - (ℓ + ((r - c : ℕ) : ℤ)) - 1) * statePhase α)
          * comulCoeff p (ℓ + ((r - c : ℕ) : ℤ)) a c b := by
  rw [← Finset.sum_range_reflect]
  have hterm : ∀ k ∈ Finset.range (r + 1),
      cbz m ((r - (r + 1 - 1 - k) : ℕ) : ℤ)
          * ((-1 : ℂ) ^ (p - (ℓ + ((r - (r + 1 - 1 - k) : ℕ) : ℤ)) - 1) * statePhase α)
          * comulCoeff p (ℓ + ((r - (r + 1 - 1 - k) : ℕ) : ℤ)) a (r + 1 - 1 - k) b
        = (statePhase α * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * (-1 : ℂ) ^ (p - ℓ - 1))
          * ((-1 : ℂ) ^ k * gBinom m k * gBinom ((2 * p - ℓ - 2 - (a : ℤ)) - k) (r - k)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e1 : r - (r + 1 - 1 - k) = k := by omega
    have e2 : r + 1 - 1 - k = r - k := by omega
    rw [e1, e2, cbz_apply_nonneg m (by positivity), Int.toNat_natCast, comulCoeff]
    have hz : (-1 : ℂ) ^ (p - (ℓ + (k : ℤ)) - 1) = (-1 : ℂ) ^ (p - ℓ - 1) * (-1 : ℂ) ^ k := by
      rw [show p - (ℓ + (k : ℤ)) - 1 = (p - ℓ - 1) + (-(k : ℤ)) by ring,
        zpow_add₀ (by norm_num), zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
    rw [hz, show 2 * p - (ℓ + (k : ℤ)) - 2 - (a : ℤ) = (2 * p - ℓ - 2 - (a : ℤ)) - k by ring]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, vandermonde_neg,
    cbz_apply_nonneg _ (by positivity), Int.toNat_natCast,
    show 2 * p - ℓ - 2 - (a : ℤ) - m = 2 * p - ℓ - m - 2 - (a : ℤ) by ring,
    VOA.Huang.LiRegular.negOnePow_eq_zpow]
  have hs : (-1 : ℂ) ^ p * -(-1 : ℂ) ^ ℓ = (-1 : ℂ) ^ (p - ℓ - 1) := by
    rw [show p - ℓ - 1 = p + (-ℓ) + (-1) by ring, zpow_add₀ (by norm_num),
      zpow_add₀ (by norm_num), zpow_neg, zpow_neg]
    have hl : ((-1 : ℂ) ^ ℓ)⁻¹ = (-1 : ℂ) ^ ℓ := by
      rw [← inv_zpow, inv_neg, inv_one]
    rw [hl]
    norm_num
  linear_combination (statePhase α * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹)
    * gBinom (2 * p - ℓ - m - 2 - (a : ℤ)) r) * hs

end Bookkeeping

/-! ## The opposite Jacobi identity -/

section OppJacobi

variable {A₁ : C2Rigid.GWModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {Y : IntertwiningModes M₁ M₂ M₃}

/-- A uniform truncation bound for the tower modes. -/
theorem exists_tower_bound {u : V} (w : M₁) (ℓ : ℤ) (P J : ℕ)
    (hP : ∀ a, P ≤ a → (W.L 1 ^ a) u = 0) (hJ : ∀ b, J ≤ b → (L1w A₁.toWeakModule ^ b) w = 0) :
    ∃ C : ℕ, ∀ (a b : ℕ) (k : ℤ), ℓ + (C : ℤ) ≤ k →
      mode (A₁.YM ((W.L 1 ^ a) u)) k ((L1w A₁.toWeakModule ^ b) w) = 0 := by
  classical
  choose Nf hNf using fun ab : ℕ × ℕ =>
    A₁.toWeakModule.truncation ((W.L 1 ^ ab.1) u) ((L1w A₁.toWeakModule ^ ab.2) w)
  set S : Finset (ℕ × ℕ) := Finset.range P ×ˢ Finset.range J
  set B : ℕ := ∑ ab ∈ S, (Nf ab).natAbs
  refine ⟨(B : ℤ) - ℓ |>.toNat, fun a b k hk => ?_⟩
  rcases le_or_gt P a with ha | ha
  · rw [hP a ha, map_zero, mode_zero, LinearMap.zero_apply]
  rcases le_or_gt J b with hb | hb
  · rw [hJ b hb, map_zero]
  have hmem : (a, b) ∈ S := Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha,
    Finset.mem_range.mpr hb⟩
  have hle : (Nf (a, b)).natAbs ≤ B :=
    Finset.single_le_sum (f := fun ab => (Nf ab).natAbs) (fun _ _ => Nat.zero_le _) hmem
  exact hNf (a, b) k (by omega)

/-- **The opposite Jacobi identity** of the twisted intertwiner (FHL (5.5.4)–(5.5.5) in
modes): for `u ∈ V_p`, any `w ∈ M₁` (twisted with weight parameter `α`) and `y ∈ M₂`,
`Σᶠᵢ (−1)ⁱC(ℓ,i)(𝒴°_{n+i}(w) u°_{ℓ+m−i} y − (−1)^ℓ u°_{m+i} 𝒴°_{ℓ+n−i}(w) y)
  = Σᶠᵢ C(m,i) 𝒴°_{m+n−i}(u_{ℓ+i}w) y`, the twist of `u_{ℓ+i}w` using `α + p − ℓ − i − 1`. -/
theorem opp_jacobi (hY : IsJacobiFamily A₁.toWeakModule A₂ A₃ Y) {p : ℤ} {u : V}
    (hu : u ∈ W.grading p) (α : ℂ) (w : M₁) (y : M₂) (ℓ m : ℤ) (n : ℂ) :
    ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • (twI A₁ Y α (n + i) w (oppB A₂ u (ℓ + m - i) y)
        - negOnePow ℓ • oppB A₃ u (m + i) (twI A₁ Y α (ℓ + n - i) w y))
      = ∑ᶠ i : ℤ, cbz m i •
          twI A₁ Y (α + p - (ℓ + i) - 1) (m + n - i) (mode (A₁.YM u) (ℓ + i) w) y := by
  classical
  set P : ℕ := p.toNat + 1 with hPdef
  have hP : ∀ a, P ≤ a → (W.L 1 ^ a) u = 0 := fun a ha =>
    L_one_pow_eq_zero W hu (by omega)
  obtain ⟨J, hJ⟩ := L1w_pow_eventually A₁ w
  obtain ⟨C, hC⟩ := exists_tower_bound (A₁ := A₁) w ℓ P J hP hJ
  set κ : ℂ := 2 * p + 2 * α - 2 * ℓ - m - n - 4 with hκ
  set cL : ℕ → ℕ → ℂ := fun a b =>
    statePhase α * (-1 : ℂ) ^ p * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * -negOnePow ℓ with hcL
  have hVz : ∀ (a b : ℕ) (r : ℕ), C ≤ r → vecV A₁ Y u w y κ ℓ a b r = 0 := by
    intro a b r hr
    rw [vecV, hC a b _ (by omega), map_zero, LinearMap.zero_apply]
  -- left side
  have hL : ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • (twI A₁ Y α (n + i) w (oppB A₂ u (ℓ + m - i) y)
        - negOnePow ℓ • oppB A₃ u (m + i) (twI A₁ Y α (ℓ + n - i) w y))
      = ∑ a ∈ Finset.range P, ∑ b ∈ Finset.range J, cL a b •
          ∑ r ∈ Finset.range C,
            cbz (2 * p - ℓ - m - 2 - (a : ℤ)) r • vecV A₁ Y u w y κ ℓ a b r := by
    rw [finsum_congr (lhs_term (Y := Y) (A₂ := A₂) (A₃ := A₃) hu α hJ y ℓ m n)]
    rw [finsum_sum_comm]
    swap
    · intro a _
      exact hasFiniteSupport_finsetSum _ _ (fun b _ =>
        (jacL_support_finite hY.truncation _ _ y ℓ _ _).subset
          (Function.support_const_smul_subset _ _))
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [finsum_sum_comm]
    swap
    · intro b _
      exact (jacL_support_finite hY.truncation _ _ y ℓ _ _).subset
        (Function.support_const_smul_subset _ _)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hjac : ∀ (U : V) (X : M₁) (m' : ℤ) (n' : ℂ),
        ∑ᶠ i, jacL A₂ A₃ Y U X y ℓ m' n' i
          = ∑ᶠ i, jacR A₁.toWeakModule Y U X y ℓ m' n' i :=
      fun U X m' n' => hY.jacobi U X y ℓ m' n'
    rw [← smul_finsum, hjac]
    congr 1
    rw [finsum_int_eq_sum_range _ C (fun i hi => by
        rw [jacR, cbz_apply_neg _ hi, zero_smul])
      (fun i hi => by
        rw [jacR, hC a b _ (by omega), map_zero, LinearMap.zero_apply,
          smul_zero])]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [jacR, vecV]
    congr 2
    rw [hκ]; push_cast; ring_nf
  -- right side
  have hR : ∑ᶠ i : ℤ, cbz m i •
        twI A₁ Y (α + p - (ℓ + i) - 1) (m + n - i) (mode (A₁.YM u) (ℓ + i) w) y
      = ∑ a ∈ Finset.range P, ∑ b ∈ Finset.range J, ∑ r ∈ Finset.range C,
          (∑ c ∈ Finset.range (r + 1), cbz m ((r - c : ℕ) : ℤ)
            * ((-1 : ℂ) ^ (p - (ℓ + ((r - c : ℕ) : ℤ)) - 1) * statePhase α)
            * comulCoeff p (ℓ + ((r - c : ℕ) : ℤ)) a c b) • vecV A₁ Y u w y κ ℓ a b r := by
    rw [finsum_int_eq_sum_range _ C (fun i hi => by rw [cbz_apply_neg _ hi, zero_smul])
      (fun i hi => by
        have h0 := hC 0 0 (ℓ + i) (by omega)
        simp only [pow_zero, Module.End.one_apply] at h0
        rw [h0, map_zero, LinearMap.zero_apply, smul_zero])]
    rw [Finset.sum_congr rfl (fun (i : ℕ) _ => rhs_term (Y := Y) hu α y ℓ m n hP hJ hC (i : ℤ))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun c _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have := diag_sum (fun i c => cbz m (i : ℤ) * ((-1 : ℂ) ^ (p - (ℓ + (i : ℤ)) - 1) * statePhase α)
        * comulCoeff p (ℓ + (i : ℤ)) a c b) (fun r : ℕ => vecV A₁ Y u w y κ ℓ a b r) C
      (fun r hr => hVz a b r hr)
    simp only [Nat.cast_add] at this
    rw [← this]
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [smul_smul, ← coeff_match]

end OppJacobi


end VOA.LogTensor.Ar
