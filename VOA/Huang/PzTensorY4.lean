/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorHatBridge
import VOA.Huang.HuangODEContra

/-!
# The first iterate intertwiner `𝒴₄` from a `τ`-module of compatible functions

Let `R` be a lowest-weight module and `ψ : R → (P₁ ⊗ P₂)*` a linear map into bilinear functions
of homogeneous pairs which **intertwines** the module action of `R` with the Huang–Lepowsky
action `τ`, and whose image consists of lower-truncated compatible functions (`TauEmb`).  Then

`⟨𝒴₄(w₁, x) w₂, r⟩ = ψ(r)(w₁, w₂) x^{wt r − wt w₁ − wt w₂}`

defines an intertwining operator `𝒴₄` of type `(R' / P₁ P₂)` with values in the contragredient
`R' = contraLW R` (`isIntertwining_Y4`).  The Jacobi identity of `𝒴₄` is exactly the family
of compatibility slices `PzTensorRho.slice_holds`, transported through the **double twist**
`twist_twist` (the contragredient modes of `R'` act on `ψ(R)` by the transposed coproduct `ρ`);
the `L₋₁`-property is the `L'(0)`-eigenvalue equation `L0T ψ(r) = wt(r) ψ(r)`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorY4

open VOA VOA.Huang.LogRemovalSemisimple VOA.Huang.PzTensorBilin VOA.Huang.PzTensorAction
open VOA.Huang.PzTensorCompat VOA.Huang.PzTensorRho VOA.Huang.PzTensorHatBridge
open VOA.Huang.HuangODEContra VOA.Huang.AssocTauStable
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## The double twist -/

/-- `Σ_{j ≤ N} (−1)^j / (j! (N−j)!) = δ_{N,0}`. -/
theorem alt_inv_fact (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)
      = if N = 0 then 1 else 0 := by
  have hN : ((N.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have key : ∀ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j
      * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)
      = (N.factorial : ℂ)⁻¹ * (((-1 : ℤ) ^ j * (N.choose j : ℤ) : ℤ) : ℂ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hc := Nat.choose_mul_factorial_mul_factorial (show j ≤ N by omega)
    have hj' : ((j.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hNj : (((N - j).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N - j)
    have hc' : ((N.choose j : ℂ)) * (j.factorial : ℂ) * ((N - j).factorial : ℂ)
        = (N.factorial : ℂ) := by exact_mod_cast hc
    have hC : ((N.choose j : ℂ)) = (N.factorial : ℂ) * ((j.factorial : ℂ)⁻¹
        * ((N - j).factorial : ℂ)⁻¹) := by
      field_simp
      linear_combination hc'
    push_cast
    rw [hC]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Int.cast_sum,
    Int.alternating_sum_range_choose]
  split_ifs with h
  · subst h; simp
  · simp

/-- The triangle sum `Σ_{j+i ≤ w} (−1)^j/(j! i!) T(i+j) = T 0`. -/
theorem triangle_sum {X : Type*} [AddCommGroup X] [Module ℂ X] (w : ℕ) (T : ℕ → X) :
    ∑ j ∈ Finset.range (w + 1), ∑ i ∈ Finset.range (w - j + 1),
      ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹)) • T (i + j) = T 0 := by
  -- reindex the inner sum by `N = i + j`
  have h1 : ∀ j ∈ Finset.range (w + 1), ∑ i ∈ Finset.range (w - j + 1),
      ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹)) • T (i + j)
      = ∑ N ∈ Finset.Ico j (w + 1),
          ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)) • T N := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.sum_Ico_eq_sum_range, show w + 1 - j = w - j + 1 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show j + i - j = i by omega, add_comm i j]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.range (w + 1)) (s' := fun N => Finset.range (N + 1))
    (fun j N => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have h2 : ∀ N ∈ Finset.range (w + 1), ∑ j ∈ Finset.range (N + 1),
      ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)) • T N
      = (if N = 0 then (1 : ℂ) else 0) • T N := by
    intro N _
    rw [← Finset.sum_smul, alt_inv_fact]
  rw [Finset.sum_congr rfl h2, Finset.sum_eq_single 0 (fun N _ hN => by rw [if_neg hN, zero_smul])
    (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos w)) h), if_pos rfl, one_smul]

section Twist

variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
variable (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)

/-- **The double twist**: the contragredient twist of `τ̂` is `ρ`. -/
theorem twist_twist {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (k : ℤ)
    (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) :
    (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
        tauHat A₁ A₂ (wt - j) ((W.L 1 ^ j) u) (2 * wt - k - 2 - (j : ℤ)) β
      = rhoL A₁ A₂ u k β := by
  rcases lt_or_ge wt 0 with hw | hw
  · have hu0 : u = 0 := by
      have := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hu (j := 0) (by omega)
      simpa using this
    subst hu0
    simp [tauHat, rhoL_zero_state]
  obtain ⟨w, rfl⟩ : ∃ w : ℕ, wt = w := ⟨wt.toNat, (Int.toNat_of_nonneg hw).symm⟩
  simp only [Int.toNat_natCast, tauHat, Finset.smul_sum, smul_smul]
  have hin : ∀ j ∈ Finset.range (w + 1), ∀ i ∈ Finset.range (((w : ℤ) - (j : ℤ)).toNat + 1),
      ((-1 : ℂ) ^ (w : ℤ) * ((j.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ ((w : ℤ) - (j : ℤ))
        * (i.factorial : ℂ)⁻¹))) •
        rhoL A₁ A₂ ((W.L 1 ^ i) ((W.L 1 ^ j) u))
          (2 * ((w : ℤ) - (j : ℤ)) - (2 * (w : ℤ) - k - 2 - (j : ℤ)) - 2 - (i : ℤ)) β
      = ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹)) •
            rhoL A₁ A₂ ((W.L 1 ^ (i + j)) u) (k - ((i + j : ℕ) : ℤ)) β := by
    intro j hj i _
    have hs : (-1 : ℂ) ^ (w : ℤ) * (-1 : ℂ) ^ ((w : ℤ) - (j : ℤ)) = (-1 : ℂ) ^ j := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        show (w : ℤ) + ((w : ℤ) - (j : ℤ)) = 2 * ((w : ℤ) - (j : ℤ)) + j by ring,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
      norm_num
    rw [show (2 * ((w : ℤ) - (j : ℤ)) - (2 * (w : ℤ) - k - 2 - (j : ℤ)) - 2 - (i : ℤ))
      = k - ((i + j : ℕ) : ℤ) by push_cast; ring, pow_add, Module.End.mul_apply]
    congr 1
    linear_combination ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹) * hs
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => hin j hj i hi]
  have hrange : ∀ j ∈ Finset.range (w + 1), ((w : ℤ) - (j : ℤ)).toNat = w - j := by
    intro j hj; rw [Finset.mem_range] at hj; omega
  rw [Finset.sum_congr rfl fun j hj => by rw [hrange j hj]]
  rw [triangle_sum w (fun N => rhoL A₁ A₂ ((W.L 1 ^ N) u) (k - (N : ℤ)) β)]
  simp

end Twist

/-! ## The double twist on functions of homogeneous pairs -/

variable {P₁ P₂ : LWModule W}

theorem twist_twist_fn {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {wt : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading wt) (k : ℤ) (x : HomPair P₁ P₂) :
    (-1 : ℂ) ^ wt * ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) *
        tauHom (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) (2 * wt - k - 2 - (j : ℤ)) G x
      = copT hu k G x := by
  have h := congrArg (fun β => β x.w₁ x.w₂) (twist_twist (A₁ P₁) (A₁ P₂) hu k (hatG G hG))
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, smul_eq_mul] at h
  rw [copT_eq_rho hG hu k x, ← h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tauHom_eq_tauHat hG]

/-- The compatibility slices on functions of homogeneous pairs. -/
theorem slice_fn {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G)
    (htr : ∀ (γ : ℤ) (a : 𝒱) (ha : a ∈ W.grading γ), ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p G = 0)
    (hc : CompatFn G) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (m L : ℤ)
    (x : HomPair P₁ P₂) :
    ∑ᶠ k : ℤ, (negOnePow k * cbz L k) * copT hu (m + L - k) G x
      = ∑ᶠ r : ℤ, cbz m r * G (pairLeft x hu (L + r))
        + ∑ᶠ j : ℤ, (cbz L j * negOnePow (L - j)) * G (pairRight x hu (m + j)) := by
  have h := slice_holds (A₁ P₁) (A₁ P₂) (truncAt_hat hG hu (htr _ _ hu))
    (compatAt_hat hG hu (htr _ _ hu) hc) m L x.w₁ x.w₂
  unfold Out InL InR at h
  have e1 : ∀ k : ℤ, (negOnePow k * cbz L k) * copT hu (m + L - k) G x
      = (negOnePow k * cbz L k) * rhoL (A₁ P₁) (A₁ P₂) u (m + L - k) (hatG G hG) x.w₁ x.w₂ :=
    fun k => by rw [copT_eq_rho hG]
  have e2 : ∀ r : ℤ, cbz m r * G (pairLeft x hu (L + r))
      = cbz m r * hatG G hG (mode ((A₁ P₁).YM u) (L + r) x.w₁) x.w₂ := fun r => by
    rw [hatG_homog G hG (VOA.mode_mem_weight P₁.isMod hu x.h₁ (L + r)) x.h₂]; rfl
  have e3 : ∀ j : ℤ, (cbz L j * negOnePow (L - j)) * G (pairRight x hu (m + j))
      = (cbz L j * negOnePow (L - j)) * hatG G hG x.w₁ (mode ((A₁ P₂).YM u) (m + j) x.w₂) :=
    fun j => by
      rw [hatG_homog G hG x.h₁ (VOA.mode_mem_weight P₂.isMod hu x.h₂ (m + j))]; rfl
  rw [finsum_congr e1, finsum_congr e2, finsum_congr e3]
  exact h

/-! ## Bilinear maps from blocks on weight spaces -/

section BiHat

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

open Classical in
/-- The bilinear map on `P₁ × P₂` assembled from its blocks on pairs of weight spaces. -/
noncomputable def biHat
    (Φ : ∀ α₁ α₂ : ℂ, P₁.isMod.weight α₁ →ₗ[ℂ] P₂.isMod.weight α₂ →ₗ[ℂ] X) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] X :=
  letI := DirectSum.IsInternal.chooseDecomposition P₁.isMod.weight P₁.isMod.isInternal
  letI := DirectSum.IsInternal.chooseDecomposition P₂.isMod.weight P₂.isMod.isInternal
  ((DFinsupp.lsum ℂ fun α₁ => (DFinsupp.lsum ℂ (M := fun α₂ => P₂.isMod.weight α₂)
      (N := X)).toLinearMap ∘ₗ LinearMap.pi fun α₂ => Φ α₁ α₂)
    ∘ₗ (DirectSum.decomposeLinearEquiv P₁.isMod.weight).toLinearMap).compl₂
    (DirectSum.decomposeLinearEquiv P₂.isMod.weight).toLinearMap

theorem biHat_homog (Φ : ∀ α₁ α₂ : ℂ, P₁.isMod.weight α₁ →ₗ[ℂ] P₂.isMod.weight α₂ →ₗ[ℂ] X)
    {α₁ α₂ : ℂ} {y : P₁.carrier} {z : P₂.carrier}
    (hy : y ∈ P₁.isMod.weight α₁) (hz : z ∈ P₂.isMod.weight α₂) :
    biHat Φ y z = Φ α₁ α₂ ⟨y, hy⟩ ⟨z, hz⟩ := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition P₁.isMod.weight P₁.isMod.isInternal
  letI := DirectSum.IsInternal.chooseDecomposition P₂.isMod.weight P₂.isMod.isInternal
  have e1 : (DirectSum.decomposeLinearEquiv P₁.isMod.weight) y
      = DirectSum.of (fun i => P₁.isMod.weight i) α₁ ⟨y, hy⟩ :=
    DirectSum.decompose_of_mem _ hy
  have e2 : (DirectSum.decomposeLinearEquiv P₂.isMod.weight) z
      = DirectSum.of (fun i => P₂.isMod.weight i) α₂ ⟨z, hz⟩ :=
    DirectSum.decompose_of_mem _ hz
  simp only [biHat, LinearMap.compl₂_apply, LinearMap.comp_apply]
  erw [e1, e2]
  erw [DFinsupp.lsum_single]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [DFinsupp.lsum_single]
  rfl

end BiHat

/-! ## Intertwining operators from homogeneous data -/

section OfHomog

variable {M₃ : Type*} [AddCommGroup M₃] [Module ℂ M₃] {A₃ : OrdVModule W M₃}

/-- The Jacobi identity of an intertwining operator at one datum. -/
def JacAt (A₃ : OrdVModule W M₃) (Y : IntertwiningModes P₁.carrier P₂.carrier M₃) (u : 𝒱)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (ℓ m : ℤ) (n : ℂ) : Prop :=
  (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) w₁ w₂)
        - negOnePow ℓ • Y (ℓ + n - i) w₁ (mode (P₂.isMod.YM u) (m + i) w₂)))
    = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) (mode (P₁.isMod.YM u) (ℓ + i) w₁) w₂

/-- **Intertwining operators from homogeneous data**: truncation, plus the `L₋₁`-property
and the Jacobi identity on homogeneous states and vectors, give an intertwining operator. -/
theorem isIntertwining_of_homog {Y : IntertwiningModes P₁.carrier P₂.carrier M₃}
    (htr : ∀ (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n : ℂ),
      ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) w₁ w₂ = 0)
    (hL : ∀ (α₁ α₂ : ℂ) (y : P₁.carrier) (z : P₂.carrier), y ∈ P₁.isMod.weight α₁ →
      z ∈ P₂.isMod.weight α₂ → ∀ n : ℂ, Y n (P₁.isMod.Lm1 y) z = (-n) • Y (n - 1) y z)
    (hJ : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → ∀ (α₁ α₂ : ℂ) (y : P₁.carrier)
      (z : P₂.carrier), y ∈ P₁.isMod.weight α₁ → z ∈ P₂.isMod.weight α₂ →
      ∀ (ℓ m : ℤ) (n : ℂ), JacAt A₃ Y u y z ℓ m n) :
    IsIntertwiningOperator P₁.isMod P₂.isMod A₃ Y := by
  refine ⟨htr, ?_, ?_⟩
  · intro w₁ n
    ext z
    rw [LinearMap.smul_apply]
    have := eq_zero_of_homog (fun y z => Y n (P₁.isMod.Lm1 y) z - (-n) • Y (n - 1) y z)
      (fun y y' z => by simp only [map_add, LinearMap.add_apply, smul_add]; abel)
      (fun y z z' => by simp only [map_add, smul_add]; abel)
      (fun α₁ α₂ y z hy hz => by dsimp only; rw [hL α₁ α₂ y z hy hz n, sub_self]) w₁ z
    exact sub_eq_zero.mp this
  · intro u w₁ w₂ ℓ m n
    -- the defect is additive in each argument
    have hfinL := fun (u : 𝒱) (w₁ : P₁.carrier) (w₂ : P₂.carrier) =>
      IsIntertwiningOperator.jacL_support_finite (A₂ := P₂.isMod) (A₃ := A₃) htr u w₁ w₂ ℓ m n
    have hfinR := fun (u : 𝒱) (w₁ : P₁.carrier) (w₂ : P₂.carrier) =>
      IsIntertwiningOperator.jacR_support_finite (A₁ := P₁.isMod) Y u w₁ w₂ ℓ m n
    set D : 𝒱 → P₁.carrier → P₂.carrier → M₃ := fun u w₁ w₂ =>
      ∑ᶠ i, IsIntertwiningOperator.jacL P₂.isMod A₃ Y u w₁ w₂ ℓ m n i
        - ∑ᶠ i, IsIntertwiningOperator.jacR P₁.isMod Y u w₁ w₂ ℓ m n i with hD
    suffices hz : D u w₁ w₂ = 0 from sub_eq_zero.mp hz
    have hDu : ∀ u u' w₁ w₂, D (u + u') w₁ w₂ = D u w₁ w₂ + D u' w₁ w₂ := by
      intro u u' w₁ w₂
      simp only [hD]
      have e1 : ∀ i, IsIntertwiningOperator.jacL P₂.isMod A₃ Y (u + u') w₁ w₂ ℓ m n i
          = IsIntertwiningOperator.jacL P₂.isMod A₃ Y u w₁ w₂ ℓ m n i
            + IsIntertwiningOperator.jacL P₂.isMod A₃ Y u' w₁ w₂ ℓ m n i := by
        intro i
        simp only [IsIntertwiningOperator.jacL, map_add, mode_add, LinearMap.add_apply]
        module
      have e2 : ∀ i, IsIntertwiningOperator.jacR P₁.isMod Y (u + u') w₁ w₂ ℓ m n i
          = IsIntertwiningOperator.jacR P₁.isMod Y u w₁ w₂ ℓ m n i
            + IsIntertwiningOperator.jacR P₁.isMod Y u' w₁ w₂ ℓ m n i := by
        intro i
        simp only [IsIntertwiningOperator.jacR, map_add, mode_add, LinearMap.add_apply,
          smul_add]
      rw [finsum_congr e1, finsum_congr e2, finsum_add_distrib (hfinL u w₁ w₂) (hfinL u' w₁ w₂),
        finsum_add_distrib (hfinR u w₁ w₂) (hfinR u' w₁ w₂)]
      abel
    have hDw₁ : ∀ u y y' w₂, D u (y + y') w₂ = D u y w₂ + D u y' w₂ := by
      intro u y y' w₂
      simp only [hD]
      have e1 : ∀ i, IsIntertwiningOperator.jacL P₂.isMod A₃ Y u (y + y') w₂ ℓ m n i
          = IsIntertwiningOperator.jacL P₂.isMod A₃ Y u y w₂ ℓ m n i
            + IsIntertwiningOperator.jacL P₂.isMod A₃ Y u y' w₂ ℓ m n i := by
        intro i
        simp only [IsIntertwiningOperator.jacL, map_add, LinearMap.add_apply]
        module
      have e2 : ∀ i, IsIntertwiningOperator.jacR P₁.isMod Y u (y + y') w₂ ℓ m n i
          = IsIntertwiningOperator.jacR P₁.isMod Y u y w₂ ℓ m n i
            + IsIntertwiningOperator.jacR P₁.isMod Y u y' w₂ ℓ m n i := by
        intro i
        simp only [IsIntertwiningOperator.jacR, map_add, LinearMap.add_apply, smul_add]
      rw [finsum_congr e1, finsum_congr e2, finsum_add_distrib (hfinL u y w₂) (hfinL u y' w₂),
        finsum_add_distrib (hfinR u y w₂) (hfinR u y' w₂)]
      abel
    have hDw₂ : ∀ u y z z', D u y (z + z') = D u y z + D u y z' := by
      intro u y z z'
      simp only [hD]
      have e1 : ∀ i, IsIntertwiningOperator.jacL P₂.isMod A₃ Y u y (z + z') ℓ m n i
          = IsIntertwiningOperator.jacL P₂.isMod A₃ Y u y z ℓ m n i
            + IsIntertwiningOperator.jacL P₂.isMod A₃ Y u y z' ℓ m n i := by
        intro i
        simp only [IsIntertwiningOperator.jacL, map_add]
        module
      have e2 : ∀ i, IsIntertwiningOperator.jacR P₁.isMod Y u y (z + z') ℓ m n i
          = IsIntertwiningOperator.jacR P₁.isMod Y u y z ℓ m n i
            + IsIntertwiningOperator.jacR P₁.isMod Y u y z' ℓ m n i := by
        intro i
        simp only [IsIntertwiningOperator.jacR, map_add, smul_add]
      rw [finsum_congr e1, finsum_congr e2, finsum_add_distrib (hfinL u y z) (hfinL u y z'),
        finsum_add_distrib (hfinR u y z) (hfinR u y z')]
      abel
    refine VOA.Huang.FusionC2.induction_grading (W := W)
      (motive := fun u => D u w₁ w₂ = 0) u ?_ ?_ ?_
    · simp only [hD, IsIntertwiningOperator.jacL, IsIntertwiningOperator.jacR, map_zero,
        mode_zero, LinearMap.zero_apply, smul_zero, finsum_zero, sub_self]
    · intro a b ha hb; rw [hDu, ha, hb, add_zero]
    · intro wt a ha
      refine eq_zero_of_homog (fun y z => D a y z) (fun y y' z => hDw₁ a y y' z)
        (fun y z z' => hDw₂ a y z z') (fun α₁ α₂ y z hy hz => ?_) w₁ w₂
      have := hJ wt a ha α₁ α₂ y z hy hz ℓ m n
      simp only [hD]
      rw [sub_eq_zero]
      exact this

end OfHomog

/-! ## `τ`-embeddings and the intertwiner `𝒴₄` -/

/-- A linear map `ψ : R → (P₁ ⊗ P₂)*` into bilinear, lower-truncated, compatible functions that
intertwines the module action of `R` with the Huang–Lepowsky action `τ`. -/
structure TauEmb (R : LWModule W) (ψ : R.carrier →ₗ[ℂ] (HomPair P₁ P₂ → ℂ)) : Prop where
  bil : ∀ r, IsBilin (ψ r)
  act : ∀ (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (k : ℤ) (r : R.carrier),
    ψ (mode (R.isMod.YM u) k r) = tauHom hu k (ψ r)
  trunc : ∀ (r : R.carrier) (γ : ℤ) (a : 𝒱) (ha : a ∈ W.grading γ),
    ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p (ψ r) = 0
  compat : ∀ r, CompatFn (ψ r)

section Y4

variable {R : LWModule W} {ψ : R.carrier →ₗ[ℂ] (HomPair P₁ P₂ → ℂ)}

/-- The functional `r ↦ ψ(r)(a, b)` on the weight space `R_γ`. -/
noncomputable def evalFun (ψ : R.carrier →ₗ[ℂ] (HomPair P₁ P₂ → ℂ)) (γ : ℂ) {α₁ α₂ : ℂ}
    (a : P₁.isMod.weight α₁)
    (b : P₂.isMod.weight α₂) : Module.Dual ℂ (R.isMod.weight γ) where
  toFun r := ψ r.1 ⟨a.1, α₁, b.1, α₂, a.2, b.2⟩
  map_add' r r' := by simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c r := by
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem evalFun_apply (γ : ℂ) {α₁ α₂ : ℂ} (a : P₁.isMod.weight α₁)
    (b : P₂.isMod.weight α₂) (r : R.isMod.weight γ) :
    evalFun ψ γ a b r = ψ r.1 ⟨a.1, α₁, b.1, α₂, a.2, b.2⟩ := rfl

/-- The block of `𝒴₄(·)_n ·` on `P₁(α₁) × P₂(α₂)`: the functional `evalFun` placed in the
weight-`(α₁+α₂−n−1)` slot of `R'`. -/
noncomputable def block4 (hE : TauEmb R ψ) (n : ℂ) (α₁ α₂ : ℂ) :
    P₁.isMod.weight α₁ →ₗ[ℂ] P₂.isMod.weight α₂ →ₗ[ℂ] RestrictedDual R.isMod :=
  LinearMap.mk₂ ℂ
    (fun a b => DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (R.isMod.weight γ))
      (α₁ + α₂ - n - 1) (evalFun ψ (α₁ + α₂ - n - 1) a b))
    (fun a a' b => by
      dsimp only
      have h : evalFun ψ (α₁ + α₂ - n - 1) (a + a') b
          = evalFun ψ (α₁ + α₂ - n - 1) a b + evalFun ψ (α₁ + α₂ - n - 1) a' b := by
        ext r; simp only [evalFun_apply, LinearMap.add_apply]
        exact (hE.bil r.1 α₁ α₂).1 a a' b
      rw [h, map_add]; rfl)
    (fun c a b => by
      dsimp only
      have h : evalFun ψ (α₁ + α₂ - n - 1) (c • a) b = c • evalFun ψ (α₁ + α₂ - n - 1) a b := by
        ext r; simp only [evalFun_apply, LinearMap.smul_apply, smul_eq_mul]
        exact (hE.bil r.1 α₁ α₂).2.1 c a b
      rw [h, map_smul]; rfl)
    (fun a b b' => by
      dsimp only
      have h : evalFun ψ (α₁ + α₂ - n - 1) a (b + b')
          = evalFun ψ (α₁ + α₂ - n - 1) a b + evalFun ψ (α₁ + α₂ - n - 1) a b' := by
        ext r; simp only [evalFun_apply, LinearMap.add_apply]
        exact (hE.bil r.1 α₁ α₂).2.2.1 a b b'
      rw [h, map_add]; rfl)
    (fun c a b => by
      dsimp only
      have h : evalFun ψ (α₁ + α₂ - n - 1) a (c • b) = c • evalFun ψ (α₁ + α₂ - n - 1) a b := by
        ext r; simp only [evalFun_apply, LinearMap.smul_apply, smul_eq_mul]
        exact (hE.bil r.1 α₁ α₂).2.2.2 c a b
      rw [h, map_smul]; rfl)

/-- **The first iterate intertwiner** `𝒴₄ : P₁ ⊗ P₂ → R'{x}`. -/
noncomputable def Y4 (hE : TauEmb R ψ) : IntertwiningModes P₁.carrier P₂.carrier
    (RestrictedDual R.isMod) :=
  fun n => biHat (block4 hE n)

theorem Y4_homog (hE : TauEmb R ψ) (n : ℂ) {α₁ α₂ : ℂ} {y : P₁.carrier} {z : P₂.carrier}
    (hy : y ∈ P₁.isMod.weight α₁) (hz : z ∈ P₂.isMod.weight α₂) :
    Y4 hE n y z = DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (R.isMod.weight γ))
      (α₁ + α₂ - n - 1) (evalFun ψ (α₁ + α₂ - n - 1) ⟨y, hy⟩ ⟨z, hz⟩) := by
  rw [Y4, biHat_homog _ hy hz]
  rfl

/-- **The pairing of `𝒴₄` with `R`.** -/
theorem pair_Y4 (hE : TauEmb R ψ) (n : ℂ) {γ α₁ α₂ : ℂ} {r : R.carrier}
    (hr : r ∈ R.isMod.weight γ) {y : P₁.carrier} {z : P₂.carrier}
    (hy : y ∈ P₁.isMod.weight α₁) (hz : z ∈ P₂.isMod.weight α₂) :
    dualPairing R.isMod r (Y4 hE n y z)
      = if γ = α₁ + α₂ - n - 1 then ψ r ⟨y, α₁, z, α₂, hy, hz⟩ else 0 := by
  rw [Y4_homog hE n hy hz, dualPairing_lof]
  split_ifs with h
  · subst h
    rw [evalFun_apply]
    rw [internalProjTo_coe_mem R.isMod hr]
  · rw [internalProjTo_eq_zero_of_ne R.isMod hr (Ne.symm h), map_zero]

/-! ## The axioms of `𝒴₄` -/

theorem dual_bot_eq_zero {γ : ℂ} (h : R.isMod.weight γ = ⊥) (g : Module.Dual ℂ (R.isMod.weight γ)) :
    g = 0 := by
  ext r
  have hr : (r : R.carrier) = 0 := (Submodule.eq_bot_iff _).mp h r r.2
  have : r = 0 := Subtype.ext hr
  rw [this, map_zero]; rfl

theorem Y4_trunc_homog (hE : TauEmb R ψ) {α₁ α₂ : ℂ} {y : P₁.carrier} {z : P₂.carrier}
    (hy : y ∈ P₁.isMod.weight α₁) (hz : z ∈ P₂.isMod.weight α₂) (n : ℂ) :
    ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y4 hE (n + k) y z = 0 := by
  obtain ⟨B, hB⟩ := R.isMod.boundedBelow
  set c : ℤ := ⌈(α₁ + α₂ - n - 1).re - B⌉ with hc
  have hc' : (α₁ + α₂ - n - 1).re - B ≤ (c : ℝ) := Int.le_ceil _
  refine ⟨c + 1, fun k hk => ?_⟩
  rw [Y4_homog hE (n + k) hy hz]
  have hbot : R.isMod.weight (α₁ + α₂ - (n + k) - 1) = ⊥ := by
    by_contra hne
    have h1 := hB _ hne
    have h3 : ((c + 1 : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at h1 hc'
    push_cast at h3
    linarith
  rw [dual_bot_eq_zero hbot (evalFun ψ (α₁ + α₂ - (n + k) - 1) ⟨y, hy⟩ ⟨z, hz⟩), map_zero]; rfl

theorem Y4_trunc (hE : TauEmb R ψ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n : ℂ) :
    ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y4 hE (n + k) w₁ w₂ = 0 := by
  refine Submodule.iSup_induction P₁.isMod.weight
    (motive := fun w₁ => ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y4 hE (n + k) w₁ w₂ = 0)
    (mem_iSup_weight P₁ w₁) ?_ ⟨0, fun k _ => by simp⟩ ?_
  · intro α₁ y hy
    refine Submodule.iSup_induction P₂.isMod.weight
      (motive := fun w₂ => ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y4 hE (n + k) y w₂ = 0)
      (mem_iSup_weight P₂ w₂) ?_ ⟨0, fun k _ => by simp⟩ ?_
    · intro α₂ z hz; exact Y4_trunc_homog hE hy hz n
    · rintro z z' ⟨N, hN⟩ ⟨N', hN'⟩
      exact ⟨max N N', fun k hk => by
        rw [map_add, hN k (le_trans (le_max_left _ _) hk), hN' k (le_trans (le_max_right _ _) hk),
          add_zero]⟩
  · rintro y y' ⟨N, hN⟩ ⟨N', hN'⟩
    exact ⟨max N N', fun k hk => by
      rw [map_add, LinearMap.add_apply, hN k (le_trans (le_max_left _ _) hk),
        hN' k (le_trans (le_max_right _ _) hk), add_zero]⟩

/-- `L'(0) ψ(r) = γ ψ(r)` for `r ∈ R_γ`. -/
theorem L0T_psi (hE : TauEmb R ψ) {γ : ℂ} {r : R.carrier} (hr : r ∈ R.isMod.weight γ) :
    L0T P₁ P₂ (ψ r) = γ • ψ r := by
  have h := hE.act 2 W.conformalVector W.conformalVector_mem_grading_two 1 r
  rw [tauHom_conformal_one (hE.bil r), R.isMod.L0_weight γ r hr, map_smul] at h
  exact h.symm

theorem Y4_L_homog (hE : TauEmb R ψ) {α₁ α₂ : ℂ} {y : P₁.carrier} {z : P₂.carrier}
    (hy : y ∈ P₁.isMod.weight α₁) (hz : z ∈ P₂.isMod.weight α₂) (n : ℂ) :
    Y4 hE n (P₁.isMod.Lm1 y) z = (-n) • Y4 hE (n - 1) y z := by
  refine restrictedDual_ext_of_pairing R.isMod fun γ r hr => ?_
  rw [map_smul, smul_eq_mul, pair_Y4 hE n hr (Lm1_mem_weight' P₁.isMod hy) hz,
    pair_Y4 hE (n - 1) hr hy hz]
  have hc : (γ = α₁ + 1 + α₂ - n - 1) ↔ (γ = α₁ + α₂ - (n - 1) - 1) := by
    constructor <;> intro h <;> rw [h] <;> ring
  by_cases h : γ = α₁ + α₂ - (n - 1) - 1
  · rw [if_pos (hc.mpr h), if_pos h]
    have hL := congrFun (L0T_psi hE hr) ⟨y, α₁, z, α₂, hy, hz⟩
    rw [L0T_apply, Pi.smul_apply, smul_eq_mul] at hL
    have hx : ψ r (HomPair.lm1 ⟨y, α₁, z, α₂, hy, hz⟩)
        = ψ r ⟨P₁.isMod.Lm1 y, α₁ + 1, z, α₂, Lm1_mem_weight' P₁.isMod hy, hz⟩ := rfl
    rw [← hx]
    simp only at hL
    rw [h] at hL
    linear_combination hL
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, mul_zero]

/-- The contragredient modes of `R'` paired with `R`. -/
theorem pair_mode {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (k : ℤ)
    (r : R.carrier) (φ : RestrictedDual R.isMod) :
    dualPairing R.isMod r (mode ((contragredientModule R.isMod).YM u) k φ)
      = (-1 : ℂ) ^ wt * ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) *
          dualPairing R.isMod (mode (R.isMod.YM ((W.L 1 ^ j) u)) (2 * wt - k - 2 - (j : ℤ)) r)
            φ := by
  change dualPairing R.isMod r (mode (YMdual R.isMod u) k φ) = _
  rw [mode_YMdual_homogeneous R.isMod hu]
  exact dualPairing_dualModeEndo R.isMod hu k φ r

/-- **The contragredient action on `𝒴₄` is the transposed coproduct** (double twist). -/
theorem pair_mode_Y4 (hE : TauEmb R ψ) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (k : ℤ)
    (n : ℂ) {γ α₁ α₂ : ℂ} {r : R.carrier} (hr : r ∈ R.isMod.weight γ) {y : P₁.carrier}
    {z : P₂.carrier} (hy : y ∈ P₁.isMod.weight α₁) (hz : z ∈ P₂.isMod.weight α₂) :
    dualPairing R.isMod r (mode ((contragredientModule R.isMod).YM u) k (Y4 hE n y z))
      = if γ - wt + k + 1 = α₁ + α₂ - n - 1 then copT hu k (ψ r) ⟨y, α₁, z, α₂, hy, hz⟩
        else 0 := by
  rw [pair_mode hu k r]
  have hj : ∀ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) *
      dualPairing R.isMod (mode (R.isMod.YM ((W.L 1 ^ j) u)) (2 * wt - k - 2 - (j : ℤ)) r)
        (Y4 hE n y z)
      = if γ - wt + k + 1 = α₁ + α₂ - n - 1 then ((j.factorial : ℂ)⁻¹) *
          tauHom (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) (2 * wt - k - 2 - (j : ℤ))
            (ψ r) ⟨y, α₁, z, α₂, hy, hz⟩ else 0 := by
    intro j _
    have hmem := VOA.mode_mem_weight R.isMod (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) hr
      (2 * wt - k - 2 - (j : ℤ))
    have e : γ + (((wt - (j : ℤ)) : ℤ) : ℂ) - (((2 * wt - k - 2 - (j : ℤ)) : ℤ) : ℂ) - 1
        = γ - wt + k + 1 := by push_cast; ring
    rw [e] at hmem
    rw [pair_Y4 hE n hmem hy hz, hE.act _ _ (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hj]
  split_ifs with h
  · rw [← twist_twist_fn (hE.bil r) hu k ⟨y, α₁, z, α₂, hy, hz⟩]
  · simp

/-- **The Jacobi identity of `𝒴₄`** on homogeneous data: it is the compatibility slice. -/
theorem Y4_jac_homog (hE : TauEmb R ψ) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    {α₁ α₂ : ℂ} {y : P₁.carrier} {z : P₂.carrier} (hy : y ∈ P₁.isMod.weight α₁)
    (hz : z ∈ P₂.isMod.weight α₂) (ℓ m : ℤ) (n : ℂ) :
    JacAt (contragredientModule R.isMod) (Y4 hE) u y z ℓ m n := by
  unfold JacAt
  refine restrictedDual_ext_of_pairing R.isMod fun γ r hr => ?_
  have hfinL := IsIntertwiningOperator.jacL_support_finite (A₂ := P₂.isMod)
    (A₃ := contragredientModule R.isMod) (Y4_trunc hE) u y z ℓ m n
  have hfinR := IsIntertwiningOperator.jacR_support_finite (A₁ := P₁.isMod) (Y4 hE) u y z ℓ m n
  change dualPairing R.isMod r (∑ᶠ i, IsIntertwiningOperator.jacL P₂.isMod
      (contragredientModule R.isMod) (Y4 hE) u y z ℓ m n i)
    = dualPairing R.isMod r (∑ᶠ i, IsIntertwiningOperator.jacR P₁.isMod (Y4 hE) u y z ℓ m n i)
  rw [map_finsum (dualPairing R.isMod r) hfinL, map_finsum (dualPairing R.isMod r) hfinR]
  set x : HomPair P₁ P₂ := ⟨y, α₁, z, α₂, hy, hz⟩ with hx
  set γ₀ : ℂ := α₁ + α₂ + wt - ℓ - m - n - 2 with hγ₀
  have hL : ∀ i : ℤ, dualPairing R.isMod r (IsIntertwiningOperator.jacL P₂.isMod
      (contragredientModule R.isMod) (Y4 hE) u y z ℓ m n i)
      = if γ = γ₀ then (negOnePow i * cbz ℓ i) * (copT hu (ℓ + m - i) (ψ r) x
          - negOnePow ℓ * ψ r (pairRight x hu (m + i))) else 0 := by
    intro i
    simp only [IsIntertwiningOperator.jacL, map_smul, map_sub, smul_eq_mul]
    rw [pair_mode_Y4 hE hu (ℓ + m - i) (n + i) hr hy hz,
      pair_Y4 hE (ℓ + n - i) hr hy (VOA.mode_mem_weight P₂.isMod hu hz (m + i))]
    have c1 : (γ - wt + ((ℓ + m - i : ℤ) : ℂ) + 1 = α₁ + α₂ - (n + i) - 1) ↔ γ = γ₀ := by
      rw [hγ₀]; push_cast; constructor <;> intro h <;> linear_combination h
    have c2 : (γ = α₁ + (α₂ + wt - ((m + i : ℤ) : ℂ) - 1) - ((ℓ : ℂ) + n - (i : ℂ)) - 1)
        ↔ γ = γ₀ := by
      rw [hγ₀]; push_cast; constructor <;> intro h <;> linear_combination h
    by_cases h : γ = γ₀
    · rw [if_pos (c1.mpr h), if_pos (c2.mpr h), if_pos h]; rfl
    · rw [if_neg (fun h' => h (c1.mp h')), if_neg (fun h' => h (c2.mp h')), if_neg h]; ring
  have hR : ∀ i : ℤ, dualPairing R.isMod r (IsIntertwiningOperator.jacR P₁.isMod (Y4 hE) u y z
      ℓ m n i) = if γ = γ₀ then cbz m i * ψ r (pairLeft x hu (ℓ + i)) else 0 := by
    intro i
    simp only [IsIntertwiningOperator.jacR, map_smul, smul_eq_mul]
    rw [pair_Y4 hE (m + n - i) hr (VOA.mode_mem_weight P₁.isMod hu hy (ℓ + i)) hz]
    have c3 : (γ = α₁ + wt - ((ℓ + i : ℤ) : ℂ) - 1 + α₂ - (m + n - i) - 1) ↔ γ = γ₀ := by
      rw [hγ₀]; push_cast; constructor <;> intro h <;> linear_combination h
    by_cases h : γ = γ₀
    · rw [if_pos (c3.mpr h), if_pos h]; rfl
    · rw [if_neg (fun h' => h (c3.mp h')), if_neg h, mul_zero]
  rw [finsum_congr hL, finsum_congr hR]
  by_cases h : γ = γ₀
  · simp only [if_pos h]
    -- the compatibility slice `(m, ℓ)` for `ψ r`
    have hs := slice_fn (hE.bil r) (hE.trunc r) (hE.compat r) hu m ℓ x
    obtain ⟨Pt, hPt⟩ := hE.trunc r wt u hu
    obtain ⟨N₂, hN₂⟩ := P₂.isMod.truncation u z
    set K : ℤ := max (ℓ + m - Pt) (N₂ - m) with hK
    have f1 : Function.HasFiniteSupport fun i : ℤ =>
        (negOnePow i * cbz ℓ i) * copT hu (m + ℓ - i) (ψ r) x :=
      hfs_of _ 0 K fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · rw [hPt _ (by omega)]; simp
    have f2 : Function.HasFiniteSupport fun i : ℤ =>
        (cbz ℓ i * negOnePow (ℓ - i)) * ψ r (pairRight x hu (m + i)) :=
      hfs_of _ 0 K fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · rw [(hE.bil r).zero_right _ (by
            change mode (P₂.isMod.YM u) (m + i) z = 0; exact hN₂ _ (by omega))]; ring
    have e : ∀ i : ℤ, (negOnePow i * cbz ℓ i) * (copT hu (ℓ + m - i) (ψ r) x
        - negOnePow ℓ * ψ r (pairRight x hu (m + i)))
        = (negOnePow i * cbz ℓ i) * copT hu (m + ℓ - i) (ψ r) x
          - (cbz ℓ i * negOnePow (ℓ - i)) * ψ r (pairRight x hu (m + i)) := by
      intro i
      have hsg : negOnePow i * negOnePow ℓ = negOnePow (ℓ - i) := by
        rw [← negOnePow_add, show i + ℓ = (ℓ - i) + 2 * i by ring, negOnePow_add]
        have : negOnePow (2 * i) = 1 := by
          unfold negOnePow; rw [if_pos (even_two_mul i)]
        rw [this, mul_one]
      rw [show m + ℓ - i = ℓ + m - i by ring]
      linear_combination (-(cbz ℓ i * ψ r (pairRight x hu (m + i)))) * hsg
    rw [finsum_congr e, finsum_sub_distrib f1 f2, hs]
    ring
  · simp only [if_neg h, finsum_zero]

/-- **`𝒴₄` is an intertwining operator of type `(R' / P₁ P₂)`.** -/
theorem isIntertwining_Y4 (hE : TauEmb R ψ) :
    IsIntertwiningOperator P₁.isMod P₂.isMod (contraLW R).isMod (Y4 hE) :=
  isIntertwining_of_homog (Y4_trunc hE) (fun _ _ _ _ hy hz n => Y4_L_homog hE hy hz n)
    (fun _ _ hu _ _ _ _ hy hz ℓ m n => Y4_jac_homog hE hu hy hz ℓ m n)

end Y4

end VOA.Huang.PzTensorY4
