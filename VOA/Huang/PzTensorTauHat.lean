/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorRhoJacobi
import VOA.Huang.PzTensorTwist

/-!
# The twisted `P(1)`-action on compatible forms satisfies the Jacobi identity

The Huang–Lepowsky action is the contragredient twist of the transposed coproduct:

`τ̂(u, k) β = (−1)^{wt u} Σ_j (1/j!) ρ(L₁ʲu, 2 wt u − k − 2 − j) β`

(`tauHat`; this is `PzTensorAction.tauHom` on honest bilinear forms).  Combining

* the reversed Jacobi identity for `ρ` on compatible lower-truncated forms
  (`PzTensorRho.rho_jacobi_pt`, all `(ℓ, m, n)`), applied to every pair of `L₁`-tower states, and
* the contragredient-twist identity for the translation-covariant family `k ↦ ρ(·, k)β(y₁,y₂)`
  (`PzTensorTwist.rhs_gen_eqT`, the module FHL computation transported from the library),

gives `tauHat_jacobi_pt`: **the honest Borcherds identity for `τ̂`** on every bilinear form
that is lower truncated and compatible for all homogeneous states (HLZ IV Thm. 5.44, `z = 1`).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorRho

open VOA VOA.Huang.PzTensorTwist
open scoped BigOperators

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v} [AddCommGroup M₁] [Module ℂ M₁]
variable {M₂ : Type w} [AddCommGroup M₂] [Module ℂ M₂]

section TauHat

variable (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)

/-- `ρ(·, k)β(y₁, y₂)` as a translation-covariant family of functionals of the states. -/
noncomputable def rhoFam (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) : Fam W ℂ :=
  fun k => rhoState A₁ A₂ k β y₁ y₂

theorem rhoFam_transCov (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    TransCov (rhoFam A₁ A₂ β y₁ y₂) := fun k g => by
  simp only [rhoFam, rhoState_apply, smul_eq_mul]
  exact rhoL_translation A₁ A₂ g k β y₁ y₂

/-- **The twisted (Huang–Lepowsky) action** `τ̂(u,k)`, for `u` of weight `wt`. -/
noncomputable def tauHat (wt : ℤ) (u : 𝒱) (k : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    rhoL A₁ A₂ ((W.L 1 ^ j) u) (2 * wt - k - 2 - (j : ℤ)) β

theorem tauHat_apply (wt : ℤ) (u : 𝒱) (k : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    tauHat A₁ A₂ wt u k β y₁ y₂ = adj (rhoFam A₁ A₂ β y₁ y₂) wt u k := by
  simp only [tauHat, adj, rhoFam, rhoState_apply, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, smul_eq_mul]

/-- The nested twisted action as a double `L₁`-tower of `ρ ρ`. -/
theorem tauHat_tauHat (p q : ℤ) (u v : 𝒱) (k₁ k₂ : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁)
    (y₂ : M₂) :
    tauHat A₁ A₂ p u k₁ (tauHat A₁ A₂ q v k₂ β) y₁ y₂
      = (-1 : ℂ) ^ (p + q) * ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
          ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹)
            * rhoL A₁ A₂ ((W.L 1 ^ a) u) (2 * p - k₁ - 2 - (a : ℤ))
                (rhoL A₁ A₂ ((W.L 1 ^ b) v) (2 * q - k₂ - 2 - (b : ℤ)) β) y₁ y₂ := by
  simp only [tauHat, map_smul, map_sum, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

/-- The `(a,b)`-block of the nested `τ̂ τ̂` Borcherds sum. -/
noncomputable def blk (u v : 𝒱) (p q ℓ m n : ℤ) (a b : ℕ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ)
    (y₁ : M₁) (y₂ : M₂) (i : ℤ) : ℂ :=
  (negOnePow i * cbz ℓ i)
    * (rhoL A₁ A₂ ((W.L 1 ^ a) u) (2 * p - (ℓ + m - i) - 2 - (a : ℤ))
          (rhoL A₁ A₂ ((W.L 1 ^ b) v) (2 * q - (n + i) - 2 - (b : ℤ)) β) y₁ y₂
      - negOnePow ℓ * rhoL A₁ A₂ ((W.L 1 ^ b) v) (2 * q - (ℓ + n - i) - 2 - (b : ℤ))
          (rhoL A₁ A₂ ((W.L 1 ^ a) u) (2 * p - (m + i) - 2 - (a : ℤ)) β) y₁ y₂)

theorem blk_fin {u v : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (p q ℓ m n : ℤ) (a b : ℕ)
    (hta : TruncAt A₁ A₂ ((W.L 1 ^ a) u) β) (htb : TruncAt A₁ A₂ ((W.L 1 ^ b) v) β)
    (y₁ : M₁) (y₂ : M₂) :
    Function.HasFiniteSupport (blk A₁ A₂ u v p q ℓ m n a b β y₁ y₂) := by
  obtain ⟨Pa, hPa⟩ := hta
  obtain ⟨Pb, hPb⟩ := htb
  refine hfs_of _ 0 (max (2 * q - n - 2 - (b : ℤ) - Pb) (2 * p - m - 2 - (a : ℤ) - Pa)) ?_
  intro i hi
  simp only [blk]
  rcases hi with hi | hi
  · rw [cbz_neg hi]; ring
  · rw [hPb _ (by omega), hPa _ (by omega)]; simp

theorem hfs_const_mul {f : ℤ → ℂ} (c : ℂ) (h : Function.HasFiniteSupport f) :
    Function.HasFiniteSupport (fun i => c * f i) :=
  Set.Finite.subset h fun i hi => by
    simp only [Function.mem_support] at hi ⊢
    intro h0; exact hi (by rw [h0, mul_zero])

/-- **The Borcherds identity for the twisted action `τ̂`** (honest order, all `ℓ, m, n`) on
every form that is lower truncated and compatible for all homogeneous states. -/
theorem tauHat_jacobi_pt {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ}
    (hT : ∀ (c : 𝒱) (γ : ℤ), c ∈ W.grading γ → TruncAt A₁ A₂ c β)
    (hC : ∀ (c : 𝒱) (γ : ℤ), c ∈ W.grading γ → CompatAt A₁ A₂ c β)
    {p q : ℤ} {u v : 𝒱} (hu : u ∈ W.grading p) (hv : v ∈ W.grading q) (ℓ m n : ℤ)
    (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ i, (negOnePow i * cbz ℓ i)
        * (tauHat A₁ A₂ p u (ℓ + m - i) (tauHat A₁ A₂ q v (n + i) β) y₁ y₂
          - negOnePow ℓ * tauHat A₁ A₂ q v (ℓ + n - i) (tauHat A₁ A₂ p u (m + i) β) y₁ y₂)
      = ∑ᶠ i, cbz m i
          * tauHat A₁ A₂ (p + q - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) β y₁ y₂ := by
  have hau : ∀ a : ℕ, (W.L 1 ^ a) u ∈ W.grading (p - (a : ℤ)) := fun a =>
    VOA.VertexOperatorAlgebra.L_one_pow_mem W hu a
  have hbv : ∀ b : ℕ, (W.L 1 ^ b) v ∈ W.grading (q - (b : ℤ)) := fun b =>
    VOA.VertexOperatorAlgebra.L_one_pow_mem W hv b
  -- right-hand side: the contragredient-twist identity
  have hR : ∑ᶠ i, cbz m i
        * tauHat A₁ A₂ (p + q - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) β y₁ y₂
      = (-1 : ℂ) ^ (p + q) *
          ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
            ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) *
              ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i *
                rhoL A₁ A₂ (W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u))
                  ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) β y₁ y₂ := by
    have h := rhs_gen_eqT (rhoFam A₁ A₂ β y₁ y₂) (rhoFam_transCov A₁ A₂ β y₁ y₂) hu hv ℓ m n
    simp only [smul_eq_mul] at h
    simp only [tauHat_apply]
    rw [h]
    simp only [rhoFam, rhoState_apply]
  rw [hR]
  -- left-hand side: expand into `(a,b)`-blocks
  have hL : ∀ i, (negOnePow i * cbz ℓ i)
        * (tauHat A₁ A₂ p u (ℓ + m - i) (tauHat A₁ A₂ q v (n + i) β) y₁ y₂
          - negOnePow ℓ * tauHat A₁ A₂ q v (ℓ + n - i) (tauHat A₁ A₂ p u (m + i) β) y₁ y₂)
      = (-1 : ℂ) ^ (p + q) * ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
          ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * blk A₁ A₂ u v p q ℓ m n a b β y₁ y₂ i := by
    intro i
    rw [tauHat_tauHat, tauHat_tauHat, show q + p = p + q by ring]
    rw [Finset.sum_comm (s := Finset.range (p.toNat + 1)) (t := Finset.range (q.toNat + 1))]
    simp only [blk, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [finsum_congr hL, ← mul_finsum]
  congr 1
  rw [finsum_sum_comm _ _ (fun b _ => hasFiniteSupport_finsetSum _ _ (fun a _ =>
      hfs_const_mul _ (blk_fin A₁ A₂ p q ℓ m n a b (hT _ _ (hau a)) (hT _ _ (hbv b)) y₁ y₂)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [finsum_sum_comm _ _ (fun a _ =>
      hfs_const_mul _ (blk_fin A₁ A₂ p q ℓ m n a b (hT _ _ (hau a)) (hT _ _ (hbv b)) y₁ y₂))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_finsum]
  congr 1
  -- per block: the reversed Jacobi identity for `ρ`
  have hJ := rho_jacobi_pt A₁ A₂ (hT _ _ (hbv b)) (hT _ _ (hau a)) (hC _ _ (hbv b))
    (hC _ _ (hau a)) ℓ (2 * q - ℓ - n - 2 - (b : ℤ)) (2 * p - ℓ - m - 2 - (a : ℤ)) y₁ y₂
  rw [← hJ]
  refine finsum_congr fun i => ?_
  simp only [blk]
  rw [show 2 * p - (ℓ + m - i) - 2 - (a : ℤ) = 2 * p - ℓ - m - 2 - (a : ℤ) + i by ring,
    show 2 * q - (n + i) - 2 - (b : ℤ) = ℓ + (2 * q - ℓ - n - 2 - (b : ℤ)) - i by ring,
    show 2 * q - (ℓ + n - i) - 2 - (b : ℤ) = 2 * q - ℓ - n - 2 - (b : ℤ) + i by ring,
    show 2 * p - (m + i) - 2 - (a : ℤ) = ℓ + (2 * p - ℓ - m - 2 - (a : ℤ)) - i by ring]

end TauHat

end VOA.Huang.PzTensorRho
