/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangModularitySymm

/-!
# Complex conjugation of Zhu's `S`-matrix is charge conjugation

For a nice VOA with modular data `D` and charge conjugation `σ` (`HuangModularity.exists_charge`),
we prove `S_{σa, b} = conj S_{ab}` (`S_charge_eq_star`).  No unitarity of `S` is assumed or used:
the identity is derived by finite linear algebra from

* the fusion eigenvector property of the columns of `S` (Huang's Theorem 5.2),
* `S² = C` with `C` the permutation matrix of the involution `σ`,
* Zhu's relation `T S T S T = S` (`S_TSTST`),
* the balancing identity `balancing_S` (from Huang's categorical balancing), complex-conjugated
  using `|e^{2πih}| = 1` and the reality of `S₀₀`, `d_a`.

This is the identity that matches Zhu's `ρ(S)` with the Ng–Schauenburg categorical `S`
(whose first index carries a dual): see `ZhuRepModel`.
-/

noncomputable section

namespace VOA.Huang.ZhuRep

open VOA VOA.Classification.COne VOA.Huang.HuangModularity VOA.Huang.VerlindeEigen Matrix

section Algebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Matrix core: from `S² = C`, `C² = 1` and `T S T S T = μ S`, `T` commutes with `C` and
`S T⁻¹ S = μ⁻¹ T S C T`. -/
theorem matrix_core (S C T Ti : Matrix ι ι ℂ) (μ : ℂ) (hμ : μ ≠ 0) (hSC : S * S = C)
    (hC2 : C * C = 1) (hTTi : T * Ti = 1) (hTiT : Ti * T = 1)
    (hTST : T * S * T * S * T = μ • S) :
    T * C = C * T ∧ S * Ti * S = μ⁻¹ • (T * S * C * T) := by
  have hSCcomm : S * C = C * S := by rw [← hSC, Matrix.mul_assoc]
  have hSinv : S * (S * C) = 1 := by rw [← Matrix.mul_assoc, hSC, hC2]
  have hP3 : (T * S) * (T * S) * (T * S) = μ • C := by
    calc _ = (T * S * T * S * T) * S := by simp only [Matrix.mul_assoc]
      _ = μ • C := by rw [hTST, Matrix.smul_mul, hSC]
  have hPC : (T * S) * C = C * (T * S) := by
    have h4 : (T * S) * ((T * S) * (T * S) * (T * S)) =
        ((T * S) * (T * S) * (T * S)) * (T * S) := by simp only [Matrix.mul_assoc]
    rw [hP3, Matrix.mul_smul, Matrix.smul_mul] at h4
    exact smul_right_injective _ hμ h4
  have hTC : T * C = C * T := by
    have h1 : (T * C) * S = (C * T) * S := by
      calc (T * C) * S = (T * S) * C := by rw [Matrix.mul_assoc, ← hSCcomm, Matrix.mul_assoc]
        _ = C * (T * S) := hPC
        _ = (C * T) * S := by rw [Matrix.mul_assoc]
    calc T * C = (T * C) * (S * (S * C)) := by rw [hSinv, Matrix.mul_one]
      _ = ((T * C) * S) * (S * C) := by simp only [Matrix.mul_assoc]
      _ = ((C * T) * S) * (S * C) := by rw [h1]
      _ = C * T := by simp only [Matrix.mul_assoc]; rw [hSinv, Matrix.mul_one]
  refine ⟨hTC, ?_⟩
  have hY : S * T * S = μ • (Ti * S * Ti) := by
    calc S * T * S = Ti * (T * S * T * S * T) * Ti := by
          simp only [← Matrix.mul_assoc, hTiT, Matrix.one_mul]
          simp only [Matrix.mul_assoc, hTTi, Matrix.mul_one]
      _ = μ • (Ti * S * Ti) := by
          rw [hTST, Matrix.mul_smul, Matrix.smul_mul]
  have hTiC : Ti * C = C * Ti := by
    calc Ti * C = Ti * C * (T * Ti) := by rw [hTTi, Matrix.mul_one]
      _ = Ti * (C * T) * Ti := by simp only [Matrix.mul_assoc]
      _ = Ti * (T * C) * Ti := by rw [hTC]
      _ = C * Ti := by rw [← Matrix.mul_assoc, hTiT, Matrix.one_mul]
  have hXY : (S * Ti * S) * (S * T * S) = 1 := by
    calc (S * Ti * S) * (S * T * S) = S * (Ti * (S * S)) * T * S := by
          simp only [Matrix.mul_assoc]
      _ = S * (C * Ti) * T * S := by rw [hSC, hTiC]
      _ = (S * C) * (Ti * T) * S := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTiT, Matrix.mul_one, hSCcomm, Matrix.mul_assoc, hSC, hC2]
  have hYZ : (S * T * S) * (μ⁻¹ • (T * S * C * T)) = 1 := by
    rw [hY, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hμ, one_smul]
    calc Ti * S * Ti * (T * S * C * T) = Ti * S * (Ti * T) * S * C * T := by
          simp only [Matrix.mul_assoc]
      _ = Ti * (S * S) * C * T := by rw [hTiT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSC, Matrix.mul_assoc Ti, hC2, Matrix.mul_one, hTiT]
  calc S * Ti * S = (S * Ti * S) * ((S * T * S) * (μ⁻¹ • (T * S * C * T))) := by
        rw [hYZ, Matrix.mul_one]
    _ = μ⁻¹ • (T * S * C * T) := by rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]

/-- **Abstract form.** Under the eigenvector, `S² = C`, `TSTST = μ S` and conjugated balancing
hypotheses, `S_{a, σb} = conj S_{ab}`. -/
theorem star_S_eq_of_balancing {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} {v0 : ι} (σ : ι → ι)
    (t : ι → ℂ) (μ : ℂ) (hμ : μ ≠ 0) (ht : ∀ x, t x ≠ 0)
    (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0) (hE : FusionEigen N S)
    (hsym : ∀ a b, S a b = S b a) (hσ : ∀ x, σ (σ x) = x) (hσ0 : σ v0 = v0) (ht0 : t v0 = 1)
    (hSC : Matrix.of S * Matrix.of S = Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0)
    (hTST : ∀ a b, t a * (∑ c, S a c * t c * S c b) * t b = μ * S a b)
    (hbal : ∀ a b, ∑ c, (N a b c : ℂ) * (t c * S c v0) = t a * t b * star (S a b))
    (a b : ι) : star (S a b) = S a (σ b) := by
  have hC2 : (Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0) *
      (Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0) = 1 := by
    ext x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ x)]
    · simp only [Matrix.of_apply, if_true, one_mul, Matrix.one_apply, hσ]
      by_cases h : x = y
      · subst h; simp
      · rw [if_neg (fun h' => h h'.symm), if_neg h]
    · intro k _ hk
      rw [Matrix.of_apply, Matrix.of_apply, if_neg hk, zero_mul]
    · simp
  have hTTi : Matrix.diagonal t * Matrix.diagonal (fun x => (t x)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext x; exact mul_inv_cancel₀ (ht x)
  have hTiT : Matrix.diagonal (fun x => (t x)⁻¹) * Matrix.diagonal t = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext x; exact inv_mul_cancel₀ (ht x)
  have hTSTm : Matrix.diagonal t * Matrix.of S * Matrix.diagonal t * Matrix.of S *
      Matrix.diagonal t = μ • Matrix.of S := by
    ext x y
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      ← hTST x y, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply]
    ring
  obtain ⟨-, hX⟩ := matrix_core _ _ _ _ μ hμ hSC hC2 hTTi hTiT hTSTm
  have hXe : ∀ x y, ∑ c, S x c * (t c)⁻¹ * S c y = μ⁻¹ * (t x * S x (σ y) * t y) := by
    intro x y
    have := congrFun (congrFun hX x) y
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal,
      Matrix.mul_apply] at this
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply] at this
    rw [this]
    congr 1
    rw [Finset.sum_eq_single (σ y)]
    · rw [if_pos (hσ y).symm]; ring
    · intro k _ hk
      rw [if_neg (fun h => hk (by rw [h, hσ]))]; ring
    · simp
  -- the key identity `Σ_c N_ab^c t_c S_{c,0} = t_a t_b S_{a,σb}`
  have hkey : ∑ c, (N a b c : ℂ) * (t c * S c v0) = t a * t b * S a (σ b) := by
    have hw : ∀ c, t c * S c v0 = ∑ x, S c x * (μ * (t x)⁻¹ * S x v0) := by
      intro c
      have h := hXe c v0
      rw [hσ0, ht0, mul_one] at h
      calc t c * S c v0 = μ * (μ⁻¹ * (t c * S c v0)) := by field_simp
        _ = μ * ∑ x, S c x * (t x)⁻¹ * S x v0 := by rw [h]
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    simp_rw [hw, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hev : ∀ x, ∑ c, (N a b c : ℂ) * (S c x * (μ * (t x)⁻¹ * S x v0)) =
        μ * (S a x * (t x)⁻¹ * S x b) := by
      intro x
      have h1 := eigval_spec hE a x b
      have h2 := eq_eigval_mul hunit hE a x
      calc ∑ c, (N a b c : ℂ) * (S c x * (μ * (t x)⁻¹ * S x v0)) =
              (∑ c, (N a b c : ℂ) * S c x) * (μ * (t x)⁻¹ * S x v0) := by
              rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
        _ = μ * ((eigval hE a x * S v0 x) * (t x)⁻¹ * S x b) := by
              rw [h1, hsym x v0, hsym b x]; ring
        _ = _ := by rw [← h2]
    rw [Finset.sum_congr rfl fun x _ => hev x, ← Finset.mul_sum, hXe a b]
    field_simp
  have h := (hbal a b).symm.trans hkey
  have hne : t a * t b ≠ 0 := mul_ne_zero (ht a) (ht b)
  exact mul_left_cancel₀ hne h

end Algebra

section VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Charge conjugation is complex conjugation on Zhu's `S`**: with the charge conjugation
`σ` of `exists_charge`, `S_{σa, b} = conj S_{ab}` for every nice VOA. -/
theorem exists_charge_star (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) :
    ∃ σ : D.ι → D.ι, (∀ x, σ (σ x) = x) ∧
      (∀ b x, fus D b x D.vac = if x = σ b then 1 else 0) ∧
      Matrix.of D.S * Matrix.of D.S = (Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0) ∧
      ∀ a b, D.S (σ a) b = star (D.S a b) := by
  obtain ⟨σ, hσ, hvac, hSC⟩ := exists_charge hW D hD
  refine ⟨σ, hσ, hvac, hSC, ?_⟩
  obtain ⟨hE, hunit, hrel⟩ := zhu_facts hW D hD
  have hsym := S_symm hW D hD
  have hσ0 : σ D.vac = D.vac := by
    have h1 := hvac D.vac D.vac
    have h2 : fus D D.vac D.vac D.vac = 1 := by
      rw [hunit]; simp
    rw [h2] at h1
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h1
    exact one_ne_zero h1
  set t : D.ι → ℂ := fun x => twistOf (D.h x : ℂ) with htdef
  set κ := modularTEntry W (0 : ℂ) with hκ
  have hκ0 : κ ≠ 0 := modularTEntry_ne_zero _
  have ht : ∀ x, t x ≠ 0 := fun x => Complex.exp_ne_zero _
  have ht0 : t D.vac = 1 := by simp [htdef, twistOf, hD.h_vac]
  have hstar : ∀ x, star (t x) = (t x)⁻¹ := fun x => by
    have := star_twistOf ((D.h x : ℚ) : ℝ)
    simpa [htdef] using this
  have hTST : ∀ a b, t a * (∑ c, D.S a c * t c * D.S c b) * t b = (κ ^ 3)⁻¹ * D.S a b := by
    intro a b
    have h := hrel a b
    have e : ∀ x : D.ι, modularTEntry W (D.h x : ℂ) = t x * κ := fun x => modularTEntry_eq _
    simp only [e] at h
    rw [← h]
    have hk3 : κ ^ 3 ≠ 0 := pow_ne_zero 3 hκ0
    field_simp
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hbal : ∀ a b, ∑ c, (fus D a b c : ℂ) * (t c * D.S c D.vac) =
      t a * t b * star (D.S a b) := by
    intro a b
    have h := congrArg star (balancing_S hW D hD hsym a b)
    simp only [star_mul', star_sum, star_natCast, star_inv₀, Complex.star_def,
      Complex.conj_ofReal] at h
    simp only [← Complex.star_def] at h
    have hst : ∀ x, star (twistOf ((D.h x : ℚ) : ℂ)) = (t x)⁻¹ := fun x => hstar x
    simp only [hst, inv_inv] at h
    have hS : ∀ c, D.S c D.vac = (D.S00 : ℂ) * (D.d c : ℂ) := fun c => hD.S_vac_right c
    simp_rw [hS]
    have hL : ∑ c, (fus D a b c : ℂ) * (t c * ((D.S00 : ℂ) * (D.d c : ℂ))) =
        (D.S00 : ℂ) * ∑ c, (fus D a b c : ℂ) * (t c * (D.d c : ℂ)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [hL, h]
  have hmain := star_S_eq_of_balancing σ t (κ ^ 3)⁻¹ (inv_ne_zero (pow_ne_zero 3 hκ0)) ht hunit
    hE hsym hσ hσ0 ht0 hSC hTST hbal
  intro a b
  rw [hsym, ← hmain b a, hsym]

end VOA

end VOA.Huang.ZhuRep
