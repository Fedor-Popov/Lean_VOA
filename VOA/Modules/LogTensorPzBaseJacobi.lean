/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzBaseModes
import VOA.Huang.PzTensorY4

/-! # Jacobi for the actual zeroth modes of a generalized compatible map

The matrix-coefficient construction uses generalized weight spaces throughout.
Its full Jacobi identity follows from compatibility and the genuine double
contragredient twist, without semisimplicity of any L(0) action.
-/

namespace VOA.LogTensor.Pz
open Module (End Dual)
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ R : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup R] [Module ℂ R]
variable {N₁ : LogVModule W M₁} {N₂ : LogVModule W M₂} {N : LogVModule W R}
variable {psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂)}

private theorem pair_contra_mode {d : ℤ} {u : V} (hu : u ∈ W.grading d)
    (p : ℤ) {c : ℂ} {r : R} (hr : r ∈ N.weight c) (f : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW r (mode ((C2Rigid.contragredientModule N.toGW).YM u) p f) =
      (-1:ℂ)^d * ∑ j ∈ Finset.range (d.toNat+1), (j.factorial:ℂ)⁻¹ *
        C2Rigid.dualPairing N.toGW (mode (N.YM ((W.L 1 ^ j) u)) (2*d-p-2-j) r) f := by
  change C2Rigid.dualPairing N.toGW r (mode (C2Rigid.YMdual N.toGW u) p f) = _
  rw [C2Rigid.dualPairing_mode_dualAdj N.toGW hu p f hr,
    C2Rigid.dualAdj_clean N.toGW hu p hr]
  change C2Rigid.dualPairingFlip N.toGW f
    ((-1:ℂ)^d • ∑ j ∈ Finset.range (d.toNat+1), (j.factorial:ℂ)⁻¹ •
      mode (N.YM ((W.L 1 ^ j) u)) (2*d-p-2-j) r) = _
  rw [map_smul,map_sum]
  simp only [map_smul,C2Rigid.dualPairingFlip_apply,smul_eq_mul]

/-- The genuine contragredient target action becomes the actual transposed coproduct
on the compatible map's matrix coefficients. -/
theorem pair_mode_baseModes (hpsi : CompatibleMap N₁ N₂ N psi)
    {d : ℤ} {u : V} (hu : u ∈ W.grading d) (p : ℤ) (n : ℂ)
    {a b c : ℂ} {x : M₁} {y : M₂} {r : R}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (hr : r ∈ N.weight c) :
    C2Rigid.dualPairing N.toGW r
      (mode ((C2Rigid.contragredientModule N.toGW).YM u) p (baseModes N₁ N₂ N psi n x y)) =
      if c-d+p+1 = a+b-n-1 then
        rhoL N₁.toWeakModule N₂.toWeakModule u p (psi r) x y else 0 := by
  rw [pair_contra_mode hu p hr]
  have hj : ∀ j ∈ Finset.range (d.toNat+1), (j.factorial:ℂ)⁻¹ *
      C2Rigid.dualPairing N.toGW (mode (N.YM ((W.L 1 ^ j) u)) (2*d-p-2-j) r)
        (baseModes N₁ N₂ N psi n x y) =
      if c-d+p+1 = a+b-n-1 then (j.factorial:ℂ)⁻¹ *
        tauHat N₁.toWeakModule N₂.toWeakModule (d-j) ((W.L 1 ^ j) u)
          (2*d-p-2-j) (psi r) x y else 0 := by
    intro j hj
    have hm := N.mode_mem_weight (VertexOperatorAlgebra.L_one_pow_mem W hu j) hr (2*d-p-2-j)
    have he : c + ((d-(j:ℤ):ℤ):ℂ) - ((2*d-p-2-(j:ℤ):ℤ):ℂ) - 1 = c-d+p+1 := by
      push_cast; ring
    rw [he] at hm
    rw [pair_baseModes N₁ N₂ N psi n hx hy hm,
      hpsi.map_mode (d-j) ((W.L 1 ^ j) u) (VertexOperatorAlgebra.L_one_pow_mem W hu j)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hj]
  split_ifs with h
  · have hd := congrArg (fun b : BilinearDual (M₁ := M₁) (M₂ := M₂) => b x y)
      (VOA.Huang.PzTensorY4.twist_twist N₁.toWeakModule N₂.toWeakModule hu p (psi r))
    simpa only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, smul_eq_mul] using hd
  · simp

/-- The zeroth modes have the full intertwiner Jacobi identity on homogeneous inputs.
The derivative axiom is reconstructed together with the higher logarithmic coefficients. -/
theorem baseModes_jacobi_homogeneous (hpsi : CompatibleMap N₁ N₂ N psi)
    {d : ℤ} {u : V} (hu : u ∈ W.grading d) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (ell m : ℤ) (n : ℂ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode ((C2Rigid.contragredientModule N.toGW).YM u) (ell+m-i)
        (baseModes N₁ N₂ N psi (n+i) x y) - negOnePow ell •
        baseModes N₁ N₂ N psi (ell+n-i) x (mode (N₂.YM u) (m+i) y))) =
      ∑ᶠ i : ℤ, cbz m i •
        baseModes N₁ N₂ N psi (m+n-i) (mode (N₁.YM u) (ell+i) x) y := by
  let Y : LogModes M₁ M₂ (C2Rigid.RestrictedDual N.toGW) := fun n _ => baseModes N₁ N₂ N psi n
  have htr : ∀ (x : M₁) (y : M₂) (n : ℂ), ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ,
      Y (n+j) k x y = 0 := by
    intro x y n
    obtain ⟨K,hK⟩ := baseModes_truncated N₁ N₂ N psi x y n
    exact ⟨K,fun j hj _ => hK j hj⟩
  refine C2Rigid.restrictedDual_ext_of_pairing N.toGW fun c r hr => ?_
  have hfinL := IsLogIntertwining.jacL_support_finite
    (A₂ := N₂.toWeakModule) (A₃ := (C2Rigid.contragredientModule N.toGW).toWeakModule)
    htr u x y ell m n 0
  have hfinR := IsLogIntertwining.jacR_support_finite (A₁ := N₁.toWeakModule) Y u x y ell m n 0
  change C2Rigid.dualPairing N.toGW r (∑ᶠ i,
    IsLogIntertwining.jacL N₂.toWeakModule (C2Rigid.contragredientModule N.toGW).toWeakModule
      Y u x y ell m n 0 i) =
    C2Rigid.dualPairing N.toGW r (∑ᶠ i, IsLogIntertwining.jacR N₁.toWeakModule Y u x y ell m n 0 i)
  rw [map_finsum (C2Rigid.dualPairing N.toGW r) hfinL,
    map_finsum (C2Rigid.dualPairing N.toGW r) hfinR]
  let c₀ : ℂ := a+b+d-ell-m-n-2
  have hL : ∀ i : ℤ, C2Rigid.dualPairing N.toGW r
      (IsLogIntertwining.jacL N₂.toWeakModule (C2Rigid.contragredientModule N.toGW).toWeakModule
        Y u x y ell m n 0 i) =
      if c = c₀ then (negOnePow i * cbz ell i) *
        (rhoL N₁.toWeakModule N₂.toWeakModule u (ell+m-i) (psi r) x y -
          negOnePow ell * psi r x (mode (N₂.YM u) (m+i) y)) else 0 := by
    intro i
    simp only [IsLogIntertwining.jacL, Y, map_smul, map_sub, smul_eq_mul]
    rw [pair_mode_baseModes hpsi hu (ell+m-i) (n+i) hx hy hr,
      pair_baseModes N₁ N₂ N psi (ell+n-i) hx (N₂.mode_mem_weight hu hy (m+i)) hr]
    have h₁ : (c-d+((ell+m-i:ℤ):ℂ)+1 = a+b-(n+i)-1) ↔ c = c₀ := by
      dsimp [c₀]; push_cast; constructor <;> intro h <;> linear_combination h
    have h₂ : (c = a+(b+d-((m+i:ℤ):ℂ)-1)-(ell+n-i)-1) ↔ c = c₀ := by
      dsimp [c₀]; push_cast; constructor <;> intro h <;> linear_combination h
    by_cases h : c = c₀
    · rw [if_pos (h₁.mpr h),if_pos (h₂.mpr h),if_pos h]
    · rw [if_neg (fun h' => h (h₁.mp h')),if_neg (fun h' => h (h₂.mp h')),if_neg h]; ring
  have hR : ∀ i : ℤ, C2Rigid.dualPairing N.toGW r
      (IsLogIntertwining.jacR N₁.toWeakModule Y u x y ell m n 0 i) =
      if c = c₀ then cbz m i * psi r (mode (N₁.YM u) (ell+i) x) y else 0 := by
    intro i
    simp only [IsLogIntertwining.jacR,Y,map_smul,smul_eq_mul]
    rw [pair_baseModes N₁ N₂ N psi (m+n-i) (N₁.mode_mem_weight hu hx (ell+i)) hy hr]
    have he : (c = a+d-((ell+i:ℤ):ℂ)-1+b-(m+n-i)-1) ↔ c = c₀ := by
      dsimp [c₀]; push_cast; constructor <;> intro h <;> linear_combination h
    by_cases h : c = c₀
    · rw [if_pos (he.mpr h),if_pos h]
    · rw [if_neg (fun h' => h (he.mp h')),if_neg h,mul_zero]
  rw [finsum_congr hL,finsum_congr hR]
  by_cases h : c = c₀
  · simp only [if_pos h]
    have hs := slice_holds N₁.toWeakModule N₂.toWeakModule
      (hpsi.truncated r d u hu) (hpsi.compatible r d u hu) m ell x y
    have hsg : ∀ i : ℤ, negOnePow i * negOnePow ell = negOnePow (ell-i) := by
      intro i
      rw [← negOnePow_add,show i+ell = (ell-i)+2*i by ring,negOnePow_add]
      have hi : negOnePow (2*i) = 1 := by unfold negOnePow; rw [if_pos (even_two_mul i)]
      rw [hi,mul_one]
    have he : ∀ i : ℤ, (negOnePow i * cbz ell i) *
      (rhoL N₁.toWeakModule N₂.toWeakModule u (ell+m-i) (psi r) x y -
        negOnePow ell * psi r x (mode (N₂.YM u) (m+i) y)) =
      (negOnePow i * cbz ell i) * rhoL N₁.toWeakModule N₂.toWeakModule u (m+ell-i) (psi r) x y -
      (cbz ell i * negOnePow (ell-i)) * psi r x (mode (N₂.YM u) (m+i) y) := by
      intro i
      rw [show m+ell-i=ell+m-i by ring]
      linear_combination (-(cbz ell i * psi r x (mode (N₂.YM u) (m+i) y))) * hsg i
    rw [finsum_congr he,finsum_sub_distrib
      (Out_fin N₁.toWeakModule N₂.toWeakModule (hpsi.truncated r d u hu) m ell x y)
      (InR_fin N₂.toWeakModule u m ell (psi r) x y)]
    change Out N₁.toWeakModule N₂.toWeakModule u m ell (psi r) x y -
      InR N₂.toWeakModule u m ell (psi r) x y = InL N₁.toWeakModule u m ell (psi r) x y
    rw [hs]
    ring
  · simp only [if_neg h,finsum_zero]

end VOA.LogTensor.Pz
