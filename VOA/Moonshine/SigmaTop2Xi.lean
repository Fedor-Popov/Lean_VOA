/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Eigen

/-!
# A quadratic refinement `ξ` of the `N(A₁²⁴)`-cocycle on the root lattice

On the root lattice `R = ⊕ ℤ α_i ⊆ N` (`α_i = 2e_i`, coordinates `x ∈ ℤ²⁴`, `φ(x) = Σ x_i α_i`)
the cocycle `ε_N` is symmetric (all inner products are even), so it is a coboundary:
`ξ(x) ξ(y) = ε_N(φx, φy) ξ(x+y)`.  We fix the solution with `ξ(e_i) = i` (`xi_single`).

## Main results
* `phiR` — `x ↦ Σ x_i α_i` (the vector `2x` of `N`).
* `xi`, `xi_mul` (`ξ(x)ξ(y) = ε_N(φx,φy) ξ(x+y)`), `xi_single`, `xi_zero`.

## Status
`sorry`-free.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality

/-- `x ↦ Σ x_i α_i = 2x ∈ N`. -/
def phiR : (Fin 24 → ℤ) →ₗ[ℤ] golayN.carrier where
  toFun x := show ↥Leech.preG from ⟨(2 : ℤ) • x, two_smul_mem_preimageOfCode Code.golay x⟩
  map_add' x y := Subtype.ext (by simp only [smul_add]; rfl)
  map_smul' c x := Subtype.ext (by
    change (2 : ℤ) • (c • x) = c • ((2 : ℤ) • x)
    rw [smul_comm])

theorem gv_phiR (x : Fin 24 → ℤ) : gv (phiR x) = (2 : ℤ) • x := rfl

theorem phiR_single (i : Fin 24) : phiR (Pi.single i 1) = golayRoot i := rfl

theorem form_phiR (x y : Fin 24 → ℤ) : golayN.form (phiR x) (phiR y) = 2 * (x ⬝ᵥ y) := by
  rw [golayN_form, gv_phiR, gv_phiR, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [show (2 : ℤ) * (2 * (x ⬝ᵥ y)) = 2 * (2 * (x ⬝ᵥ y)) from rfl]
  omega

/-- The pulled-back cocycle exponent. -/
noncomputable def DR : (Fin 24 → ℤ) →ₗ[ℤ] (Fin 24 → ℤ) →ₗ[ℤ] ℤ := (cocForm golayN).compl₁₂ phiR phiR

theorem DR_apply (x y : Fin 24 → ℤ) : DR x y = cocForm golayN (phiR x) (phiR y) := rfl

theorem εN_phiR (x y : Fin 24 → ℤ) : εN (phiR x) (phiR y) = (-1 : ℂ) ^ (DR x y) := rfl

theorem DR_symm_even (x y : Fin 24 → ℤ) : 2 ∣ DR x y + DR y x := by
  apply two_dvd_of_neg_one_zpow_eq_one
  rw [DR_apply, DR_apply, neg_one_zpow_cocForm_comm golayN golayN_even, form_phiR, zpow_mul]
  norm_num

/-- The coboundary part `i^{S(x,x)}`. -/
noncomputable def xi0 (x : Fin 24 → ℤ) : ℂ := cobSign (Pi.basisFun ℤ (Fin 24)) DR x

theorem xi0_ne_zero (x : Fin 24 → ℤ) : xi0 x ≠ 0 := cobSign_ne_zero _ _ x

theorem xi0_mul (x y : Fin 24 → ℤ) : xi0 x * xi0 y = εN (phiR x) (phiR y) * xi0 (x + y) := by
  rw [xi0, xi0, xi0, cobSign_add _ _ DR_symm_even, εN_phiR]
  have h : (-1 : ℂ) ^ (DR x y) * (-1 : ℂ) ^ (DR x y) = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  linear_combination (-(cobSign (Pi.basisFun ℤ (Fin 24)) DR x * cobSign (Pi.basisFun ℤ (Fin 24)) DR y)) * h

/-- The character correcting `ξ(e_i)` to `i`. -/
noncomputable def wXi (i : Fin 24) : ℂ := Complex.I / xi0 (Pi.single i 1)

theorem wXi_ne_zero (i : Fin 24) : wXi i ≠ 0 := div_ne_zero Complex.I_ne_zero (xi0_ne_zero _)

/-- **`ξ`**: the quadratic refinement of `ε_N` on `R` with `ξ(e_i) = i`. -/
noncomputable def xi (x : Fin 24 → ℤ) : ℂ := xi0 x * ∏ i, wXi i ^ (x i)

theorem xi_mul (x y : Fin 24 → ℤ) : xi x * xi y = εN (phiR x) (phiR y) * xi (x + y) := by
  rw [xi, xi, xi]
  have hc : ∏ i, wXi i ^ ((x + y) i) = (∏ i, wXi i ^ (x i)) * ∏ i, wXi i ^ (y i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add₀ (wXi_ne_zero i)]
  rw [hc]
  calc xi0 x * (∏ i, wXi i ^ x i) * (xi0 y * ∏ i, wXi i ^ y i)
      = (xi0 x * xi0 y) * ((∏ i, wXi i ^ x i) * ∏ i, wXi i ^ y i) := by ring
    _ = _ := by rw [xi0_mul]; ring

theorem xi_zero : xi 0 = 1 := by
  rw [xi, xi0, cobSign_zero]; simp

theorem xi_single (i : Fin 24) : xi (Pi.single i 1) = Complex.I := by
  rw [xi]
  have hp : ∏ l, wXi l ^ ((Pi.single i 1 : Fin 24 → ℤ) l) = wXi i := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro l _ hl; simp [hl]
    · simp
  rw [hp, wXi]
  field_simp [xi0_ne_zero (Pi.single i 1)]

theorem xi_ne_zero (x : Fin 24 → ℤ) : xi x ≠ 0 :=
  mul_ne_zero (xi0_ne_zero x) (Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (wXi_ne_zero i))

end VOA.Moonshine.SigmaTop
