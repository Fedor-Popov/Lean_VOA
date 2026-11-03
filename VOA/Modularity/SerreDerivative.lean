/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.QEvalHolomorphic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# The Serre derivative and its `SL₂(ℤ)`-equivariance

Following Dong–Li–Mason (q-alg/9703016, Thm 5.4 and eq. (4.29)–(4.30)), the **only** genuine
computation in Zhu's `S`-law is that the *Serre derivative*

  `∂_k f := (2πi)⁻¹ · f′ + k·(2πi)⁻² · G₂ · f`

is equivariant for the weight-`k`/weight-`(k+2)` slash actions:

  `serreDerivC_slashC : (∂_k f) ∣[k+2] γ = ∂_k (f ∣[k] γ)`.

The anomaly produced by differentiating the automorphy factor `(cz+d)^{−k}` is cancelled
*exactly* by the quasi-modular defect of `G₂` — Mathlib's
`EisensteinSeries.G2_slash_action : G₂ ∣[2] γ = G₂ − D2 γ` with `D2 γ z = 2πi·c/(cz+d)`.
`G₂` enters Zhu's argument here and nowhere else.

## Convention

Everything is in the **plain `ℂ` variable** on `imGT 0 = {z | 0 < z.im}`, matching
`Modularity.QEvalHolomorphic`: `denomC γ z = cz+d`, `mobiusC γ z = (az+b)/(cz+d)`,
`slashC k γ f z = f (mobiusC γ z) · (denomC γ z)^{−k}`, and `G2C z = G₂ (ofComplex z)`.
This keeps the derivative computation on `ℂ` (Mathlib's `HasDerivAt`) instead of in
`UpperHalfPlane` charts; `slashC_eq_slash` records the agreement with Mathlib's `∣[k]`.

The normalisation `(2πi)⁻²` is **forced**, not chosen: see `serreDerivC_slashC`'s proof — the
anomaly cancels iff the `G₂`-coefficient is `k·(2πi)⁻²`.  With Mathlib's `E₂ = G₂/(2ζ(2))` and
`ζ(2) = π²/6` this is the familiar `−(k/12)·E₂`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped MatrixGroups ModularForm

/-! ## The Möbius action on `ℂ` -/

/-- `denomC γ z = cz + d`. -/
noncomputable def denomC (γ : SL(2, ℤ)) (z : ℂ) : ℂ := (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)

/-- `mobiusC γ z = (az + b)/(cz + d)`. -/
noncomputable def mobiusC (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / denomC γ z

/-- The determinant relation `ad − bc = 1`, over `ℂ`. -/
theorem det_relC (γ : SL(2, ℤ)) :
    (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hdet
  exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) hdet

theorem denomC_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ imGT 0) : denomC γ z ≠ 0 := by
  have hz0 : (0 : ℝ) < z.im := hz
  by_cases hc : (γ 1 0 : ℤ) = 0
  · -- `c = 0` forces `d ≠ 0` by `ad − bc = 1`
    have hdet := det_relC γ
    rw [show ((γ 1 0 : ℤ) : ℂ) = 0 from by exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) hc,
      mul_zero, sub_zero] at hdet
    have hd : (γ 1 1 : ℂ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hdet; exact one_ne_zero hdet.symm
    rw [denomC, show ((γ 1 0 : ℤ) : ℂ) = 0 from by exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) hc,
      zero_mul, zero_add]
    exact hd
  · -- `c ≠ 0` makes the imaginary part nonzero
    intro h0
    have him : (denomC γ z).im = ((γ 1 0 : ℤ) : ℝ) * z.im := by
      simp [denomC, Complex.add_im, Complex.mul_im]
    rw [h0, Complex.zero_im] at him
    have hcR : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    exact hcR (by
      rcases mul_eq_zero.mp him.symm with h | h
      · exact h
      · exact absurd h hz0.ne')

/-- `mobiusC` agrees with the `SL₂(ℤ)`-action on `ℍ`. -/
theorem mobiusC_coe (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    mobiusC γ (τ : ℂ) = ((γ • τ : UpperHalfPlane) : ℂ) := by
  rw [mobiusC, denomC, UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num

theorem mobiusC_mem_imGT (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ imGT 0) : mobiusC γ z ∈ imGT 0 := by
  have hz0 : (0 : ℝ) < z.im := hz
  have hcoe : mobiusC γ z = ((γ • (⟨z, hz0⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
    mobiusC_coe γ ⟨z, hz0⟩
  rw [hcoe]
  exact (γ • (⟨z, hz0⟩ : UpperHalfPlane)).im_pos

/-! ## Derivatives -/

theorem hasDerivAt_denomC (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (denomC γ) ((γ 1 0 : ℂ)) z := by
  have h : HasDerivAt (fun w : ℂ => (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ((γ 1 0 : ℂ) * 1) z :=
    ((hasDerivAt_id z).const_mul ((γ 1 0 : ℂ))).add_const ((γ 1 1 : ℂ))
  rw [mul_one] at h
  exact h

/-- `d/dz (az+b)/(cz+d) = (cz+d)⁻²`, using `ad − bc = 1`. -/
theorem hasDerivAt_mobiusC (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ imGT 0) :
    HasDerivAt (mobiusC γ) ((denomC γ z) ^ (-2 : ℤ)) z := by
  have hD := denomC_ne_zero γ hz
  have hnum : HasDerivAt (fun w : ℂ => (γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) ((γ 0 0 : ℂ)) z := by
    have h : HasDerivAt (fun w : ℂ => (γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) ((γ 0 0 : ℂ) * 1) z :=
      ((hasDerivAt_id z).const_mul ((γ 0 0 : ℂ))).add_const ((γ 0 1 : ℂ))
    rwa [mul_one] at h
  have hq := hnum.div (hasDerivAt_denomC γ z) hD
  have hval : ((γ 0 0 : ℂ) * (denomC γ z) - ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) * (γ 1 0 : ℂ))
      / (denomC γ z) ^ 2 = (denomC γ z) ^ (-2 : ℤ) := by
    have hnum2 : (γ 0 0 : ℂ) * (denomC γ z)
        - ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) * (γ 1 0 : ℂ) = 1 := by
      rw [denomC]
      linear_combination det_relC γ
    rw [hnum2, zpow_neg, zpow_two, ← pow_two]
    exact (one_div _).trans rfl
  rw [hval] at hq
  exact hq

/-! ## The slash action on `ℂ`-functions -/

/-- The weight-`k` slash action, in the plain `ℂ` variable. -/
noncomputable def slashC (k : ℤ) (γ : SL(2, ℤ)) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f (mobiusC γ z) * (denomC γ z) ^ (-k)

/-- `2πi ≠ 0`. -/
theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_ne_zero]

theorem slashC_mul (k l : ℤ) (γ : SL(2, ℤ)) (f g : ℂ → ℂ) {z : ℂ} (hz : z ∈ imGT 0) :
    slashC (k + l) γ (fun w => f w * g w) z = slashC k γ f z * slashC l γ g z := by
  have hD := denomC_ne_zero γ hz
  rw [slashC, slashC, slashC, neg_add, zpow_add₀ hD]
  ring

/-! ## The chain rule for the slash action -/

theorem hasDerivAt_slashC (k : ℤ) (γ : SL(2, ℤ)) (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ imGT 0)
    {fd : ℂ} (hf : HasDerivAt f fd (mobiusC γ z)) :
    HasDerivAt (slashC k γ f)
      (fd * (denomC γ z) ^ (-2 : ℤ) * (denomC γ z) ^ (-k)
        + f (mobiusC γ z) * (((-k : ℤ) : ℂ) * (denomC γ z) ^ (-k - 1) * (γ 1 0 : ℂ))) z := by
  have hD := denomC_ne_zero γ hz
  have h1 : HasDerivAt (fun w => f (mobiusC γ w)) (fd * (denomC γ z) ^ (-2 : ℤ)) z :=
    hf.comp z (hasDerivAt_mobiusC γ hz)
  have h2 : HasDerivAt (fun w => (denomC γ w) ^ (-k))
      (((-k : ℤ) : ℂ) * (denomC γ z) ^ (-k - 1) * (γ 1 0 : ℂ)) z :=
    (hasDerivAt_zpow (-k) (denomC γ z) (Or.inl hD)).comp z (hasDerivAt_denomC γ z)
  exact h1.mul h2

/-- **The slash/derivative commutator.**  Differentiating `f ∣[k] γ` produces exactly one
anomalous term, proportional to `k·c/(cz+d)`. -/
theorem slashC_deriv_eq (k : ℤ) (γ : SL(2, ℤ)) (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ imGT 0)
    (hf : DifferentiableAt ℂ f (mobiusC γ z)) :
    slashC (k + 2) γ (_root_.deriv f) z
      = _root_.deriv (slashC k γ f) z
        + (k : ℂ) * (γ 1 0 : ℂ) * (denomC γ z)⁻¹ * slashC k γ f z := by
  have hD := denomC_ne_zero γ hz
  have hder := (hasDerivAt_slashC k γ f hz hf.hasDerivAt).deriv
  rw [hder, slashC, slashC]
  have e1 : (denomC γ z) ^ (-(k + 2)) = (denomC γ z) ^ (-2 : ℤ) * (denomC γ z) ^ (-k) := by
    rw [← zpow_add₀ hD]; ring_nf
  have e2 : (denomC γ z)⁻¹ * (denomC γ z) ^ (-k) = (denomC γ z) ^ (-k - 1) := by
    rw [← zpow_neg_one, ← zpow_add₀ hD]; ring_nf
  rw [e1]
  push_cast
  rw [show (k : ℂ) * (γ 1 0 : ℂ) * (denomC γ z)⁻¹ * (f (mobiusC γ z) * (denomC γ z) ^ (-k))
      = f (mobiusC γ z) * ((k : ℂ) * ((denomC γ z)⁻¹ * (denomC γ z) ^ (-k)) * (γ 1 0 : ℂ)) from by
    ring, e2]
  ring

/-! ## `G₂` in the `ℂ` picture -/

/-- Mathlib's `G₂`, read as a function on `ℂ`. -/
noncomputable def G2C (z : ℂ) : ℂ := EisensteinSeries.G2 (UpperHalfPlane.ofComplex z)

theorem G2C_coe {z : ℂ} (hz : z ∈ imGT 0) :
    G2C z = EisensteinSeries.G2 (⟨z, hz⟩ : UpperHalfPlane) := by
  rw [G2C, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- **The quasi-modularity of `G₂`, in the `ℂ` picture** (Mathlib's `G2_slash_action`). -/
theorem slashC_G2C (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ imGT 0) :
    slashC 2 γ G2C z
      = G2C z - 2 * (Real.pi : ℂ) * Complex.I * (γ 1 0 : ℂ) * (denomC γ z)⁻¹ := by
  have hlaw := congrFun (EisensteinSeries.G2_slash_action γ) (⟨z, hz⟩ : UpperHalfPlane)
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply] at hlaw
  have hden : ((γ 1 0 : ℤ) : ℂ) * ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) + ((γ 1 1 : ℤ) : ℂ)
      = denomC γ z := rfl
  rw [hden] at hlaw
  have hmob : ((γ • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = mobiusC γ z :=
    (mobiusC_coe γ ⟨z, hz⟩).symm
  have hG2m : EisensteinSeries.G2 (γ • (⟨z, hz⟩ : UpperHalfPlane)) = G2C (mobiusC γ z) := by
    rw [G2C, ← hmob, UpperHalfPlane.ofComplex_apply]
  have hD2 : (EisensteinSeries.D2 γ) (⟨z, hz⟩ : UpperHalfPlane)
      = 2 * (Real.pi : ℂ) * Complex.I * (γ 1 0 : ℂ) * (denomC γ z)⁻¹ := by
    rw [EisensteinSeries.D2, ModularGroup.denom_apply, hden]
    ring
  rw [hG2m] at hlaw
  simp only [Pi.sub_apply, hD2] at hlaw
  rw [← G2C_coe hz] at hlaw
  rw [slashC]
  exact hlaw

/-! ## The Serre derivative -/

/-- **The Serre derivative** `∂_k f = (2πi)⁻¹ f′ + k(2πi)⁻² G₂ f`.  The coefficient of `G₂` is
forced by equivariance (`serreDerivC_slashC`); with `E₂ = G₂/(2ζ(2))` it is the familiar
`−(k/12)E₂`. -/
noncomputable def serreDerivC (k : ℤ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv f z
    + (k : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * (G2C z * f z)

/-- **Serre-derivative equivariance** — the only real computation in Zhu's `S`-law.

`(∂_k f) ∣[k+2] γ = ∂_k (f ∣[k] γ)`: the anomaly `k·c/(cz+d)` from differentiating the automorphy
factor is cancelled *exactly* by the quasi-modular defect `−2πi·c/(cz+d)` of `G₂`. -/
theorem serreDerivC_slashC (k : ℤ) (γ : SL(2, ℤ)) (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ imGT 0)
    (hf : DifferentiableAt ℂ f (mobiusC γ z)) :
    slashC (k + 2) γ (serreDerivC k f) z = serreDerivC k (slashC k γ f) z := by
  have hD := denomC_ne_zero γ hz
  have hpi := two_pi_I_ne_zero
  -- split the slash of the sum
  have hsplit : slashC (k + 2) γ (serreDerivC k f) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * slashC (k + 2) γ (_root_.deriv f) z
        + (k : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2
            * (slashC 2 γ G2C z * slashC k γ f z) := by
    rw [← slashC_mul 2 k γ G2C f hz]
    simp only [slashC, serreDerivC]
    rw [show (2 : ℤ) + k = k + 2 from by ring]
    ring
  rw [hsplit, slashC_deriv_eq k γ f hz hf, slashC_G2C γ hz, serreDerivC]
  field_simp
  ring

end VOA
