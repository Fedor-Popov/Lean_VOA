/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroClassification

/-!
# Genus zero on the abstract interface: the stabiliser of `∞` in the symmetry group

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. For a `J`-dominated `q`-series `f`, every element
of `symmetryGroup f` with lower-left entry `0` acts on `ℍ` as an integer translation
(`exists_int_smul_eq_add_of_lowerLeft_eq_zero`): such a `γ` acts as `z ↦ (a/d) z + b/d`, an
affine global symmetry, and those are integer translations (`exists_int_of_affine_family`, which
uses top injectivity). No Hecke input.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set

/-- **The stabiliser of `∞`**: an element of `symmetryGroup f` with `γ 1 0 = 0` is
`τ ↦ τ + n` on `ℍ` for an integer `n`. -/
theorem exists_int_smul_eq_add_of_lowerLeft_eq_zero {c : ℕ → ℂ} (hc : IsJDominated c)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ symmetryGroup (qSeriesFun c)) (h10 : γ 1 0 = 0) :
    ∃ n : ℤ, ∀ τ : ℍ, ((γ • τ : ℍ) : ℂ) = τ + n := by
  have hdet : γ.det.val = 1 := by rw [hγ.1]; rfl
  have hdet' : γ 0 0 * γ 1 1 = 1 := by
    have h := hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, mul_zero,
      sub_zero] at h
    exact h
  have hd : γ 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet'
  have hdc : ((γ 1 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hform : ∀ τ : ℍ, ((γ • τ : ℍ) : ℂ) =
      ((γ 0 0 / γ 1 1 : ℝ) : ℂ) * τ + ((γ 0 1 / γ 1 1 : ℝ) : ℂ) := by
    intro τ
    rw [coe_smul_of_det_pos (by rw [hdet]; exact one_pos), num, denom, h10,
      Complex.ofReal_zero, zero_mul, zero_add]
    push_cast
    field_simp
  have hglob : ∀ z : ℂ, 0 < z.im →
      0 < (((γ 0 0 / γ 1 1 : ℝ) : ℂ) * z + ((γ 0 1 / γ 1 1 : ℝ) : ℂ)).im ∧
      qSeriesExt c (((γ 0 0 / γ 1 1 : ℝ) : ℂ) * z + ((γ 0 1 / γ 1 1 : ℝ) : ℂ)) =
        qSeriesExt c z := by
    intro z hz
    have h1 := hform ⟨z, hz⟩
    refine ⟨?_, ?_⟩
    · rw [← h1]
      exact (γ • (⟨z, hz⟩ : ℍ)).im_pos
    · rw [← h1, qSeriesExt_coe, hγ.2, qSeriesExt_of_im_pos c hz]
  obtain ⟨hB, n, hK⟩ := exists_int_of_affine_family hc hglob
  refine ⟨n, fun τ => ?_⟩
  rw [hform, hB, hK, Complex.ofReal_one, one_mul]

end VOA.Moonshine.ConwayNorton
