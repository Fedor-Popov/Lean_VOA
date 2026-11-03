/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkContinuation

/-!
# Serre–Stark S5-5c: the Fricke transform of a class form (functional equations combined)

For a class form `f` (class-form space `S`, `ψ` primitive and even), `W f = fricke N f`, and `z`
with `Re z > 3/2`, `Im z ≠ 0`, `1/2 − z` good:

`L(z, W f) = Pref(z) · F_g(1/2 − z) ∏_{p ∣ N} (1 − ψ(p) p^{2z−1}) · L(2z, ψ⁻¹)`

(`fricke_LSeries_eq`), combining Hecke's functional equation for θ-type forms
(`fePair_functional_equation`), the continuation `G1_eq_G2`, `LFunction_changeLevel`, and
Mathlib's functional equation for primitive Dirichlet L-functions
(`IsPrimitive.completedLFunction_one_sub`).
-/

open Complex
open scoped UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

namespace ClassSetup

variable (S : ClassSetup)

theorem even_inv {ψ : DirichletCharacter ℂ S.r} (hev : ψ.Even) : ψ⁻¹.Even := by
  unfold DirichletCharacter.Even at *
  rw [MulChar.inv_apply]
  have : Ring.inverse (-1 : ZMod S.r) = -1 := by
    have h := Ring.inverse_unit (-1 : (ZMod S.r)ˣ)
    simpa using h
  rw [this, hev]

/-- The prefactor of the Fricke functional equation. -/
def Pref (z : ℂ) : ℂ :=
  (feRoot S.N)⁻¹ * ((feScale S.N : ℝ) : ℂ) ^ z * ((feScale S.N : ℝ) : ℂ) ^ (-(1 / 2 - z)) *
    (S.t : ℂ) ^ (-(1 / 2 - z)) * (S.r : ℂ) ^ (2 * z - 1 / 2) *
    DirichletCharacter.rootNumber S.ψ * (Real.pi : ℂ) ^ (-(2 * z) / 2) /
    (Real.pi : ℂ) ^ (-(1 - 2 * z) / 2)

variable {f : ℂ → ℂ} (hf : IsClassForm S.N S.r S.ψ S.t f)

/-- **The L-series of `W f` through the resolvent factor.** -/
theorem fricke_LSeries_eq (hprim : S.ψ.IsPrimitive) (hev : S.ψ.Even) {z : ℂ}
    (hz : 3 / 2 < z.re) (hzi : z.im ≠ 0) (hgood : S.Good (1 / 2 - z)) :
    LSeries (thetaTypeCoeff (fricke S.N f)) z =
      S.Pref z * (S.Fs (1 / 2 - z) (S.gf hf) *
        ∏ p ∈ S.N.primeFactors, (1 - S.ψ p * (p : ℂ) ^ (-(1 - 2 * z)))) *
        DirichletCharacter.LFunction S.ψ⁻¹ (2 * z) := by
  set c : ℂ := ((feScale S.N : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (feScale_pos S.hN).ne'
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz; linarith
  -- `1/2 − z ∈ Ω`
  have hs0 : (1 / 2 - z) ≠ 0 := fun h => hzi (by
    have := congrArg Complex.im h; simp at this; linarith)
  have hs12 : (1 / 2 - z) ≠ 1 / 2 := fun h => hz0 (by linear_combination -h)
  have hΩ : (1 / 2 - z) ∈ S.Ω := ⟨hgood, hs0, hs12⟩
  have hG := S.G1_eq_G2 hf hΩ
  -- Gamma factors are nonzero
  have hΓz : Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hΓs : Gamma (1 / 2 - z) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    apply hzi
    have := congrArg Complex.im hm
    simp at this
    linarith
  -- Hecke's functional equation
  have hFE := fePair_functional_equation S.hN S.h24 hf.1 z
  rw [fePair_symm_Λ_eq S.hN S.h24 hf.1 hz] at hFE
  -- the continuation at `1/2 − z`
  rw [G1, G2] at hG
  have hΛ : (fePair S.N f S.hN S.h24 hf.1).Λ (1 / 2 - z) = Gamma (1 / 2 - z) *
      (c ^ (-(1 / 2 - z)) * S.Fs (1 / 2 - z) (S.gf hf) * (S.t : ℂ) ^ (-(1 / 2 - z)) *
      DirichletCharacter.LFunction S.χN (2 * (1 / 2 - z))) := by
    rw [← hG, mul_comm, mul_assoc, inv_mul_cancel₀ hΓs, mul_one]
  -- change of level
  have h2s : 2 * (1 / 2 - z) = 1 - 2 * z := by ring
  rw [h2s] at hΛ
  have hCL := DirichletCharacter.LFunction_changeLevel S.hrN S.ψ (s := 1 - 2 * z)
    (Or.inr (fun h => hz0 (by linear_combination -h / 2)))
  rw [show DirichletCharacter.changeLevel S.hrN S.ψ = S.χN from rfl] at hCL
  rw [hCL] at hΛ
  -- Dirichlet functional equation
  have h12z : (1 - 2 * z) ≠ 0 := fun h => hzi (by
    have := congrArg Complex.im h; simp at this; linarith)
  have hD1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor S.ψ (1 - 2 * z)
    (Or.inl h12z)
  rw [hprim.completedLFunction_one_sub (2 * z)] at hD1
  have h2z0 : (2 * z) ≠ 0 := mul_ne_zero two_ne_zero hz0
  have hD2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor S.ψ⁻¹ (2 * z)
    (Or.inl h2z0)
  have hevi := S.even_inv hev
  rw [hev.gammaFactor_def] at hD1
  rw [hevi.gammaFactor_def] at hD2
  have hGR2 : Gammaℝ (2 * z) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [mul_re]; simp; linarith)
  have hcomp : DirichletCharacter.completedLFunction S.ψ⁻¹ (2 * z) =
      DirichletCharacter.LFunction S.ψ⁻¹ (2 * z) * Gammaℝ (2 * z) := by
    rw [hD2]; field_simp
  rw [hcomp] at hD1
  rw [hD1] at hΛ
  -- unfold the Gamma factors
  have hGR_a : Gammaℝ (2 * z) = (Real.pi : ℂ) ^ (-(2 * z) / 2) * Gamma z := by
    rw [Gammaℝ_def]; congr 2; ring
  have hGR_b : Gammaℝ (1 - 2 * z) = (Real.pi : ℂ) ^ (-(1 - 2 * z) / 2) * Gamma (1 / 2 - z) := by
    rw [Gammaℝ_def]; congr 2; ring
  rw [hGR_a, hGR_b] at hΛ
  have hpa : (Real.pi : ℂ) ^ (-(2 * z) / 2) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hpi0)
  have hpb : (Real.pi : ℂ) ^ (-(1 - 2 * z) / 2) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hpi0)
  have hcz : c ^ (-z) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hc0)
  have hcz' : c ^ z ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hc0)
  have hε := feRoot_ne_zero S.hN
  rw [hΛ] at hFE
  -- solve for `L(z, W f)`
  have hcc : c ^ z * c ^ (-z) = 1 := by
    rw [← cpow_add _ _ hc0, add_neg_cancel, cpow_zero]
  unfold Pref
  rw [← hc]
  set A := LSeries (thetaTypeCoeff (fricke S.N f)) z
  have hΓs' : Gamma ((1 - 2 * z) / 2) ≠ 0 := by rwa [show (1 - 2 * z) / 2 = 1 / 2 - z by ring]
  rw [show ((feScale S.N : ℝ) : ℂ) ^ (-z) = (c ^ z)⁻¹ from cpow_neg _ _] at hFE
  have hA : A = (feRoot S.N)⁻¹ * (Gamma z)⁻¹ * c ^ z * (Gamma (1 / 2 - z) *
      (c ^ (-(1 / 2 - z)) * S.Fs (1 / 2 - z) (S.gf hf) * ↑S.t ^ (-(1 / 2 - z)) *
        (↑S.r ^ (2 * z - 1 / 2) * S.ψ.rootNumber *
              (DirichletCharacter.LFunction S.ψ⁻¹ (2 * z) * (↑Real.pi ^ (-(2 * z) / 2) * Gamma z)) /
            (↑Real.pi ^ (-(1 - 2 * z) / 2) * Gamma (1 / 2 - z)) *
          ∏ p ∈ S.N.primeFactors, (1 - S.ψ ↑p * ↑p ^ (-(1 - 2 * z)))))) := by
    rw [hFE]; field_simp
  rw [hA]
  field_simp

end ClassSetup

end SSHecke

end VOA.Classification.COne
