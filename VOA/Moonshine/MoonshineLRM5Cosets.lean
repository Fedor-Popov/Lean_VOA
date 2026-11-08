import VOA.Moonshine.MoonshineLRM5Invariance

/-!
# Hecke cosets under `S`: the point identity

For a Hecke coset `A = (a b; 0 d)` write `d = g d₁`, `b = g b₁` with `x b₁ + y d₁ = 1`, and put
`e = a d₁` and `b′ = t e − x a`. Then `A S = γ A′` with `A′ = (g b′; 0 e)` and
`γ = (b₁, −t b₁ − y; d₁, x − t d₁) ∈ SL₂(ℤ)` (`cosetMatrix`). On points:
`(a·(S•τ) + b)/d = γ • ((gτ + b′)/e)` (`heckePoint_S_smul_eq`).

Check: the numerator of `γ • w`, `w = (gτ + b′)/e`, is `(bτ − a)/e`, and the denominator is
`dτ/e`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real
open scoped MatrixGroups

/-- The matrix `(b₁, −t b₁ − y; d₁, x − t d₁) ∈ SL₂(ℤ)` (determinant `x b₁ + y d₁ = 1`). -/
def cosetMatrix (b₁ d₁ x y t : ℤ) (h : x * b₁ + y * d₁ = 1) : SL(2, ℤ) :=
  ⟨!![b₁, -t * b₁ - y; d₁, x - t * d₁], by
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

/-- **The point identity for `S`.** -/
theorem heckePoint_S_smul_eq (a d b g e b' : ℕ) (ha : 0 < a) (hd : 0 < d) (hg : 0 < g)
    (he : 0 < e) (b₁ d₁ x y t : ℤ) (hbez : x * b₁ + y * d₁ = 1) (hdg : (d : ℤ) = g * d₁)
    (hbg : (b : ℤ) = g * b₁) (hea : (e : ℤ) = a * d₁) (hb' : (b' : ℤ) = t * e - x * a) (τ : ℍ) :
    heckePoint a d b ha hd (ModularGroup.S • τ) =
      cosetMatrix b₁ d₁ x y t hbez • heckePoint g e b' hg he τ := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, coe_heckePoint_apply, coe_heckePoint_apply, modular_S_smul,
    coe_mk]
  simp only [cosetMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, algebraMap_int_eq,
    eq_intCast]
  have hdC : (d : ℂ) = g * d₁ := by exact_mod_cast hdg
  have hbC : (b : ℂ) = g * b₁ := by exact_mod_cast hbg
  have heC : (e : ℂ) = a * d₁ := by exact_mod_cast hea
  have hb'C : (b' : ℂ) = t * e - x * a := by exact_mod_cast hb'
  have hbezC : (x : ℂ) * b₁ + y * d₁ = 1 := by exact_mod_cast hbez
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set w : ℂ := ((g : ℂ) * τ + b') / e with hw
  have hnum : (b₁ : ℂ) * w + (-(t : ℂ) * b₁ - y) = ((b : ℂ) * τ - a) / e := by
    rw [hw]
    field_simp
    rw [hbC, hb'C, heC]
    linear_combination (-(a : ℂ) * (d₁ : ℂ)) * hbezC + (a : ℂ) * (d₁ : ℂ) * hbezC - (a : ℂ) * hbezC
  have hden : (d₁ : ℂ) * w + ((x : ℂ) - t * d₁) = (d : ℂ) * τ / e := by
    rw [hw]
    field_simp
    rw [hdC, hb'C, heC]
    ring
  push_cast
  rw [hnum, hden, div_div_div_cancel_right₀ he0]
  field_simp
  ring

end VOA.Moonshine.ConwayNorton.M8
