/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.LatticeDeligne
import VOA.DeligneAudit.E6LatTable

/-!
# The FLM cocycle of the `E₆` root lattice, up to a coboundary

Rank-6 instance of the `E7LieCocycle`: `latticeCocycle e6` is cohomologous to the explicit upper-triangular
cocycle `ε'(α,β) = (-1)^{ep α β}` (`cocycle_coboundary`, with the explicit sign `f = (-1)^q`).
-/

namespace VOA.DeligneAudit.E6Lat

open VOA VOA.IntegralLattice VOA.CartanLattices

set_option linter.style.longLine false

noncomputable section

/-- The `E₆` Cartan matrix as a computable table. -/
def Gm : Fin 6 → Fin 6 → ℤ := ![![2, 0, -1, 0, 0, 0], ![0, 2, 0, -1, 0, 0], ![-1, 0, 2, -1, 0, 0], ![0, -1, -1, 2, -1, 0], ![0, 0, 0, -1, 2, -1], ![0, 0, 0, 0, -1, 2]]

theorem cartanE6_eq (i j : Fin 6) : CartanMatrix.E₆ i j = Gm i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem e6_formG (v w : Lat) : e6.form v w = ∑ i, ∑ j, v i * Gm i j * w j := by
  show Matrix.toBilin' (CartanMatrix.E₆) v w = _
  rw [Matrix.toBilin'_apply]
  simp only [cartanE6_eq]

theorem e6_form_eq (v w : Lat) : e6.form v w = formZ v w := by
  rw [e6_formG]
  simp only [Fin.sum_univ_six, formZ, Gm, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-! ## Bilinearity of the cocycle exponent -/

/-- The basis used by `latticeCocycle e6`. -/
abbrev B := latticeBasis e6

/-- `Tᵢⱼ = coc(eᵢ, eⱼ)`. -/
def T (i j : Fin 6) : ℤ := cocExp e6 B (Pi.single i 1 : Lat) (Pi.single j 1 : Lat)

theorem lat_decomp (α : Lat) : α = ∑ i, α i • (Pi.single i 1 : Lat) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem cocExp_eq (α β : Lat) : cocExp e6 B α β = ∑ i, ∑ j, α i * β j * T i j := by
  let φ : Lat →+ ℤ := AddMonoidHom.mk' (fun x => cocExp e6 B x β) fun x y => cocExp_add_left e6 B x y β
  have hφ : cocExp e6 B α β = φ α := rfl
  rw [hφ, lat_decomp α, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, smul_eq_mul]
  let ψ : Lat →+ ℤ := AddMonoidHom.mk' (fun y => cocExp e6 B (Pi.single i 1 : Lat) y)
    fun x y => cocExp_add_right e6 B _ x y
  have hψ : φ (Pi.single i 1) = ψ β := rfl
  rw [hψ, lat_decomp β, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, smul_eq_mul]
  have : ψ (Pi.single j 1) = T i j := rfl
  rw [this]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- The cocycle exponent in coordinates. -/
def cE (α β : Lat) : ℤ := ∑ i, ∑ j, α i * β j * T i j

theorem latticeCocycle_eq (α β : Lat) : latticeCocycle e6 α β = (-1 : ℂ) ^ cE α β := by
  show (-1 : ℂ) ^ cocExp e6 B α β = _
  rw [cocExp_eq]; rfl

/-- The commutator property in coordinates: `Tᵢⱼ + Tⱼᵢ ≡ Gᵢⱼ (mod 2)`. -/
theorem T_swap (i j : Fin 6) : ∃ k : ℤ, T i j + T j i = Gm i j + 2 * k := by
  have h := cocExp_add_swap e6 B (Pi.single i 1 : Lat) (Pi.single j 1 : Lat)
  have hD : (2 : ℤ) ∣ ∑ l : Fin _, e6.form (B l) (B l) * B.repr (Pi.single i 1 : Lat) l *
      B.repr (Pi.single j 1 : Lat) l :=
    Finset.dvd_sum fun l _ => ((e6_even (B l)).mul_right _).mul_right _
  obtain ⟨k, hk⟩ := hD
  refine ⟨-k, ?_⟩
  have hf : e6.form (Pi.single i 1 : Lat) (Pi.single j 1 : Lat) = Gm i j := by
    rw [e6_formG]
    simp [Pi.single_apply]
  change T i j + T j i = _ at h
  rw [h, hf, hk]
  ring

/-! ## The explicit cocycle and the coboundary -/

/-- The upper-triangular exponent table: `T'ᵢⱼ = Gᵢⱼ` for `i < j`, `T'ᵢᵢ = 1`, else `0`. -/
def Tp : Fin 6 → Fin 6 → ℤ := ![![1, 0, -1, 0, 0, 0], ![0, 1, 0, -1, 0, 0], ![0, 0, 1, -1, 0, 0], ![0, 0, 0, 1, -1, 0], ![0, 0, 0, 0, 1, -1], ![0, 0, 0, 0, 0, 1]]

/-- `n(n-1)/2`. -/
def C2 (x : ℤ) : ℤ := x * (x - 1) / 2

theorem two_C2 (x : ℤ) : 2 * C2 x = x * (x - 1) :=
  Int.mul_ediv_cancel' (even_iff_two_dvd.mp (Int.even_mul_pred_self x))

theorem C2_add (x y : ℤ) : C2 (x + y) = C2 x + C2 y + x * y := by
  have h1 := two_C2 (x + y)
  have h2 := two_C2 x
  have h3 := two_C2 y
  have : 2 * C2 (x + y) = 2 * (C2 x + C2 y + x * y) := by linear_combination h1 - h2 - h3
  omega

theorem C2_zero : C2 0 = 0 := rfl

/-- `R = T - T'`. -/
def R (i j : Fin 6) : ℤ := T i j - Tp i j

/-- The quadratic refinement `q` of `R`. -/
def q (α : Lat) : ℤ :=
  R 0 1 * α 0 * α 1 +
    R 0 2 * α 0 * α 2 +
    R 0 3 * α 0 * α 3 +
    R 0 4 * α 0 * α 4 +
    R 0 5 * α 0 * α 5 +
    R 1 2 * α 1 * α 2 +
    R 1 3 * α 1 * α 3 +
    R 1 4 * α 1 * α 4 +
    R 1 5 * α 1 * α 5 +
    R 2 3 * α 2 * α 3 +
    R 2 4 * α 2 * α 4 +
    R 2 5 * α 2 * α 5 +
    R 3 4 * α 3 * α 4 +
    R 3 5 * α 3 * α 5 +
    R 4 5 * α 4 * α 5 +
    R 0 0 * C2 (α 0) + R 1 1 * C2 (α 1) + R 2 2 * C2 (α 2) + R 3 3 * C2 (α 3) + R 4 4 * C2 (α 4) + R 5 5 * C2 (α 5)

/-- The rescaling sign `f(α) = (-1)^{q α}`. -/
def f (α : Lat) : ℂ := (-1 : ℂ) ^ q α

theorem f_zero : f 0 = 1 := by
  simp [f, q, C2_zero]

theorem f_mul_self (α : Lat) : f α * f α = 1 := by
  rw [f, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

theorem neg_one_zpow_eq {m n : ℤ} (e : ℤ) (h : m = n + 2 * e) : (-1 : ℂ) ^ m = (-1 : ℂ) ^ n := by
  rw [h, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

/-- **The coboundary identity** `ε(α,β) f(α) f(β) = ε'(α,β) f(α+β)`. -/
theorem cocycle_coboundary (α β : Lat) :
    latticeCocycle e6 α β * f α * f β = (-1 : ℂ) ^ ep α β * f (α + β) := by
  obtain ⟨k01, h01⟩ := T_swap 0 1
  obtain ⟨k02, h02⟩ := T_swap 0 2
  obtain ⟨k03, h03⟩ := T_swap 0 3
  obtain ⟨k04, h04⟩ := T_swap 0 4
  obtain ⟨k05, h05⟩ := T_swap 0 5
  obtain ⟨k12, h12⟩ := T_swap 1 2
  obtain ⟨k13, h13⟩ := T_swap 1 3
  obtain ⟨k14, h14⟩ := T_swap 1 4
  obtain ⟨k15, h15⟩ := T_swap 1 5
  obtain ⟨k23, h23⟩ := T_swap 2 3
  obtain ⟨k24, h24⟩ := T_swap 2 4
  obtain ⟨k25, h25⟩ := T_swap 2 5
  obtain ⟨k34, h34⟩ := T_swap 3 4
  obtain ⟨k35, h35⟩ := T_swap 3 5
  obtain ⟨k45, h45⟩ := T_swap 4 5
  rw [latticeCocycle_eq, f, f, f, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  refine neg_one_zpow_eq
    ((k01 - R 0 1) * α 1 * β 0 +
      (k02 - R 0 2) * α 2 * β 0 +
      (k03 - R 0 3) * α 3 * β 0 +
      (k04 - R 0 4) * α 4 * β 0 +
      (k05 - R 0 5) * α 5 * β 0 +
      (k12 - R 1 2) * α 2 * β 1 +
      (k13 - R 1 3) * α 3 * β 1 +
      (k14 - R 1 4) * α 4 * β 1 +
      (k15 - R 1 5) * α 5 * β 1 +
      (k23 - R 2 3) * α 3 * β 2 +
      (k24 - R 2 4) * α 4 * β 2 +
      (k25 - R 2 5) * α 5 * β 2 +
      (k34 - R 3 4) * α 4 * β 3 +
      (k35 - R 3 5) * α 5 * β 3 +
      (k45 - R 4 5) * α 5 * β 4) ?_
  have e0 := C2_add (α 0) (β 0)
  have e1 := C2_add (α 1) (β 1)
  have e2 := C2_add (α 2) (β 2)
  have e3 := C2_add (α 3) (β 3)
  have e4 := C2_add (α 4) (β 4)
  have e5 := C2_add (α 5) (β 5)
  simp only [cE, ep, q, R, Fin.sum_univ_six, Pi.add_apply, Tp, Gm] at *
  simp only [Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] at *
  rw [e0, e1, e2, e3, e4, e5]
  linear_combination (α 1 * β 0) * h01 +
    (α 2 * β 0) * h02 +
    (α 3 * β 0) * h03 +
    (α 4 * β 0) * h04 +
    (α 5 * β 0) * h05 +
    (α 2 * β 1) * h12 +
    (α 3 * β 1) * h13 +
    (α 4 * β 1) * h14 +
    (α 5 * β 1) * h15 +
    (α 3 * β 2) * h23 +
    (α 4 * β 2) * h24 +
    (α 5 * β 2) * h25 +
    (α 4 * β 3) * h34 +
    (α 5 * β 3) * h35 +
    (α 5 * β 4) * h45

end

end VOA.DeligneAudit.E6Lat
