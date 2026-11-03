/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelJet
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The polynomial image `A_r` and its stability under the mode derivations

The generators of the polynomial image are the jet series

  `X = u², Y = uv, Z = v², J = u'v - uv'`

(physical normalization `e = X, f = -Z, h = -2Y, T = -J`). Their coefficients span `genSpan`,
and `A_r = genSpan ^ r` (`jetImage r`) is the span of products of `r` generator coefficients.

* `serD D` — a derivation applied coefficientwise to jet series (Leibniz, commutes with `d/ds`);
* `serD_colSer_*` — the action on `u(s), v(s)`: `e_m v = s^m u`, `f_m u = s^m v`,
  `h_m u = s^m u`, `h_m v = -s^m v`;
* `inGen_serD` — every mode derivation maps each generator series to a series with
  coefficients in `genSpan` (the twelve formulas of the note, e.g. `e_m J = -m s^{m-1} X`);
* `jetDer_jetImage` — the mode derivations preserve `A_r`.

Everything is proved outright.
-/

namespace VOA.SymbolModel

open MvPolynomial

noncomputable section

/-- Jet series `Σ_j p_j s^j` with jet-polynomial coefficients. -/
abbrev JetSer : Type := PowerSeries JetPoly

/-- The formal variable `s`. -/
abbrev sX : JetSer := PowerSeries.X

/-- `d/ds`. -/
abbrev dS : Derivation JetPoly JetSer JetSer := PowerSeries.derivative JetPoly

/-- The column series: `u(s)` for `b = 0`, `v(s)` for `b = 1`. -/
def colSer (b : Fin 2) : JetSer := PowerSeries.mk fun j => X (b, j)

/-- `X = u²`. -/
def xSer : JetSer := colSer 0 * colSer 0
/-- `Y = uv`. -/
def ySer : JetSer := colSer 0 * colSer 1
/-- `Z = v²`. -/
def zSer : JetSer := colSer 1 * colSer 1
/-- `J = u'v - uv'`. -/
def jSer : JetSer := dS (colSer 0) * colSer 1 - colSer 0 * dS (colSer 1)

/-- The four generator series. -/
def genSer (g : Fin 4) : JetSer := ![xSer, ySer, zSer, jSer] g

/-- The coefficients of the generator series. -/
def genCoeff (g : Fin 4) (a : ℕ) : JetPoly := PowerSeries.coeff a (genSer g)

/-- The span of all generator coefficients. -/
def genSpan : Submodule ℂ JetPoly :=
  Submodule.span ℂ (Set.range fun p : Fin 4 × ℕ => genCoeff p.1 p.2)

/-- **The polynomial image `A_r`**: the span of products of `r` generator coefficients. -/
def jetImage (r : ℕ) : Submodule ℂ JetPoly := genSpan ^ r

/-! ### Coefficientwise derivations -/

/-- A linear map applied coefficientwise to a jet series. -/
def serD (D : JetPoly →ₗ[ℂ] JetPoly) (f : JetSer) : JetSer :=
  PowerSeries.mk fun n => D (PowerSeries.coeff n f)

@[simp] theorem coeff_serD (D : JetPoly →ₗ[ℂ] JetPoly) (f : JetSer) (n : ℕ) :
    PowerSeries.coeff n (serD D f) = D (PowerSeries.coeff n f) := PowerSeries.coeff_mk _ _

theorem serD_add (D : JetPoly →ₗ[ℂ] JetPoly) (f g : JetSer) :
    serD D (f + g) = serD D f + serD D g := by
  ext n; simp

theorem serD_sub (D : JetPoly →ₗ[ℂ] JetPoly) (f g : JetSer) :
    serD D (f - g) = serD D f - serD D g := by
  ext n; simp

theorem serD_neg (D : JetPoly →ₗ[ℂ] JetPoly) (f : JetSer) : serD D (-f) = -serD D f := by
  ext n; simp

theorem serD_mul (D : Derivation ℂ JetPoly JetPoly) (f g : JetSer) :
    serD D (f * g) = serD D f * g + f * serD D g := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_serD, PowerSeries.coeff_mul, map_add, map_sum, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem serD_derivative (D : Derivation ℂ JetPoly JetPoly) (f : JetSer) :
    serD D (dS f) = dS (serD D f) := by
  ext n
  simp only [coeff_serD, PowerSeries.coeff_derivative, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul]
  have h : D ((n : JetPoly) + 1) = 0 := by
    rw [show ((n : JetPoly) + 1) = ((n + 1 : ℕ) : JetPoly) by push_cast; ring]
    exact D.map_natCast _
  rw [h, mul_zero, zero_add, mul_comm]

theorem serD_X_pow_mul (D : JetPoly →ₗ[ℂ] JetPoly) (m : ℕ) (f : JetSer) :
    serD D (sX ^ m * f) = sX ^ m * serD D f := by
  ext n
  simp only [coeff_serD, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

theorem serD_zero (D : JetPoly →ₗ[ℂ] JetPoly) : serD D 0 = 0 := by
  ext n; simp

/-! ### The action on `u(s)`, `v(s)` -/

theorem coeff_X_pow_mul_colSer (m : ℕ) (b : Fin 2) (n : ℕ) :
    PowerSeries.coeff n (sX ^ m * colSer b) = shiftVar b m n := by
  rw [PowerSeries.coeff_X_pow_mul', shiftVar, colSer]
  split_ifs <;> simp

theorem serD_e_u (m : ℕ) : serD (jetDer (0, m)).toLinearMap (colSer 0) = 0 := by
  ext n; simp [colSer, jetDerVal]

theorem serD_e_v (m : ℕ) : serD (jetDer (0, m)).toLinearMap (colSer 1) = sX ^ m * colSer 0 := by
  ext n; rw [coeff_X_pow_mul_colSer]; simp [colSer, jetDerVal]

theorem serD_f_u (m : ℕ) : serD (jetDer (1, m)).toLinearMap (colSer 0) = sX ^ m * colSer 1 := by
  ext n; rw [coeff_X_pow_mul_colSer]; simp [colSer, jetDerVal]

theorem serD_f_v (m : ℕ) : serD (jetDer (1, m)).toLinearMap (colSer 1) = 0 := by
  ext n; simp [colSer, jetDerVal]

theorem serD_h_u (m : ℕ) : serD (jetDer (2, m)).toLinearMap (colSer 0) = sX ^ m * colSer 0 := by
  ext n; rw [coeff_X_pow_mul_colSer]; simp [colSer, jetDerVal]

theorem serD_h_v (m : ℕ) :
    serD (jetDer (2, m)).toLinearMap (colSer 1) = -(sX ^ m * colSer 1) := by
  ext n; rw [map_neg, coeff_X_pow_mul_colSer]; simp [colSer, jetDerVal]

/-! ### Series with coefficients in `genSpan` -/

/-- All coefficients lie in `genSpan`. -/
def InGen (f : JetSer) : Prop := ∀ n, PowerSeries.coeff n f ∈ genSpan

theorem inGen_gen (g : Fin 4) : InGen (genSer g) := fun n =>
  Submodule.subset_span ⟨(g, n), rfl⟩

theorem inGen_zero : InGen 0 := fun n => by simp

theorem inGen_add {f g : JetSer} (hf : InGen f) (hg : InGen g) : InGen (f + g) := fun n => by
  rw [map_add]; exact add_mem (hf n) (hg n)

theorem inGen_neg {f : JetSer} (hf : InGen f) : InGen (-f) := fun n => by
  rw [map_neg]; exact neg_mem (hf n)

theorem inGen_nsmul {f : JetSer} (k : ℕ) (hf : InGen f) : InGen (k • f) := fun n => by
  rw [map_nsmul]; exact nsmul_mem (hf n) k

theorem inGen_X_pow_mul {f : JetSer} (m : ℕ) (hf : InGen f) : InGen (sX ^ m * f) := fun n => by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs
  · exact hf _
  · exact Submodule.zero_mem _

theorem dS_X_pow (m : ℕ) : dS (sX ^ m) = m • sX ^ (m - 1) := by
  rw [Derivation.leibniz_pow, PowerSeries.derivative_X, smul_eq_mul, mul_one]

theorem inGen_dX_pow_mul {f : JetSer} (m : ℕ) (hf : InGen f) : InGen (dS (sX ^ m) * f) := by
  rw [dS_X_pow, smul_mul_assoc]
  exact inGen_nsmul m (inGen_X_pow_mul _ hf)

/-! ### The twelve generator formulas -/

theorem genSer_zero : genSer 0 = xSer := rfl
theorem genSer_one : genSer 1 = ySer := rfl
theorem genSer_two : genSer 2 = zSer := rfl
theorem genSer_three : genSer 3 = jSer := rfl

section Formulas

variable (D : Derivation ℂ JetPoly JetPoly)

theorem serD_xSer : serD D xSer =
    serD D (colSer 0) * colSer 0 + colSer 0 * serD D (colSer 0) := serD_mul _ _ _

theorem serD_ySer : serD D ySer =
    serD D (colSer 0) * colSer 1 + colSer 0 * serD D (colSer 1) := serD_mul _ _ _

theorem serD_zSer : serD D zSer =
    serD D (colSer 1) * colSer 1 + colSer 1 * serD D (colSer 1) := serD_mul _ _ _

theorem serD_jSer : serD D jSer =
    dS (serD D (colSer 0)) * colSer 1 + dS (colSer 0) * serD D (colSer 1) -
      (serD D (colSer 0) * dS (colSer 1) + colSer 0 * dS (serD D (colSer 1))) := by
  rw [jSer, serD_sub, serD_mul, serD_mul, serD_derivative, serD_derivative]

end Formulas

theorem inGen_serD_e (m : ℕ) (g : Fin 4) :
    InGen (serD (jetDer (0, m)).toLinearMap (genSer g)) := by
  fin_cases g
  · change InGen (serD _ xSer)
    rw [serD_xSer, serD_e_u]; simpa using inGen_zero
  · change InGen (serD _ ySer)
    rw [serD_ySer, serD_e_u, serD_e_v]
    have : (0 : JetSer) * colSer 1 + colSer 0 * (sX ^ m * colSer 0) = sX ^ m * genSer 0 := by
      rw [genSer_zero, xSer]; ring
    rw [this]; exact inGen_X_pow_mul m (inGen_gen 0)
  · change InGen (serD _ zSer)
    rw [serD_zSer, serD_e_v]
    have : sX ^ m * colSer 0 * colSer 1 + colSer 1 * (sX ^ m * colSer 0) =
        sX ^ m * genSer 1 + sX ^ m * genSer 1 := by
      rw [genSer_one, ySer]; ring
    rw [this]; exact inGen_add (inGen_X_pow_mul m (inGen_gen 1)) (inGen_X_pow_mul m (inGen_gen 1))
  · change InGen (serD _ jSer)
    rw [serD_jSer, serD_e_u, serD_e_v, map_zero, Derivation.leibniz]
    have : (0 : JetSer) * colSer 1 + dS (colSer 0) * (sX ^ m * colSer 0) -
        (0 * dS (colSer 1) + colSer 0 * (sX ^ m • dS (colSer 0) + colSer 0 • dS (sX ^ m))) =
        -(dS (sX ^ m) * genSer 0) := by
      rw [genSer_zero, xSer, smul_eq_mul, smul_eq_mul]; ring
    rw [this]; exact inGen_neg (inGen_dX_pow_mul m (inGen_gen 0))

theorem inGen_serD_f (m : ℕ) (g : Fin 4) :
    InGen (serD (jetDer (1, m)).toLinearMap (genSer g)) := by
  fin_cases g
  · change InGen (serD _ xSer)
    rw [serD_xSer, serD_f_u]
    have : sX ^ m * colSer 1 * colSer 0 + colSer 0 * (sX ^ m * colSer 1) =
        sX ^ m * genSer 1 + sX ^ m * genSer 1 := by
      rw [genSer_one, ySer]; ring
    rw [this]; exact inGen_add (inGen_X_pow_mul m (inGen_gen 1)) (inGen_X_pow_mul m (inGen_gen 1))
  · change InGen (serD _ ySer)
    rw [serD_ySer, serD_f_u, serD_f_v]
    have : sX ^ m * colSer 1 * colSer 1 + colSer 0 * 0 = sX ^ m * genSer 2 := by
      rw [genSer_two, zSer]; ring
    rw [this]; exact inGen_X_pow_mul m (inGen_gen 2)
  · change InGen (serD _ zSer)
    rw [serD_zSer, serD_f_v]; simpa using inGen_zero
  · change InGen (serD _ jSer)
    rw [serD_jSer, serD_f_u, serD_f_v, map_zero, Derivation.leibniz]
    have : (sX ^ m • dS (colSer 1) + colSer 1 • dS (sX ^ m)) * colSer 1 + dS (colSer 0) * 0 -
        (sX ^ m * colSer 1 * dS (colSer 1) + colSer 0 * 0) = dS (sX ^ m) * genSer 2 := by
      rw [genSer_two, zSer, smul_eq_mul, smul_eq_mul]; ring
    rw [this]; exact inGen_dX_pow_mul m (inGen_gen 2)

theorem inGen_serD_h (m : ℕ) (g : Fin 4) :
    InGen (serD (jetDer (2, m)).toLinearMap (genSer g)) := by
  fin_cases g
  · change InGen (serD _ xSer)
    rw [serD_xSer, serD_h_u]
    have : sX ^ m * colSer 0 * colSer 0 + colSer 0 * (sX ^ m * colSer 0) =
        sX ^ m * genSer 0 + sX ^ m * genSer 0 := by
      rw [genSer_zero, xSer]; ring
    rw [this]; exact inGen_add (inGen_X_pow_mul m (inGen_gen 0)) (inGen_X_pow_mul m (inGen_gen 0))
  · change InGen (serD _ ySer)
    rw [serD_ySer, serD_h_u, serD_h_v]
    have : sX ^ m * colSer 0 * colSer 1 + colSer 0 * -(sX ^ m * colSer 1) = 0 := by ring
    rw [this]; exact inGen_zero
  · change InGen (serD _ zSer)
    rw [serD_zSer, serD_h_v]
    have : -(sX ^ m * colSer 1) * colSer 1 + colSer 1 * -(sX ^ m * colSer 1) =
        -(sX ^ m * genSer 2 + sX ^ m * genSer 2) := by
      rw [genSer_two, zSer]; ring
    rw [this]
    exact inGen_neg (inGen_add (inGen_X_pow_mul m (inGen_gen 2)) (inGen_X_pow_mul m (inGen_gen 2)))
  · change InGen (serD _ jSer)
    rw [serD_jSer, serD_h_u, serD_h_v, map_neg, Derivation.leibniz, Derivation.leibniz]
    have : (sX ^ m • dS (colSer 0) + colSer 0 • dS (sX ^ m)) * colSer 1 +
        dS (colSer 0) * -(sX ^ m * colSer 1) -
        (sX ^ m * colSer 0 * dS (colSer 1) +
          colSer 0 * -(sX ^ m • dS (colSer 1) + colSer 1 • dS (sX ^ m))) =
        dS (sX ^ m) * genSer 1 + dS (sX ^ m) * genSer 1 := by
      rw [genSer_one, ySer, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]; ring
    rw [this]; exact inGen_add (inGen_dX_pow_mul m (inGen_gen 1)) (inGen_dX_pow_mul m (inGen_gen 1))

/-- **The mode derivations preserve the generator series' span.** -/
theorem inGen_serD (k : Fin 3 × ℕ) (g : Fin 4) :
    InGen (serD (jetDer k).toLinearMap (genSer g)) := by
  obtain ⟨a, m⟩ := k
  fin_cases a
  · exact inGen_serD_e m g
  · exact inGen_serD_f m g
  · exact inGen_serD_h m g

theorem jetDer_genCoeff (k : Fin 3 × ℕ) (g : Fin 4) (a : ℕ) :
    jetDer k (genCoeff g a) = PowerSeries.coeff a (serD (jetDer k).toLinearMap (genSer g)) := by
  rw [coeff_serD]; rfl

theorem jetDer_genSpan (k : Fin 3 × ℕ) : ∀ x ∈ genSpan, jetDer k x ∈ genSpan := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, a⟩, rfl⟩ := hx
    rw [jetDer_genCoeff]; exact inGen_serD k g a
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Derivation.map_smul]; exact Submodule.smul_mem _ c hx

/-- **The mode derivations preserve `A_r`.** -/
theorem jetDer_jetImage (k : Fin 3 × ℕ) (r : ℕ) : ∀ x ∈ jetImage r, jetDer k x ∈ jetImage r := by
  induction r with
  | zero =>
    intro x hx
    rw [jetImage, pow_zero, Submodule.mem_one] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [Derivation.map_algebraMap]; exact Submodule.zero_mem _
  | succ r ih =>
    intro x hx
    rw [jetImage, pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine add_mem (Submodule.mul_mem_mul hm (jetDer_genSpan k n hn)) ?_
      rw [mul_comm n]
      exact Submodule.mul_mem_mul (ih m hm) hn
    · intro x y hx hy; rw [map_add]; exact add_mem hx hy

end

end VOA.SymbolModel
