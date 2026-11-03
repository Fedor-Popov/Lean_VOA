/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# Euler series over `𝕜 = ℚ((q))` (D₄ kernel, layer 1)

The coefficient field is `𝕜 = LaurentSeries ℚ` in `r = q^{1/2}` (`rr`), with `q = qq = r²`.  The two Euler series

  `eInv = ∑_n yⁿ/(q;q)_n = 1/(y;q)_∞`,   `ePos = ∑_n (-1)ⁿ q^{n(n-1)/2} yⁿ/(q;q)_n = (y;q)_∞`

are power series in `y` over `𝕜`.  Their defining `q`-difference equations

  `eInv · (1 - y) = eInv(qy)`,   `ePos = (1 - y) · ePos(qy)`,   `ePos · eInv = 1`

are proved here coefficientwise.  Later layers transport them along `rescale` and `expand` to the
factors `(c z^v s^k; q)_∞^{±1}` of the D₄ kernel.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- The coefficient field `ℚ((q))`. -/
abbrev Kq := LaurentSeries ℚ

/-- `r = q^{1/2}`: the series variable of `Kq`, so that `√q`-shifts are ring homomorphisms. -/
def rr : Kq := HahnSeries.single 1 1

/-- The nome `q = r²`. -/
def qq : Kq := HahnSeries.single 2 1

theorem rr_ne_zero : rr ≠ 0 := by simp [rr]

theorem qq_eq_rr_sq : qq = rr ^ 2 := by
  rw [qq, rr, HahnSeries.single_pow]; norm_num

theorem qq_ne_zero : qq ≠ 0 := by simp [qq]

theorem qq_pow (n : ℕ) : qq ^ n = HahnSeries.single (2 * n : ℤ) 1 := by
  rw [qq, HahnSeries.single_pow]; simp [mul_comm]

theorem one_sub_qq_pow_ne_zero (n : ℕ) (hn : n ≠ 0) : (1 : Kq) - qq ^ n ≠ 0 := by
  rw [sub_ne_zero, qq_pow]
  intro h
  have := congrArg (fun f : Kq => f.coeff 0) h
  simp [HahnSeries.coeff_single] at this
  omega

/-- `(q;q)_n`. -/
def qpoch (n : ℕ) : Kq := ∏ i ∈ Finset.range n, (1 - qq ^ (i + 1))

theorem qpoch_succ (n : ℕ) : qpoch (n + 1) = qpoch n * (1 - qq ^ (n + 1)) := by
  rw [qpoch, Finset.prod_range_succ, ← qpoch]

theorem qpoch_ne_zero (n : ℕ) : qpoch n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => one_sub_qq_pow_ne_zero (i + 1) (Nat.succ_ne_zero i)

/-- `1/(y;q)_∞ = ∑ yⁿ/(q;q)_n`. -/
def eInv : PowerSeries Kq := mk fun n => (qpoch n)⁻¹

/-- `(y;q)_∞ = ∑ (-1)ⁿ q^{n(n-1)/2} yⁿ/(q;q)_n`. -/
def ePos : PowerSeries Kq := mk fun n => (-1) ^ n * qq ^ (n * (n - 1) / 2) * (qpoch n)⁻¹

theorem eInv_mul_one_sub : eInv * (1 - X) = rescale qq eInv := by
  refine PowerSeries.ext fun n => ?_
  rw [mul_sub, mul_one, map_sub, coeff_rescale]
  rcases n with _ | n
  · simp [eInv, coeff_zero_eq_constantCoeff]
  · rw [coeff_succ_mul_X, eInv, coeff_mk, coeff_mk, qpoch_succ]
    have h1 := qpoch_ne_zero n
    have h2 := one_sub_qq_pow_ne_zero (n + 1) (Nat.succ_ne_zero n)
    field_simp
    exact sub_sub_cancel _ _

theorem ePos_eq : ePos = (1 - X) * rescale qq ePos := by
  refine PowerSeries.ext fun n => ?_
  rw [sub_mul, one_mul, map_sub, coeff_rescale]
  rcases n with _ | n
  · simp [ePos, coeff_zero_eq_constantCoeff]
  · rw [mul_comm X, coeff_succ_mul_X, coeff_rescale, ePos, coeff_mk, coeff_mk, qpoch_succ]
    have h1 := qpoch_ne_zero n
    have h2 := one_sub_qq_pow_ne_zero (n + 1) (Nat.succ_ne_zero n)
    have hexp : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]
        have : (n + 1 + 1) * (n + 1) = n * (n + 1) + 2 * (n + 1) := by ring
        rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
        simp [mul_comm]
    rw [hexp]
    field_simp
    ring

theorem ePos_mul_eInv : ePos * eInv = 1 := by
  set u := ePos * eInv with hu
  have hfix : rescale qq u = u := by
    rw [hu, map_mul]
    calc rescale qq ePos * rescale qq eInv = rescale qq ePos * (eInv * (1 - X)) := by
          rw [eInv_mul_one_sub]
      _ = ((1 - X) * rescale qq ePos) * eInv := by ring
      _ = ePos * eInv := by rw [← ePos_eq]
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) hfix
  rw [coeff_rescale] at hn
  rcases n with _ | n
  · simp [hu, ePos, eInv, coeff_zero_eq_constantCoeff, qpoch]
  · rw [coeff_one, if_neg (Nat.succ_ne_zero n)]
    have h2 := one_sub_qq_pow_ne_zero (n + 1) (Nat.succ_ne_zero n)
    have : (1 - qq ^ (n + 1)) * coeff (n + 1) u = 0 := by rw [sub_mul, one_mul, hn, sub_self]
    exact (mul_eq_zero.mp this).resolve_left h2

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.eInv_mul_one_sub
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.ePos_eq
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.ePos_mul_eInv
end AxiomAudit
