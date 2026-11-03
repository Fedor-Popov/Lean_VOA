/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Rank-one theta functions `θ_{n₀,r,t}` and their modular transformations

Gannon–Rayhaun (arXiv:2609.00122), eq. (3.15), use the rank-one theta functions
`θ_{n₀,r,t}(τ) = ∑_{n ≡ n₀ (mod r)} q^{t n²}`, `q = e^{2πiτ}`.
The case `θ_{0,1,t}` is the theta series of the lattice `√(2t) ℤ`.

Here `n₀ r : ℤ` and `t : ℝ` (a real `t` is needed: the S-transform of `θ_{0,1,t}` is
`θ_{0,1,1/(4t)}`).

## Main definitions

* `rankOneTheta n₀ r t τ = ∑' m : ℤ, e^{2πi t (n₀ + r m)² τ}`.

## Main results

* `rankOneTheta_eq_jacobiTheta₂`: `θ_{n₀,r,t}(τ) = e^{2πi t n₀² τ} ϑ(2 t r n₀ τ, 2 t r² τ)`,
  where `ϑ = jacobiTheta₂` (unconditional, termwise).
* `tsum_residueClass_eq_rankOneTheta`: the q-expansion as a sum over the residue class.
* `rankOneTheta_S`: for `r ≠ 0`, `t > 0`, `Im τ > 0`,
  `θ_{n₀,r,t}(−1/τ) = (−iτ/(2tr²))^{1/2} ϑ(n₀/r, τ/(2tr²))`.
* `rankOneTheta_S_tsum`: the same, with `ϑ` expanded,
  `= (−iτ/(2tr²))^{1/2} ∑_k e^{2πi k n₀/r} e^{2πi k² τ/(4tr²)}`.
* `rankOneTheta_S_residues`: for `r ≥ 1`, the residue decomposition
  `θ_{n₀,r,t}(−1/τ) = (−iτ/(2tr²))^{1/2} ∑_{j mod r} e^{2πi j n₀/r} θ_{j,r,1/(4tr²)}(τ)`.
* `rankOneTheta_zero_one_S`: `θ_{0,1,t}(−1/τ) = (−iτ/(2t))^{1/2} θ_{0,1,1/(4t)}(τ)`.
* `rankOneTheta_T`: `θ_{n₀,r,t}(τ+1) = θ_{n₀,r,t}(τ)` for integer `t`;
  `rankOneTheta_T_twisted`: `θ_{n₀,r,t}(τ+1) = e^{2πi t n₀²} θ_{n₀,r,t}(τ)` when `t r² ∈ ℤ` and
  `2 t r n₀ ∈ ℤ`.
-/

open Complex Real

noncomputable section

namespace VOA.Classification.COne

/-- The `m`-th term `e^{2πi t (n₀ + r m)² τ}` of `θ_{n₀,r,t}`. -/
def rankOneThetaTerm (n₀ r : ℤ) (t : ℝ) (τ : ℂ) (m : ℤ) : ℂ :=
  cexp (2 * π * I * t * ((n₀ + r * m : ℤ) : ℂ) ^ 2 * τ)

/-- Gannon–Rayhaun's `θ_{n₀,r,t}(τ) = ∑_{n ≡ n₀ (r)} q^{t n²}`, parametrised by `n = n₀ + r m`. -/
def rankOneTheta (n₀ r : ℤ) (t : ℝ) (τ : ℂ) : ℂ :=
  ∑' m : ℤ, rankOneThetaTerm n₀ r t τ m

/-- `θ_{n₀,r,t}` through Mathlib's two-variable Jacobi theta function. -/
theorem rankOneTheta_eq_jacobiTheta₂ (n₀ r : ℤ) (t : ℝ) (τ : ℂ) :
    rankOneTheta n₀ r t τ =
      cexp (2 * π * I * t * (n₀ : ℂ) ^ 2 * τ) *
        jacobiTheta₂ (2 * t * r * n₀ * τ) (2 * t * (r : ℂ) ^ 2 * τ) := by
  rw [rankOneTheta, jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [rankOneThetaTerm, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma im_two_mul_sq_mul_pos {r : ℤ} (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 0 < τ.im) : 0 < (2 * t * (r : ℂ) ^ 2 * τ).im := by
  have : (2 * t * (r : ℂ) ^ 2 * τ) = ((2 * t * (r : ℝ) ^ 2 : ℝ) : ℂ) * τ := by push_cast; ring
  rw [this, Complex.im_ofReal_mul]
  have : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  positivity

/-- The series defining `θ_{n₀,r,t}` converges on the upper half plane. -/
theorem summable_rankOneThetaTerm (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 0 < τ.im) : Summable (rankOneThetaTerm n₀ r t τ) := by
  have h := ((hasSum_jacobiTheta₂_term (2 * t * r * n₀ * τ)
    (im_two_mul_sq_mul_pos hr ht hτ)).summable.mul_left
      (cexp (2 * π * I * t * (n₀ : ℂ) ^ 2 * τ)))
  refine h.congr fun m => ?_
  rw [rankOneThetaTerm, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The parametrisation `m ↦ n₀ + r m` of the residue class `n ≡ n₀ (mod r)`. -/
def residueClassEquiv (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) :
    ℤ ≃ {n : ℤ // n ≡ n₀ [ZMOD r]} where
  toFun m := ⟨n₀ + r * m, by simp [Int.ModEq, Int.add_mul_emod_self_left]⟩
  invFun n := (n.1 - n₀) / r
  left_inv m := by simp [Int.mul_ediv_cancel_left _ hr]
  right_inv n := by
    ext
    simp only
    rw [Int.mul_ediv_cancel' n.2.symm.dvd]
    ring

/-- The q-expansion: `θ_{n₀,r,t}(τ) = ∑_{n ≡ n₀ (mod r)} q^{t n²}`. -/
theorem tsum_residueClass_eq_rankOneTheta (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) (t : ℝ) (τ : ℂ) :
    ∑' n : {n : ℤ // n ≡ n₀ [ZMOD r]}, cexp (2 * π * I * t * (n.1 : ℂ) ^ 2 * τ) =
      rankOneTheta n₀ r t τ := by
  rw [rankOneTheta, ← (residueClassEquiv n₀ hr).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [rankOneThetaTerm, residueClassEquiv, Equiv.coe_fn_mk]

/-- **S-transformation** of `θ_{n₀,r,t}`. -/
theorem rankOneTheta_S (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 0 < τ.im) :
    rankOneTheta n₀ r t (-1 / τ) =
      (-I * (τ / (2 * t * (r : ℂ) ^ 2))) ^ (1 / 2 : ℂ) *
        jacobiTheta₂ ((n₀ : ℂ) / r) (τ / (2 * t * (r : ℂ) ^ 2)) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hr0 : (r : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  set τ' : ℂ := τ / (2 * t * (r : ℂ) ^ 2) with hτ'
  set a : ℂ := (n₀ : ℂ) / r with ha
  have hs : (-I * τ') ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    simp only [neg_mul, neg_eq_zero, mul_eq_zero, I_ne_zero, false_or, hτ', div_eq_zero_iff,
      hτ0, OfNat.ofNat_ne_zero, ht0] at h
    exact hr0 ((pow_eq_zero_iff two_ne_zero).mp h)
  have hfe := jacobiTheta₂_functional_equation a τ'
  have e1 : (2 * t * r * n₀ * (-1 / τ) : ℂ) = -(a / τ') := by
    rw [hτ', ha]; field_simp
  have e2 : (2 * t * (r : ℂ) ^ 2 * (-1 / τ) : ℂ) = -1 / τ' := by
    rw [hτ']; field_simp
  rw [rankOneTheta_eq_jacobiTheta₂, e1, e2, jacobiTheta₂_neg_left, hfe, ← mul_assoc, ← mul_assoc,
    mul_one_div_cancel hs, one_mul]
  congr 2
  rw [hτ', ha]
  field_simp

/-- The S-transformation with the theta series written out. -/
theorem rankOneTheta_S_tsum (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 0 < τ.im) :
    rankOneTheta n₀ r t (-1 / τ) =
      (-I * (τ / (2 * t * (r : ℂ) ^ 2))) ^ (1 / 2 : ℂ) *
        ∑' k : ℤ, cexp (2 * π * I * k * n₀ / r) *
          cexp (2 * π * I * τ * (k : ℂ) ^ 2 / (4 * t * (r : ℂ) ^ 2)) := by
  rw [rankOneTheta_S n₀ hr ht hτ, jacobiTheta₂]
  congr 1
  refine tsum_congr fun k => ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  have hr0 : (r : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  congr 1
  field_simp
  ring

/-- The S-transformation, decomposed into residues `k ≡ j (mod r)`:
`θ_{n₀,r,t}(−1/τ) = (−iτ/(2tr²))^{1/2} ∑_{j mod r} e^{2πi j n₀/r} θ_{j,r,1/(4tr²)}(τ)`. -/
theorem rankOneTheta_S_residues (n₀ : ℤ) (r : ℕ) [NeZero r] {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 0 < τ.im) :
    rankOneTheta n₀ r t (-1 / τ) =
      (-I * (τ / (2 * t * ((r : ℤ) : ℂ) ^ 2))) ^ (1 / 2 : ℂ) *
        ∑ j : Fin r, cexp (2 * π * I * (j : ℕ) * n₀ / r) *
          rankOneTheta (j : ℕ) r (1 / (4 * t * (r : ℝ) ^ 2)) τ := by
  have hr : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne r)
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have ht' : 0 < 1 / (4 * t * (r : ℝ) ^ 2) := by
    have : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne r))
    positivity
  rw [rankOneTheta_S_tsum n₀ hr ht hτ]
  congr 1
  set f : ℤ → ℂ := fun k => cexp (2 * π * I * k * n₀ / ((r : ℤ) : ℂ)) *
    cexp (2 * π * I * τ * (k : ℂ) ^ 2 / (4 * t * ((r : ℤ) : ℂ) ^ 2)) with hf
  -- the summand at `k = m r + j`
  have hterm : ∀ (j : Fin r) (m : ℤ), f ((Int.divModEquiv r).symm (m, j)) =
      cexp (2 * π * I * (j : ℕ) * n₀ / r) *
        rankOneThetaTerm (j : ℕ) r (1 / (4 * t * (r : ℝ) ^ 2)) τ m := by
    intro j m
    simp only [hf, Int.divModEquiv_symm_apply, rankOneThetaTerm]
    have hint : cexp (2 * π * I * ((m * r + ((j : ℕ) : ℤ) : ℤ) : ℂ) * n₀ / ((r : ℤ) : ℂ)) =
        cexp (2 * π * I * (j : ℕ) * n₀ / r) := by
      have : (2 * π * I * ((m * r + ((j : ℕ) : ℤ) : ℤ) : ℂ) * n₀ / ((r : ℤ) : ℂ)) =
          2 * π * I * (j : ℕ) * n₀ / r + (m * n₀ : ℤ) * (2 * π * I) := by
        push_cast; field_simp; ring
      rw [this, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    rw [hint]
    congr 2
    push_cast
    field_simp
    ring
  have hsum : Summable f := by
    have h := (hasSum_jacobiTheta₂_term ((n₀ : ℂ) / ((r : ℤ) : ℂ))
      (τ := τ / (2 * t * ((r : ℤ) : ℂ) ^ 2)) ?_).summable
    · refine h.congr fun k => ?_
      simp only [hf, jacobiTheta₂_term, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    · have : τ / (2 * t * ((r : ℤ) : ℂ) ^ 2) = ((1 / (2 * t * (r : ℝ) ^ 2) : ℝ) : ℂ) * τ := by
        push_cast; field_simp
      rw [this, Complex.im_ofReal_mul]
      have : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne r))
      positivity
  -- reindex `ℤ ≃ ℤ × Fin r`, then sum fibrewise over `Fin r`
  have hprod : HasSum (fun p : Fin r × ℤ => f ((Int.divModEquiv r).symm (p.2, p.1)))
      (∑' k, f k) := by
    have := ((Int.divModEquiv r).symm.hasSum_iff.mpr hsum.hasSum)
    exact (Equiv.prodComm (Fin r) ℤ).hasSum_iff.mpr this
  have hfib : ∀ j : Fin r, HasSum (fun m : ℤ => f ((Int.divModEquiv r).symm (m, j)))
      (cexp (2 * π * I * (j : ℕ) * n₀ / r) *
        rankOneTheta (j : ℕ) r (1 / (4 * t * (r : ℝ) ^ 2)) τ) := by
    intro j
    simp_rw [hterm]
    exact ((summable_rankOneThetaTerm (j : ℕ) hr ht' hτ).hasSum).mul_left _
  exact ((hprod.prod_fiberwise hfib).unique (hasSum_fintype _)).trans (by simp)

/-- The lattice case: `θ_{0,1,t}(−1/τ) = (−iτ/(2t))^{1/2} θ_{0,1,1/(4t)}(τ)`. -/
theorem rankOneTheta_zero_one_S {t : ℝ} (ht : 0 < t) {τ : ℂ} (hτ : 0 < τ.im) :
    rankOneTheta 0 1 t (-1 / τ) =
      (-I * (τ / (2 * t))) ^ (1 / 2 : ℂ) * rankOneTheta 0 1 (1 / (4 * t)) τ := by
  have h := rankOneTheta_S (0 : ℤ) one_ne_zero ht hτ
  simp only [Int.cast_one, one_pow, mul_one, Int.cast_zero, zero_div] at h
  rw [h, jacobiTheta₂, rankOneTheta]
  congr 1
  refine tsum_congr fun m => ?_
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [jacobiTheta₂_term, rankOneThetaTerm]
  congr 1
  push_cast
  field_simp
  ring

/-- **T-transformation**, twisted form: if `t r² ∈ ℤ` and `2 t r n₀ ∈ ℤ`, then
`θ_{n₀,r,t}(τ + 1) = e^{2πi t n₀²} θ_{n₀,r,t}(τ)`. -/
theorem rankOneTheta_T_twisted (n₀ r : ℤ) (t : ℝ) (a b : ℤ) (ha : t * r ^ 2 = a)
    (hb : 2 * t * r * n₀ = b) (τ : ℂ) :
    rankOneTheta n₀ r t (τ + 1) = cexp (2 * π * I * t * (n₀ : ℂ) ^ 2) * rankOneTheta n₀ r t τ := by
  rw [rankOneTheta, rankOneTheta, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [rankOneThetaTerm, rankOneThetaTerm, ← Complex.exp_add]
  have ha' : (t : ℂ) * (r : ℂ) ^ 2 = a := by exact_mod_cast ha
  have hb' : 2 * (t : ℂ) * r * n₀ = b := by exact_mod_cast hb
  have : 2 * π * I * t * ((n₀ + r * m : ℤ) : ℂ) ^ 2 * (τ + 1) =
      2 * π * I * t * (n₀ : ℂ) ^ 2 + 2 * π * I * t * ((n₀ + r * m : ℤ) : ℂ) ^ 2 * τ +
        (a * m ^ 2 + b * m : ℤ) * (2 * π * I) := by
    push_cast
    rw [← ha', ← hb']
    ring
  rw [this, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- **T-transformation** for integer `t`: `θ_{n₀,r,t}(τ + 1) = θ_{n₀,r,t}(τ)`. -/
theorem rankOneTheta_T (n₀ r t : ℤ) (τ : ℂ) :
    rankOneTheta n₀ r t (τ + 1) = rankOneTheta n₀ r t τ := by
  rw [rankOneTheta_T_twisted n₀ r t (t * r ^ 2) (2 * t * r * n₀) (by push_cast; ring)
    (by push_cast; ring)]
  have : 2 * π * I * ((t : ℝ) : ℂ) * (n₀ : ℂ) ^ 2 = (t * n₀ ^ 2 : ℤ) * (2 * π * I) := by
    push_cast; ring
  rw [this, exp_int_mul_two_pi_mul_I, one_mul]

end VOA.Classification.COne
