/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Assembly2

/-!
# Solving the D₄ recursion (layer 7, part 3)

With `B_R = π_{s_θ} π₀` on `R` and the Demazure characters `C_m = q^{m²} B_R^m(1)`:

* `Ikernel_coeff_odd`: the odd `s`-coefficients of `2I` vanish;
* **`Ikernel_coeff_even`**: `[s^{2m}] 2I = (2/(q;q)_m) · C_m`.

So, conditional only on `D4F.D4FiniteIdentity`, the flavoured two-variable D₄ identity holds:
`CT_x Θ(x) M(s, x, z) = 2 ∑_m t^m C_m(q, z)/(q;q)_m`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- `π_{s_θ}` on `R`. -/
def piThetaR (f : R) : R := wordS.foldl (fun g i => piR (rootV i) g) f

/-- `B_R = π_{s_θ} π₀` on `R`. -/
def BR (f : R) : R := piThetaR (pi0R f)

theorem coeff_piThetaS (G : S) (n : ℕ) : coeff n (piThetaS G) = piThetaR (coeff n G) := by
  unfold piThetaS piThetaR
  generalize wordS = w
  induction w generalizing G with
  | nil => rfl
  | cons i w ih => simp only [List.foldl_cons]; rw [ih, coeff_smap]

theorem coeff_Bop (F : S) (n : ℕ) : coeff n (Bop F) = BR (coeff n F) := by
  rw [Bop, coeff_piThetaS, coeff_smap]; rfl

theorem piThetaR_smul (c : Kq) (f : R) : piThetaR (c • f) = c • piThetaR f := by
  unfold piThetaR
  generalize wordS = w
  induction w generalizing f with
  | nil => rfl
  | cons i w ih => simp only [List.foldl_cons]; rw [map_smul, ih]

theorem BR_smul (c : Kq) (f : R) : BR (c • f) = c • BR f := by
  rw [BR, map_smul, piThetaR_smul]; rfl

/-- **The level-one Demazure character** `C_m = q^{m²} B^m(1)` (in `R`, `x`-free). -/
def Cdem (m : ℕ) : R := qq ^ (m * m) • (BR^[m] 1)

theorem Cdem_succ (m : ℕ) : Cdem (m + 1) = qq ^ (2 * m + 1) • BR (Cdem m) := by
  rw [Cdem, Cdem, Function.iterate_succ_apply', BR_smul, smul_smul, ← pow_add]
  congr 2
  ring

theorem coeff_Ikernel_zero : coeff 0 Ikernel = mon 0 2 := by
  rw [Ikernel, coeff_smap, coeff_zero_eq_constantCoeff_apply, constantCoeff_kernelM]
  rw [show (1 : R) = mon 0 1 from rfl, ctFun_mon]
  simp [killX, thK_zero]

theorem rr_pow_ne_one (n : ℕ) (hn : n ≠ 0) : (1 : Kq) - rr ^ n ≠ 0 := by
  rw [sub_ne_zero, rr, HahnSeries.single_pow]
  intro h
  have := congrArg (fun f : Kq => f.coeff 0) h
  simp [HahnSeries.coeff_single] at this
  omega

/-- The coefficientwise recursion. -/
theorem Ikernel_coeff_rec (hF : D4F.D4FiniteIdentity) (n : ℕ) :
    (1 - rr ^ (n + 2)) • coeff (n + 2) Ikernel = qq ^ (n + 1) • BR (coeff n Ikernel) := by
  have h := congrArg (coeff (n + 2)) (Ikernel_recursion hF)
  have e1 : coeff (n + 2) (rescale (algebraMap Kq R rr) Ikernel) =
      rr ^ (n + 2) • coeff (n + 2) Ikernel := by
    rw [coeff_rescale, ← map_pow, Algebra.smul_def]
  have e2 : coeff (n + 2) (C (algebraMap Kq R qq) * X ^ 2 *
      Bop (rescale (algebraMap Kq R qq) Ikernel)) = qq ^ (n + 1) • BR (coeff n Ikernel) := by
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega),
      show n + 2 - 2 = n by omega, coeff_Bop, coeff_rescale, ← map_pow,
      ← Algebra.smul_def (qq ^ n), BR_smul, ← Algebra.smul_def, smul_smul, ← pow_succ']
  rw [map_sub, e1, e2] at h
  rw [sub_smul, one_smul, h]

theorem Ikernel_coeff_one (hF : D4F.D4FiniteIdentity) : coeff 1 Ikernel = 0 := by
  have h := congrArg (coeff 1) (Ikernel_recursion hF)
  rw [map_sub, coeff_rescale, mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega),
    mul_zero, pow_one] at h
  have h' : (1 - rr) • coeff 1 Ikernel = 0 := by
    rw [sub_smul, one_smul, Algebra.smul_def, h]
  rcases smul_eq_zero.mp h' with h0 | h0
  · exact absurd h0 (by simpa using rr_pow_ne_one 1 one_ne_zero)
  · exact h0

theorem Ikernel_coeff_odd (hF : D4F.D4FiniteIdentity) (k : ℕ) :
    coeff (2 * k + 1) Ikernel = 0 := by
  induction k with
  | zero => exact Ikernel_coeff_one hF
  | succ k ih =>
      have h := Ikernel_coeff_rec hF (2 * k + 1)
      rw [ih, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring] at h
      have hb : BR 0 = 0 := by rw [BR, map_zero]; unfold piThetaR; generalize wordS = w; induction w with
        | nil => rfl
        | cons i w ih' => simp only [List.foldl_cons, map_zero]; exact ih'
      rw [hb, smul_zero] at h
      rcases smul_eq_zero.mp h with h0 | h0
      · exact absurd h0 (rr_pow_ne_one _ (by omega))
      · exact h0

/-- **The flavoured two-variable D₄ identity**, coefficientwise:
`[s^{2m}] CT_x Θ M = (2/(q;q)_m) · C_m`. -/
theorem Ikernel_coeff_even (hF : D4F.D4FiniteIdentity) (m : ℕ) :
    coeff (2 * m) Ikernel = (2 * (qpoch m)⁻¹) • Cdem m := by
  induction m with
  | zero =>
      rw [mul_zero, coeff_Ikernel_zero, Cdem]
      simp only [qpoch, Finset.range_zero, Finset.prod_empty, inv_one, mul_one, mul_zero, pow_zero,
        Function.iterate_zero, id, one_smul]
      rw [show (1 : R) = mon 0 1 from rfl, smul_mon, mul_one]
  | succ m ih =>
      have h := Ikernel_coeff_rec hF (2 * m)
      rw [ih, BR_smul, smul_smul, show 2 * m + 2 = 2 * (m + 1) by ring] at h
      have hrq : rr ^ (2 * (m + 1)) = qq ^ (m + 1) := by
        rw [pow_mul, ← qq_eq_rr_sq]
      rw [hrq] at h
      have hne := one_sub_qq_pow_ne_zero (m + 1) (Nat.succ_ne_zero m)
      have h2 := congrArg (fun f => (1 - qq ^ (m + 1))⁻¹ • f) h
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
      rw [h2, Cdem_succ, smul_smul, qpoch_succ, mul_inv]
      congr 1
      ring

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.Ikernel_coeff_odd
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.Ikernel_coeff_even
end AxiomAudit
