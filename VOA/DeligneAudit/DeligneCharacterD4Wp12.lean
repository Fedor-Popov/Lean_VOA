/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp11
import VOA.DeligneAudit.DeligneCharacterD4MLDE
import VOA.DeligneAudit.D4FiniteStatementProof
import VOA.DeligneAudit.DeligneMLDERamanujanAdapters

/-!
# `D4SchurEqE4`: the elliptic evaluation of the D₄ Schur index (layer 12, assembly)

**`d4SchurEqE4 : D4MLDE.D4SchurEqE4`**: `½ CT_x Θ(x) M(√q, x, 1) = q^{-7/12} E₄′/(240 η¹⁰)`, coefficientwise.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- The `s^k` CT coefficients of the integral kernel. -/
def cK (k : ℕ) : P := ctP (coeff k kernelM')

theorem ev1_Ikernel (k : ℕ) : D4K.ev1 (coeff k D4K.Ikernel) = coeK (cK k) := by
  rw [D4K.Ikernel, D4K.coeff_smap, ← ιS_kernelM', coeff_map, ev1_ctTheta_ιR, cK]

theorem cK_odd (m : ℕ) : cK (2 * m + 1) = 0 := by
  apply coeK_injective
  rw [← ev1_Ikernel, D4K.Ikernel_coeff_odd D4Finite.d4FiniteIdentity_holds m, map_zero, map_zero]

theorem half_coeK_coeff (x : P) (n : ℕ) :
    ((2 : D4K.Kq)⁻¹ * coeK x).coeff (n : ℤ) = (1 / 2 : ℚ) * coeff n x := by
  rw [show (2 : D4K.Kq)⁻¹ = HahnSeries.C (1 / 2 : ℚ) by
    rw [show (2 : D4K.Kq) = HahnSeries.C (2 : ℚ) from (map_ofNat HahnSeries.C 2).symm, ← map_inv₀]; norm_num,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.ofPowerSeries_apply_coeff, smul_eq_mul]

theorem sum_range_even {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hf : ∀ m, f (2 * m + 1) = 0) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N + 1), f k = ∑ m ∈ Finset.range (N + 1), f (2 * m) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        hf N, add_zero, Finset.sum_range_succ (fun m => f (2 * m)) (N + 1),
        show 2 * N + 1 + 1 = 2 * (N + 1) by ring]

theorem d4SchurQ_eq_rhs (N : ℕ) : D4K.d4SchurQ N = (1 / 2 : ℚ) * coeff (2 * N) (rhsCT kernelM') := by
  rw [D4K.d4SchurQ, rhsCT, coeff_diagS, Finset.mul_sum]
  simp only [coeff_mk]
  rw [sum_range_even (fun k => (1 / 2 : ℚ) * coeff (2 * N - k) (ctP (coeff k kernelM')))
    (fun m => by simp only; rw [show ctP (coeff (2 * m + 1) kernelM') = cK (2 * m + 1) from rfl, cK_odd,
      map_zero, mul_zero])]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ N := by rw [Finset.mem_range] at hm; omega
  rw [ev1_Ikernel, show 2 * ((N : ℤ) - m) = ((2 * N - 2 * m : ℕ) : ℤ) by omega,
    half_coeK_coeff, cK]

/-- `η(r²)` over `ℚ`. -/
def etaP : P := infProd fun k => 1 - X ^ (2 * k + 2)

theorem pf_etaP : ProdFactors fun k => (1 : P) - X ^ (2 * k + 2) := by
  have h := prodFactors_one_add (R := ℚ) (-1) (fun k => 2 * k + 2) (fun k => by show k < 2 * k + 2; omega)
  simpa [sub_eq_add_neg] using h

theorem map_cst_etaP : PowerSeries.map cst etaP = etaR := by
  have hpf : ProdFactors fun k => (1 : PowerSeries L) - X ^ (2 * k + 2) := by
    have h := pf_sub (1 : L) (fun k => 2 * k + 2) (fun k => by show k < 2 * k + 2; omega); simpa using h
  rw [etaR]
  apply eq_infProd_of_agree hpf
  intro N
  have h := (agreeTo_infProd pf_etaP N).map (PowerSeries.map cst) (L := N + 1)
    (by rw [map_pow, PowerSeries.map_X])
  rw [etaP]
  refine h.trans (AgreeTo.of_eq ?_)
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [map_sub, map_one, map_pow, PowerSeries.map_X]

theorem lhs_kernel : etaP ^ 10 * rhsCT kernelM' = -ctx (W1 * W1) := by
  rw [← lhsCT_eq_rhsCT, lhsCT]
  have hI := integrand_sq
  have hS := Sp'_kernelM'
  have hu : IsUnit (Den ^ 8) := (isUnit_infProd _).pow 8
  have key : etaR ^ 10 * (ThX * Sp' kernelM') = -(W1 ^ 2) := by
    apply hu.mul_right_cancel
    rw [← hS] at hI
    linear_combination hI
  rw [← ctx_map_cst_mul, map_pow, map_cst_etaP, key, pow_two]
  ext n : 1
  simp only [ctx, coeff_mk, map_neg]
  rfl

/-- `∑_N (N+1) σ₃(N+1) q^N`. -/
def Qs : PowerSeries ℚ := PowerSeries.mk fun N => ((N + 1 : ℕ) : ℚ) * ∑ d ∈ (N + 1).divisors, (d : ℚ) ^ 3

theorem neg_ctx_W1_sq : -ctx (W1 * W1) = expand 2 two_ne_zero (2 * Qs) := by
  ext n : 1
  rw [map_neg, coeff_expand]
  obtain ⟨N, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [if_pos (dvd_mul_right 2 N), Nat.mul_div_cancel_left _ (by norm_num), ctx_W1_sq_even,
      show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat _ 2).symm, coeff_C_mul, Qs, coeff_mk]
    ring
  · rw [if_neg (by omega), ctx_W1_sq_odd, neg_zero]

theorem expand_euler : expand 2 two_ne_zero (euler : PowerSeries ℚ) = etaP := by
  rw [euler_eq_infProd, expand_infProd 2 two_ne_zero prodFactors_euler, etaP]
  refine infProd_congr fun k => ?_
  rw [map_sub, map_one, map_pow, expand_X, ← pow_mul]; ring_nf

theorem rhsCT_eq : rhsCT kernelM' = expand 2 two_ne_zero (2 * Qs * D4MLDE.Qinv) := by
  have h := lhs_kernel
  rw [neg_ctx_W1_sq, ← expand_euler, ← map_pow] at h
  have h1 := D4MLDE.euler_pow_mul_Qinv
  calc rhsCT kernelM' = expand 2 two_ne_zero ((euler : PowerSeries ℚ) ^ 10 * D4MLDE.Qinv) * rhsCT kernelM' := by
        rw [h1, map_one, one_mul]
    _ = expand 2 two_ne_zero D4MLDE.Qinv * (expand 2 two_ne_zero ((euler : PowerSeries ℚ) ^ 10) * rhsCT kernelM') := by
        rw [map_mul]; ring
    _ = _ := by rw [h, ← map_mul]; ring_nf

theorem d4SchurQ_eq_Qs (N : ℕ) : D4K.d4SchurQ N = coeff N (Qs * D4MLDE.Qinv) := by
  rw [d4SchurQ_eq_rhs, rhsCT_eq, coeff_expand, if_pos (dvd_mul_right 2 N), Nat.mul_div_cancel_left _ (by norm_num),
    mul_assoc, show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat _ 2).symm, coeff_C_mul]
  ring

theorem eulerOp_E4s : eulerOp D4MLDE.E4s = X * (PowerSeries.C 240 * Qs) := by
  ext n : 1
  rcases n with _ | n
  · rw [D4MLDE.coeff_eulerOp, coeff_zero_X_mul]; simp
  · rw [D4MLDE.coeff_eulerOp, coeff_succ_X_mul, coeff_C_mul, Qs, coeff_mk, D4MLDE.E4s, map_add,
      D4MLDE.coeff_ofNat_mul, D4MLDE.sigS, coeff_mk, coeff_one, if_neg (Nat.succ_ne_zero n),
      if_neg (Nat.succ_ne_zero n), sigmaK]
    push_cast; ring

theorem gser_eq : D4MLDE.gser = PowerSeries.C 240 * Qs * D4MLDE.Qinv := by
  apply X_pow_mul_cancel 1
  rw [pow_one, D4MLDE.X_mul_gser, D4MLDE.Gser, eulerOp_E4s]; ring

/-- **`D4SchurEqE4`**: the D₄ Schur index `½ CT_x Θ(x) M(√q, x, z = 1)` equals
`q^{-7/12} E₄′/(240 η¹⁰)`, coefficientwise. -/
theorem d4SchurEqE4 : D4MLDE.D4SchurEqE4 := by
  intro N
  rw [d4SchurQ_eq_Qs, D4MLDE.d4E4Target, gser_eq, mul_assoc, coeff_C_mul]
  ring

/-- **The D₄ Schur index solves the Arakawa–Kawasetsu MLDE** (`h∨ = 6`), unconditionally. -/
theorem d4SchurQ_eq_mldeCoeff_holds (N : ℕ) : D4K.d4SchurQ N = mldeCoeff 6 N :=
  D4MLDE.d4SchurQ_eq_mldeCoeff d4SchurEqE4 D4MLDE.ramanujanIdentities N

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4Wp.d4SchurQ_eq_mldeCoeff_holds
#print axioms VOA.DeligneAudit.DeligneCharacter.D4Wp.d4SchurEqE4
end AxiomAudit
