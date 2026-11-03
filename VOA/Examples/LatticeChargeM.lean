/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeExp

/-!
# The general-charge lattice OPE core `E⁻(cα)` for `𝒱(A₁)`  (Gannon §5.2.2; FLM Ch. 8)

The charge-`c` generalization of `LatticeExp`: the creation half `E⁻(cα,z) = exp(c·∑_{n≥1} α₋ₙ/n zⁿ)`
of the vertex operator `Y(e^{cα},z)`.  Specializing `c = 1` recovers `LatExp.cSchur`/`EminusOp`;
`c = -1` gives the charge `e^{-α}` operator needed to reach the negative lattice sectors (so the
generators span all of `LatModule`).

## What this file proves (all `sorry`-free, axiom-clean, `pbw`-free)

* `cSchurC c N` — the **charge-`c` creation Schur polynomials**, `cSchurC c 0 = 1`,
  `(N+1)·cSchurC c (N+1) = c·∑_{m<N+1} X_{(m,0)}·cSchurC c (N-m)` (the `c`-scaled Newton recursion);
  `E⁻(cα,z) = exp(c·∑ α₋ₙ/n zⁿ)` is multiplication by `cSchurC c N` at `zⁿ`.
* `pderiv_cSchurC` — the **charge-`c` lynchpin**: `∂_{X_{(i,0)}}(cSchurC c N) = c·(i+1)⁻¹·cSchurC c (N-(i+1))`
  (when `i+1 ≤ N`, else `0`).  The `c` threads linearly through the Newton telescoping.
* `alpha_comp_EminusOpC` — the **charge-`c` operator contraction** `[αₘ, E⁻(cα)_N] = 2c·E⁻(cα)_{N-m}`
  (`1 ≤ m ≤ N`; the structure constant is `⟨α,cα⟩ = 2c`).  The operator form of `pderiv_cSchurC`.

## References
* Gannon §5.2.2; FLM Ch. 8 (the vertex operators `Y(e^{cα},z)`); Kac §5.4–5.5.
-/

namespace VOA
namespace LatExp

open scoped BigOperators
open Module (End)
open HeisenbergN (FockN oscN vacuumN)
open MvPolynomial

/-- The **charge-`c` creation Schur polynomials** `p_N^{(c)}`: `p_0 = 1`,
`(N+1)·p_{N+1} = c·∑_{m=0}^{N} X_{(m,0)}·p_{N-m}` (the Newton recursion for `exp(c·∑ α₋ₙ/n zⁿ)`). -/
noncomputable def cSchurC (c : ℂ) : ℕ → B
  | 0 => 1
  | (N+1) => ((N+1 : ℂ))⁻¹ • (c • ∑ m ∈ Finset.range (N+1), cVar m * cSchurC c (N - m))

theorem cSchurC_zero (c : ℂ) : cSchurC c 0 = 1 := by simp only [cSchurC]

theorem cSchurC_succ (c : ℂ) (N : ℕ) :
    cSchurC c (N+1)
      = ((N+1 : ℂ))⁻¹ • (c • ∑ m ∈ Finset.range (N+1), cVar m * cSchurC c (N - m)) := by
  simp only [cSchurC]

theorem cSchurC_one (c : ℂ) : cSchurC c 1 = c • cVar 0 := by
  rw [cSchurC_succ]; simp [cSchurC_zero]

/-- `cSchurC 1 = cSchur` (the charge-`c` core specializes to the proved charge-`+1` core). -/
theorem cSchurC_one_eq (N : ℕ) : cSchurC 1 N = cSchur N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [cSchurC_zero, cSchur_zero]
    | (M+1) =>
      rw [cSchurC_succ, cSchur_succ, one_smul]
      congr 1
      refine Finset.sum_congr rfl (fun m hm => ?_)
      simp only [Finset.mem_range] at hm
      rw [ih (M - m) (by omega)]

/-- The `c`-scaled Newton recursion in summed form: `c·∑_{m<d} X_{(m,0)}·cSchurC c ((d-1)-m) = d·cSchurC c d`. -/
theorem cSchurC_recursion_sum (c : ℂ) (d : ℕ) :
    (c • ∑ m ∈ Finset.range d, cVar m * cSchurC c ((d-1) - m)) = (d : ℂ) • cSchurC c d := by
  match d with
  | 0 => simp
  | (D+1) =>
    rw [cSchurC_succ]
    simp only [Nat.add_sub_cancel]
    rw [smul_smul, smul_smul]
    congr 1
    push_cast
    rw [mul_inv_cancel₀ (Nat.cast_add_one_ne_zero D), one_mul]

/-- **The charge-`c` lynchpin contraction identity**:
`∂_{X_{(i,0)}}(cSchurC c N) = c·(i+1)⁻¹·cSchurC c (N-(i+1))` when `i+1 ≤ N`, else `0`. -/
theorem pderiv_cSchurC (c : ℂ) (i N : ℕ) :
    (pderiv ((i, (0:Fin 1)))) (cSchurC c N)
      = if i + 1 ≤ N then c • (((i+1 : ℂ))⁻¹ • cSchurC c (N - (i+1))) else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [cSchurC_zero]
    | (M+1) =>
      rw [cSchurC_succ, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, pderiv_C_mul,
        pderiv_C_mul, map_sum]
      have hterm : ∀ m ∈ Finset.range (M+1),
          (pderiv ((i, (0:Fin 1)))) (cVar m * cSchurC c (M - m))
            = (if m = i then cSchurC c (M - m) else 0)
              + cVar m * (if i + 1 ≤ M - m then c • (((i+1:ℂ))⁻¹ • cSchurC c ((M-m) - (i+1))) else 0) := by
        intro m hm
        rw [pderiv_mul, ih (M - m) (by simp at hm; omega)]
        congr 1
        · rw [cVar, pderiv_X]
          by_cases h : m = i
          · subst h; simp
          · rw [Pi.single_apply, if_neg (by simp [Prod.ext_iff, h]), if_neg h, zero_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hS1 : (∑ m ∈ Finset.range (M+1), if m = i then cSchurC c (M - m) else 0)
          = if i ≤ M then cSchurC c (M - i) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range (M+1)) i (fun m => cSchurC c (M - m))]
        simp only [Finset.mem_range]
        by_cases h : i ≤ M
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      by_cases hiM : i ≤ M
      · have hstep1 : (∑ m ∈ Finset.range (M+1),
                if i+1 ≤ M-m then cVar m * cSchurC c ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then cVar m * cSchurC c ((M-i-1)-m) else 0 := by
          refine (Finset.sum_subset
            (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
          intro m _ hm'
          simp only [Finset.mem_range, not_lt] at hm'
          rw [if_neg (by omega)]
        have hstep2 : (∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then cVar m * cSchurC c ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i), cVar m * cSchurC c ((M-i-1) - m) := by
          apply Finset.sum_congr rfl
          intro m hm; simp only [Finset.mem_range] at hm; rw [if_pos (by omega)]
        have hS2 : (∑ m ∈ Finset.range (M+1),
              cVar m * (if i+1 ≤ M-m then c • (((i+1:ℂ))⁻¹ • cSchurC c ((M-m)-(i+1))) else 0))
            = ((i+1:ℂ))⁻¹ • (((M - i : ℕ) : ℂ) • cSchurC c (M - i)) := by
          have hpt : ∀ m ∈ Finset.range (M+1),
              cVar m * (if i+1 ≤ M-m then c • (((i+1:ℂ))⁻¹ • cSchurC c ((M-m)-(i+1))) else 0)
                = c • (((i+1:ℂ))⁻¹ • (if i+1 ≤ M-m then cVar m * cSchurC c ((M-i-1)-m) else 0)) := by
            intro m hm
            by_cases h : i+1 ≤ M-m
            · rw [if_pos h, if_pos h, mul_smul_comm, mul_smul_comm]
              congr 4; omega
            · rw [if_neg h, if_neg h, mul_zero, smul_zero, smul_zero]
          rw [Finset.sum_congr rfl hpt, ← Finset.smul_sum, ← Finset.smul_sum, hstep1, hstep2,
            smul_comm c ((i+1:ℂ)⁻¹), cSchurC_recursion_sum c (M - i)]
        rw [hS1, hS2, if_pos hiM, if_pos (show i+1 ≤ M+1 by omega),
          show M + 1 - (i+1) = M - i from by omega, ← MvPolynomial.smul_eq_C_mul,
          ← MvPolynomial.smul_eq_C_mul]
        simp only [smul_add, smul_smul]
        rw [← add_smul]
        congr 1
        rw [Nat.cast_sub hiM]
        have hM1 : (M : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero M
        have hi1 : (i : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero i
        field_simp
        ring
      · rw [hS1, if_neg hiM]
        have hS2z : (∑ m ∈ Finset.range (M+1),
              cVar m * (if i+1 ≤ M-m then c • (((i+1:ℂ))⁻¹ • cSchurC c ((M-m)-(i+1))) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), mul_zero]
        rw [hS2z, add_zero, mul_zero, mul_zero, if_neg (show ¬ i + 1 ≤ M + 1 by omega)]

/-- `E⁻(cα)` creation half: multiplication by `cSchurC c N` (the `zⁿ` coefficient of `E⁻(cα,z)`). -/
noncomputable def EminusOpC (c : ℂ) (N : ℕ) : End ℂ B := LinearMap.mulLeft ℂ (cSchurC c N)

theorem EminusOpC_vacuum (c : ℂ) (N : ℕ) : EminusOpC c N (vacuumN 1) = cSchurC c N := by
  rw [EminusOpC, LinearMap.mulLeft_apply, vacuumN, mul_one]

/-- `E⁻(1·α) = E⁻(α)` (the charge-`c` core specializes to the proved charge-`+1` core). -/
theorem EminusOpC_one_eq (N : ℕ) : EminusOpC 1 N = EminusOp N := by
  rw [EminusOpC, EminusOp, cSchurC_one_eq]

/-- **The charge-`c` operator contraction** `[αₘ, E⁻(cα)_N] = 2c·E⁻(cα)_{N-m}` (for `1 ≤ m ≤ N`,
else the bracket vanishes): the structure constant is `⟨α,cα⟩ = 2c`.  The operator form of
`pderiv_cSchurC`. -/
theorem alpha_comp_EminusOpC (c : ℂ) (m N : ℕ) (hm : 1 ≤ m) :
    (α (m : ℤ)).comp (EminusOpC c N)
      = (EminusOpC c N).comp (α (m : ℤ))
        + (if m ≤ N then (2 * c) • EminusOpC c (N - m) else 0) := by
  refine LinearMap.ext fun q => ?_
  have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hidx : ((m : ℤ) - 1).toNat = m - 1 := by omega
  have hcast : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by rw [Nat.cast_sub hm]; push_cast; ring
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hm
  simp only [LinearMap.comp_apply, LinearMap.add_apply, α, EminusOpC, LinearMap.mulLeft_apply]
  rw [HeisenbergN.oscN_apply_pos 1 2 0 hmpos, HeisenbergN.oscN_apply_pos 1 2 0 hmpos, hidx,
    pderiv_mul, pderiv_cSchurC c (m - 1) N, hcast]
  by_cases h : m ≤ N
  · rw [if_pos (by omega), if_pos h, LinearMap.smul_apply]
    simp only [LinearMap.mulLeft_apply, show N - (m - 1 + 1) = N - m from by omega, Int.cast_natCast,
      smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    rw [show (m : ℂ) * (2 * (c * (m : ℂ)⁻¹)) = 2 * c from by field_simp]
    abel
  · rw [if_neg (by omega), if_neg h, LinearMap.zero_apply, add_zero]
    simp only [zero_mul, zero_add, Int.cast_natCast, mul_smul_comm]

/-- `E⁺(cα)` annihilation half via the `c`-scaled Newton recursion
`(N+1)·E⁺(cα)_{-(N+1)} = c·∑_{m} (-α_{m+1}) E⁺(cα)_{-(N-m)}` (for `E⁺(cα,z) = exp(-c·∑ αₙ/n z^{-n})`). -/
noncomputable def aExpC (c : ℂ) : ℕ → End ℂ B
  | 0 => LinearMap.id
  | (N+1) => ((N+1 : ℂ))⁻¹ • (c • ∑ m ∈ Finset.range (N+1), (-(α (m+1 : ℤ))).comp (aExpC c (N - m)))

theorem aExpC_zero (c : ℂ) : aExpC c 0 = LinearMap.id := by simp only [aExpC]

theorem aExpC_succ (c : ℂ) (N : ℕ) :
    aExpC c (N+1) = ((N+1 : ℂ))⁻¹ • (c • ∑ m ∈ Finset.range (N+1),
      (-(α (m+1 : ℤ))).comp (aExpC c (N - m))) := by simp only [aExpC]

/-- `E⁺(1·α) = E⁺(α)` (the charge-`c` core specializes to the proved charge-`+1` core). -/
theorem aExpC_one_eq (N : ℕ) : aExpC 1 N = aExp N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpC_zero, aExp_zero]
    | (M+1) =>
      rw [aExpC_succ, aExp_succ, one_smul]
      congr 1
      refine Finset.sum_congr rfl (fun m hm => ?_)
      simp only [Finset.mem_range] at hm
      rw [ih (M - m) (by omega)]

/-- `E⁺(cα)` fixes the vacuum: `E⁺(cα)_0 |0⟩ = |0⟩`, `E⁺(cα)_{-N} |0⟩ = 0` for `N ≥ 1`. -/
theorem aExpC_vacuum (c : ℂ) (N : ℕ) :
    aExpC c N (vacuumN 1) = if N = 0 then vacuumN 1 else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [aExpC_zero]
    | (M+1) =>
      rw [aExpC_succ, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply]
      have hz : ∀ m ∈ Finset.range (M+1),
          ((-(α (m+1 : ℤ))).comp (aExpC c (M - m))) (vacuumN 1) = 0 := by
        intro m hm
        rw [LinearMap.comp_apply, ih (M - m) (by simp at hm; omega)]
        split_ifs with h
        · rw [LinearMap.neg_apply, α_vacuum_nonneg (by positivity), neg_zero]
        · rw [map_zero]
      rw [Finset.sum_eq_zero hz, smul_zero, smul_zero]; simp

end LatExp
end VOA
