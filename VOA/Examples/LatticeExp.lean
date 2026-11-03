/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergNFock
import VOA.Foundations.FormalSeries

/-!
# The lattice vertex-operator OPE core `E⁻`/`E⁺` for `𝒱(A₁)`  (Gannon §5.2.2; FLM Ch. 8)

The genuine half-current exponential vertex operators of the `A₁` lattice VOA, and the
**operator contraction** that drives the lattice OPE.  This is the novel algebraic core of the
lattice construction (the boson-dressed all-states `Y`, the full OPE, locality, and the
`VertexOperatorAlgebra` instance are assembled on top of it).

## Normalisation (no `√2`)

We realise the `A₁` boson on the **`k = 2`** rank-1 Heisenberg Fock space `FockN 1`, so the
canonical commutator is `[αₘ, αₙ] = 2 m δ_{m+n,0} = ⟨α,α⟩ m δ_{m+n,0}` — the lattice norm
`⟨α,α⟩ = 2` enters as the level `k = 2`, with **no `√2`**.  (The placeholder fields in
`Examples.LatticeA1` use `k = 1`, the wrong normalisation; this file supersedes them with the
genuine `k = 2` operators.)

## What this file proves (all `sorry`-free, axiom-clean)

* `cSchur N` — the **creation Schur polynomials**, `cSchur 0 = 1`,
  `(N+1)·cSchur(N+1) = ∑_{m<N+1} X_{(m,0)}·cSchur(N-m)` (the Newton recursion); the creation
  half `E⁻(α,z) = exp(∑_{n≥1} α₋ₙ/n zⁿ)` is **multiplication by `cSchur N`** at `zⁿ` (the
  creation modes `α₋ₙ` are `X`-multiplications).  `cSchur_recursion_sum` packages the recursion.
* `EminusOp N` (= `E⁻` coefficient) and `aExp N` (= `E⁺(α,z) = exp(-∑ αₙ/n z^{-n})` coefficient,
  built by the annihilation Newton recursion), with their **vacuum actions**
  (`EminusOp_vacuum`, `aExp_vacuum`).
* `pderiv_cSchur` — **the lynchpin**: `∂_{X_{(i,0)}}(cSchur N) = (i+1)⁻¹·cSchur(N-(i+1))`
  (when `i+1 ≤ N`, else `0`).  The whole lattice OPE reduces to this one polynomial identity,
  proved by the Newton-recursion telescoping.
* `alpha_comp_EminusOp` — **the operator contraction** `[αₘ, E⁻_N] = 2·E⁻_{N-m}` (for
  `1 ≤ m ≤ N`; the bracket vanishes for `m > N`).  Since `αₘ = 2m·∂_{(m-1,0)}` is a derivation,
  this is the operator form of `pderiv_cSchur` — the bridge from the polynomial identity to the
  field-level OPE `E⁺(α,z₁)E⁻(α,z₂) = (z₁-z₂)^{⟨α,α⟩}·:…:`.

## Remaining construction (built on this core; the lattice VOA instance)

The field OPE (iterating `alpha_comp_EminusOp` over the `aExp` recursion), the boson current with
its zero mode on `ℂ{L}`, the boson-dressed `Y` on the free basis `FockN 1 ⊗ ℂ{ℤ}`, locality via
`negPowJump`/`local_iff_deltaSum`, and the `VertexOperatorAlgebra (LatModule)` instance with
VA1–VA5 + VOA1–VOA4 — assembled on the lemmas of this file (the genuine OPE core is done).

## References
* Gannon §5.2.2; FLM Ch. 8 (the vertex operator `Y(eᵅ,z)`); Kac §5.4–5.5.
-/

namespace VOA
namespace LatExp

open scoped BigOperators
open Module (End)
open HeisenbergN (FockN oscN vacuumN)
open MvPolynomial

/-- The `k = 2` rank-1 boson Fock space. -/
noncomputable abbrev B : Type := FockN 1

/-- The creation variable `α₋ₘ ↔ X_{(m,0)}` (the `m`-th creation mode is multiplication by the
`m`-th polynomial variable). -/
noncomputable def cVar (i : ℕ) : B := MvPolynomial.X (i, (0 : Fin 1))

/-- The **creation Schur polynomials** `p_N`: `p_0 = 1`,
`(N+1)·p_{N+1} = ∑_{m=0}^{N} X_{(m,0)}·p_{N-m}` (the Newton recursion for
`exp(∑_{n≥1} α₋ₙ/n zⁿ)`). -/
noncomputable def cSchur : ℕ → B
  | 0 => 1
  | (N+1) => ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1), cVar m * cSchur (N - m)

theorem cSchur_zero : cSchur 0 = 1 := by simp only [cSchur]

theorem cSchur_succ (N : ℕ) :
    cSchur (N+1) = ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1), cVar m * cSchur (N - m) := by
  simp only [cSchur]

theorem cSchur_one : cSchur 1 = cVar 0 := by
  rw [cSchur_succ]; simp [cSchur_zero]

/-- The genuine boson modes on the `k = 2` rank-1 boson: `αₘ = oscN 1 2 0 m`.  Creation (`m<0`)
is `X`-multiplication; annihilation (`m>0`) is `2m·∂`; `[αₘ,αₙ] = 2m δ_{m+n,0}`. -/
noncomputable def α (m : ℤ) : End ℂ B := oscN 1 2 0 m

theorem α_vacuum_nonneg {m : ℤ} (hm : 0 ≤ m) : α m (vacuumN 1) = 0 :=
  HeisenbergN.oscN_vacuum 1 2 0 m hm

/-- `E⁻` creation half: multiplication by `cSchur N` (the `zⁿ` coefficient of `E⁻(α,z)`). -/
noncomputable def EminusOp (N : ℕ) : End ℂ B := LinearMap.mulLeft ℂ (cSchur N)

theorem EminusOp_vacuum (N : ℕ) : EminusOp N (vacuumN 1) = cSchur N := by
  rw [EminusOp, LinearMap.mulLeft_apply, vacuumN, mul_one]

/-- `E⁺` annihilation half via the Newton recursion `N·E⁺_{-N} = ∑_{m=1}^N (-αₘ) E⁺_{-(N-m)}`. -/
noncomputable def aExp : ℕ → End ℂ B
  | 0 => LinearMap.id
  | (N+1) => ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1), (-(α (m+1 : ℤ))).comp (aExp (N - m))

theorem aExp_zero : aExp 0 = LinearMap.id := by simp only [aExp]

theorem aExp_succ (N : ℕ) :
    aExp (N+1) = ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1),
      (-(α (m+1 : ℤ))).comp (aExp (N - m)) := by simp only [aExp]

/-- `E⁺` fixes the vacuum: `E⁺_0 |0⟩ = |0⟩`, `E⁺_{-N} |0⟩ = 0` for `N ≥ 1`. -/
theorem aExp_vacuum (N : ℕ) :
    aExp N (vacuumN 1) = if N = 0 then vacuumN 1 else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [aExp_zero]
    | (M+1) =>
      rw [aExp_succ, LinearMap.smul_apply, LinearMap.sum_apply]
      have : ∀ m ∈ Finset.range (M+1),
          ((-(α (m+1 : ℤ))).comp (aExp (M - m))) (vacuumN 1) = 0 := by
        intro m hm
        rw [LinearMap.comp_apply, ih (M - m) (by simp at hm; omega)]
        split_ifs with h
        · rw [LinearMap.neg_apply, α_vacuum_nonneg (by positivity), neg_zero]
        · rw [map_zero]
      rw [Finset.sum_eq_zero this, smul_zero]; simp

/-- The Newton recursion in summed form: `∑_{m<d} X_{(m,0)}·cSchur((d-1)-m) = d·cSchur d`. -/
theorem cSchur_recursion_sum (d : ℕ) :
    (∑ m ∈ Finset.range d, cVar m * cSchur ((d-1) - m)) = (d : ℂ) • cSchur d := by
  match d with
  | 0 => simp
  | (D+1) =>
    rw [cSchur_succ]
    simp only [Nat.add_sub_cancel]
    rw [smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (Nat.cast_add_one_ne_zero D), one_smul]

/-- **The lynchpin contraction identity**: `∂_{X_{(i,0)}}(cSchur N) = (i+1)⁻¹·cSchur(N-(i+1))`
when `i+1 ≤ N`, else `0`. The Newton-recursion derivative telescopes exactly — the whole lattice
OPE reduces to this one identity. -/
theorem pderiv_cSchur (i N : ℕ) :
    (pderiv ((i, (0:Fin 1)))) (cSchur N)
      = if i + 1 ≤ N then ((i+1 : ℂ))⁻¹ • cSchur (N - (i+1)) else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [cSchur_zero]
    | (M+1) =>
      rw [cSchur_succ, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, map_sum]
      have hterm : ∀ m ∈ Finset.range (M+1),
          (pderiv ((i, (0:Fin 1)))) (cVar m * cSchur (M - m))
            = (if m = i then cSchur (M - m) else 0)
              + cVar m * (if i + 1 ≤ M - m then ((i+1:ℂ))⁻¹ • cSchur ((M-m) - (i+1)) else 0) := by
        intro m hm
        rw [pderiv_mul, ih (M - m) (by simp at hm; omega)]
        congr 1
        · rw [cVar, pderiv_X]
          by_cases h : m = i
          · subst h; simp
          · rw [Pi.single_apply, if_neg (by simp [Prod.ext_iff, h]), if_neg h, zero_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hS1 : (∑ m ∈ Finset.range (M+1), if m = i then cSchur (M - m) else 0)
          = if i ≤ M then cSchur (M - i) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range (M+1)) i (fun m => cSchur (M - m))]
        simp only [Finset.mem_range]
        by_cases h : i ≤ M
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      by_cases hiM : i ≤ M
      · have hS2 : (∑ m ∈ Finset.range (M+1),
              cVar m * (if i+1 ≤ M-m then ((i+1:ℂ))⁻¹ • cSchur ((M-m)-(i+1)) else 0))
            = ((i+1:ℂ))⁻¹ • (((M - i : ℕ) : ℂ) • cSchur (M - i)) := by
          have hpt : ∀ m ∈ Finset.range (M+1),
              cVar m * (if i+1 ≤ M-m then ((i+1:ℂ))⁻¹ • cSchur ((M-m)-(i+1)) else 0)
                = ((i+1:ℂ))⁻¹ • (if i+1 ≤ M-m then cVar m * cSchur ((M-i-1)-m) else 0) := by
            intro m hm
            by_cases h : i+1 ≤ M-m
            · rw [if_pos h, if_pos h, mul_smul_comm]
              congr 3; omega
            · rw [if_neg h, if_neg h, mul_zero, smul_zero]
          rw [Finset.sum_congr rfl hpt, ← Finset.smul_sum]
          congr 1
          have hstep1 : (∑ m ∈ Finset.range (M+1),
                if i+1 ≤ M-m then cVar m * cSchur ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then cVar m * cSchur ((M-i-1)-m) else 0 := by
            refine (Finset.sum_subset
              (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
            intro m _ hm'
            simp only [Finset.mem_range, not_lt] at hm'
            rw [if_neg (by omega)]
          have hstep2 : (∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then cVar m * cSchur ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i), cVar m * cSchur ((M-i-1) - m) := by
            apply Finset.sum_congr rfl
            intro m hm; simp only [Finset.mem_range] at hm; rw [if_pos (by omega)]
          rw [hstep1, hstep2, cSchur_recursion_sum (M - i)]
        rw [hS1, hS2, if_pos hiM, if_pos (show i+1 ≤ M+1 by omega),
          show M + 1 - (i+1) = M - i from by omega, ← MvPolynomial.smul_eq_C_mul]
        have key : cSchur (M-i) + ((i+1:ℂ))⁻¹ • (((M - i : ℕ) : ℂ) • cSchur (M - i))
            = (1 + ((i+1:ℂ))⁻¹ * ((M - i : ℕ):ℂ)) • cSchur (M - i) := by
          rw [add_smul, one_smul, smul_smul]
        rw [key, smul_smul]
        congr 1
        rw [Nat.cast_sub hiM]
        field_simp
        ring
      · rw [hS1, if_neg hiM]
        have hS2z : (∑ m ∈ Finset.range (M+1),
              cVar m * (if i+1 ≤ M-m then ((i+1:ℂ))⁻¹ • cSchur ((M-m)-(i+1)) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), mul_zero]
        rw [hS2z, add_zero, mul_zero, if_neg (by omega)]

/-- **The operator contraction** `[αₘ, E⁻_N] = 2·E⁻_{N-m}` (for `1 ≤ m ≤ N`, else the bracket
term vanishes): the annihilation mode `αₘ = 2m·∂_{(m-1,0)}` (a derivation) contracts the creation
exponential, dropping its level by `m` with the structure constant `⟨α,α⟩ = 2`.  This is the
operator form of `pderiv_cSchur`, the heart of the lattice OPE. -/
theorem alpha_comp_EminusOp (m N : ℕ) (hm : 1 ≤ m) :
    (α (m : ℤ)).comp (EminusOp N)
      = (EminusOp N).comp (α (m : ℤ))
        + (if m ≤ N then (2 : ℂ) • EminusOp (N - m) else 0) := by
  refine LinearMap.ext fun q => ?_
  have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hidx : ((m : ℤ) - 1).toNat = m - 1 := by omega
  have hcast : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
    rw [Nat.cast_sub hm]; push_cast; ring
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hm
  simp only [LinearMap.comp_apply, LinearMap.add_apply, α, EminusOp,
    LinearMap.mulLeft_apply]
  rw [HeisenbergN.oscN_apply_pos 1 2 0 hmpos, HeisenbergN.oscN_apply_pos 1 2 0 hmpos, hidx,
    pderiv_mul, pderiv_cSchur (m - 1) N, hcast]
  by_cases h : m ≤ N
  · rw [if_pos (by omega), if_pos h, LinearMap.smul_apply]
    simp only [LinearMap.mulLeft_apply,
      show N - (m - 1 + 1) = N - m from by omega, Int.cast_natCast,
      smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    rw [show (m:ℂ) * (2 * (m:ℂ)⁻¹) = 2 from by field_simp]
    abel
  · rw [if_neg (by omega), if_neg h, LinearMap.zero_apply, add_zero]
    simp only [zero_mul, zero_add, Int.cast_natCast, mul_smul_comm]

end LatExp
end VOA
