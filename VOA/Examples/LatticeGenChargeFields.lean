/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenCharge
import VOA.Examples.HeisenbergNVertex

/-!
# The charge-`α` creation half-current `E⁻(α)` of the general lattice VOA  (FLM Ch. 8)

Lifting the A₁ charge-`c` Schur machinery (`LatExp.cSchurC`/`pderiv_cSchurC`/`alpha_comp_EminusOpC`)
to a **lattice-vector charge** `α ∈ L`, over `FockN (rank L)`.  The single A₁ creation variable
`cVar m = X_{(m,0)}` is replaced by the **charge-weighted variable**

  `vVar α m := ∑ₐ (orthCoordα ₐ : ℂ) · X_{(m,a)}`

(the charge is baked into the coefficients, one per direction).  The creation half is then
`E⁻(α,z) = exp(∑_{n≥1} α(-n)/n zⁿ) = mult by ∑_N vSchur α N · zᴺ` with the Newton recursion driven by
`vVar`.  The two payoffs:

* `pderiv_vSchur` — the lynchpin `∂_{X_{(i,b)}}(vSchur α N) = (orthCoordα b)·(i+1)⁻¹·vSchur α (N-(i+1))`
  (engine-verified; the charge coordinate `orthCoordα b` threads through the Newton telescoping);
* `chargeOsc_comp_EminusVec` — the operator contraction
  `[β(m), E⁻(α)_N] = ⟨α,β⟩ · E⁻(α)_{N-m}` (`1 ≤ m ≤ N`), whose structure constant `⟨α,β⟩` is
  exactly `orthCoord_inner` (the frame identity `∑ b orthCoordα b · orthCoordβ b = ⟨α,β⟩`).  This
  is the vector-charge generalization of A₁'s `[αₘ, E⁻(cα)_N] = 2c·E⁻(cα)_{N-m}`.

## References
* FLM Ch. 8; Gannon §5.2.2; Kac §5.4–5.5.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open VOA VOA.IntegralLattice HeisenbergN
open Module (End)
open MvPolynomial

variable (L : IntegralLattice)

/-! ## The charge-weighted creation variable and the vector Schur polynomials -/

/-- The charge coordinate `(orthCoordα b : ℂ)` in the ambient direction `b`. -/
noncomputable def chargeCoord (α : L.carrier) (b : Fin (rank L)) : ℂ :=
  (orthCoord L α (rankEquiv L b) : ℂ)

/-- The metric identity in `chargeCoord` form: `∑ b chargeCoord α b · chargeCoord β b = ⟨α,β⟩`. -/
theorem sum_chargeCoord (hPos : L.PosDef) (α β : L.carrier) :
    ∑ b, chargeCoord L α b * chargeCoord L β b = ((L.form α β : ℤ) : ℂ) :=
  sum_orthCoord_rankEquiv L hPos α β

/-- The **charge-weighted creation variable** `vVar α m = ∑ₐ (orthCoordα ₐ)·X_{(m,a)}` (generalizes
the A₁ `cVar m = X_{(m,0)}`; the lattice charge lives in the per-direction coefficients). -/
noncomputable def vVar (α : L.carrier) (m : ℕ) : HeisenbergN.FockN (rank L) :=
  ∑ a : Fin (rank L), chargeCoord L α a • (MvPolynomial.X ((m, a)) : HeisenbergN.FockN (rank L))

/-- The **vector-charge creation Schur polynomials** `vSchur α N`: `vSchur α 0 = 1`,
`(N+1)·vSchur α (N+1) = ∑_{m=0}^{N} vVar α m · vSchur α (N-m)` (the Newton recursion for
`exp(∑_{n≥1} α(-n)/n zⁿ)`, driven by the charge-weighted variable). -/
noncomputable def vSchur (α : L.carrier) : ℕ → HeisenbergN.FockN (rank L)
  | 0 => 1
  | (N+1) => ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1), vVar L α m * vSchur α (N - m)

theorem vSchur_zero (α : L.carrier) : vSchur L α 0 = 1 := by simp only [vSchur]

theorem vSchur_succ (α : L.carrier) (N : ℕ) :
    vSchur L α (N+1)
      = ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1), vVar L α m * vSchur L α (N - m) := by
  simp only [vSchur]

/-- The Newton recursion in summed form: `∑_{m<d} vVar α m · vSchur α ((d-1)-m) = d·vSchur α d`. -/
theorem vSchur_recursion_sum (α : L.carrier) (d : ℕ) :
    (∑ m ∈ Finset.range d, vVar L α m * vSchur L α ((d-1) - m)) = (d : ℂ) • vSchur L α d := by
  match d with
  | 0 => simp [vSchur_zero]
  | (D+1) =>
    rw [vSchur_succ]
    simp only [Nat.add_sub_cancel]
    rw [smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (Nat.cast_add_one_ne_zero D), one_smul]

/-- `∂_{X_{(i,b)}}(vVar α m) = if m = i then (orthCoordα b) else 0` — the derivative of the
charge-weighted variable pulls out the charge coordinate of direction `b`. -/
theorem pderiv_vVar (α : L.carrier) (i : ℕ) (b : Fin (rank L)) (m : ℕ) :
    (pderiv ((i, b))) (vVar L α m)
      = if m = i then MvPolynomial.C (chargeCoord L α b) else 0 := by
  rw [vVar, map_sum, Finset.sum_eq_single b]
  · rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X, Pi.single_apply]
    by_cases h : m = i
    · subst h; rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg (show ((m, b) : ℕ × Fin (rank L)) ≠ (i, b) from
        fun hc => h (congrArg Prod.fst hc)), mul_zero, if_neg h]
  · intro a _ ha
    rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X, Pi.single_apply,
      if_neg (show ((m, a) : ℕ × Fin (rank L)) ≠ (i, b) from
        fun hc => ha (congrArg Prod.snd hc)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- **The vector-charge lynchpin** (engine-verified): `∂_{X_{(i,b)}}(vSchur α N) = (orthCoordα b)·
(i+1)⁻¹·vSchur α (N-(i+1))` when `i+1 ≤ N`, else `0`.  The charge coordinate `orthCoordα b` of the
`b`-direction threads linearly through the Newton telescoping (generalizes `pderiv_cSchur`). -/
theorem pderiv_vSchur (α : L.carrier) (i : ℕ) (b : Fin (rank L)) (N : ℕ) :
    (pderiv ((i, b))) (vSchur L α N)
      = if i + 1 ≤ N then chargeCoord L α b • (((i+1 : ℂ))⁻¹ • vSchur L α (N - (i+1))) else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [vSchur_zero]
    | (M+1) =>
      rw [vSchur_succ, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, map_sum]
      have hterm : ∀ m ∈ Finset.range (M+1),
          (pderiv ((i, b))) (vVar L α m * vSchur L α (M - m))
            = (if m = i then MvPolynomial.C (chargeCoord L α b) * vSchur L α (M - m) else 0)
              + vVar L α m * (if i + 1 ≤ M - m then
                  chargeCoord L α b • (((i+1:ℂ))⁻¹ • vSchur L α ((M-m) - (i+1))) else 0) := by
        intro m hm
        rw [pderiv_mul, ih (M - m) (by simp at hm; omega), pderiv_vVar]
        congr 1
        by_cases h : m = i
        · subst h; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg h, if_neg h, zero_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hS1 : (∑ m ∈ Finset.range (M+1),
              if m = i then MvPolynomial.C (chargeCoord L α b) * vSchur L α (M - m) else 0)
          = if i ≤ M then MvPolynomial.C (chargeCoord L α b) * vSchur L α (M - i) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range (M+1)) i
          (fun m => MvPolynomial.C (chargeCoord L α b) * vSchur L α (M - m))]
        simp only [Finset.mem_range]
        by_cases h : i ≤ M
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      by_cases hiM : i ≤ M
      · have hS2 : (∑ m ∈ Finset.range (M+1),
              vVar L α m * (if i+1 ≤ M-m then
                chargeCoord L α b • (((i+1:ℂ))⁻¹ • vSchur L α ((M-m)-(i+1))) else 0))
            = chargeCoord L α b • (((i+1:ℂ))⁻¹ • (((M - i : ℕ) : ℂ) • vSchur L α (M - i))) := by
          have hpt : ∀ m ∈ Finset.range (M+1),
              vVar L α m * (if i+1 ≤ M-m then
                  chargeCoord L α b • (((i+1:ℂ))⁻¹ • vSchur L α ((M-m)-(i+1))) else 0)
                = chargeCoord L α b • (((i+1:ℂ))⁻¹ •
                    (if i+1 ≤ M-m then vVar L α m * vSchur L α ((M-i-1)-m) else 0)) := by
            intro m hm
            by_cases h : i+1 ≤ M-m
            · rw [if_pos h, if_pos h, mul_smul_comm, mul_smul_comm]
              congr 4; omega
            · rw [if_neg h, if_neg h, mul_zero, smul_zero, smul_zero]
          rw [Finset.sum_congr rfl hpt, ← Finset.smul_sum, ← Finset.smul_sum]
          have hstep1 : (∑ m ∈ Finset.range (M+1),
                if i+1 ≤ M-m then vVar L α m * vSchur L α ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then vVar L α m * vSchur L α ((M-i-1)-m) else 0 := by
            refine (Finset.sum_subset
              (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
            intro m _ hm'
            simp only [Finset.mem_range, not_lt] at hm'
            rw [if_neg (by omega)]
          have hstep2 : (∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then vVar L α m * vSchur L α ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i), vVar L α m * vSchur L α ((M-i-1) - m) := by
            apply Finset.sum_congr rfl
            intro m hm; simp only [Finset.mem_range] at hm; rw [if_pos (by omega)]
          rw [hstep1, hstep2, vSchur_recursion_sum L α (M - i)]
        rw [hS1, hS2, if_pos hiM, if_pos (show i+1 ≤ M+1 by omega),
          show M + 1 - (i+1) = M - i from by omega,
          ← MvPolynomial.smul_eq_C_mul (vSchur L α (M - i)) (chargeCoord L α b),
          ← MvPolynomial.smul_eq_C_mul _ (((M : ℂ) + 1)⁻¹)]
        simp only [smul_smul]
        rw [← add_smul, smul_smul]
        congr 1
        rw [Nat.cast_sub hiM]
        have hM1 : (M : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero M
        have hi1 : (i : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero i
        field_simp
        ring
      · rw [hS1, if_neg hiM]
        have hS2z : (∑ m ∈ Finset.range (M+1),
              vVar L α m * (if i+1 ≤ M-m then
                chargeCoord L α b • (((i+1:ℂ))⁻¹ • vSchur L α ((M-m)-(i+1))) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), mul_zero]
        rw [hS2z, add_zero, mul_zero, if_neg (show ¬ i + 1 ≤ M + 1 by omega)]

/-! ## The creation half-current `E⁻(α)` -/

/-- `E⁻(α)` creation half: multiplication by `vSchur α N` (the `zᴺ` coefficient of `E⁻(α,z)`). -/
noncomputable def EminusVec (α : L.carrier) (N : ℕ) : End ℂ (HeisenbergN.FockN (rank L)) :=
  LinearMap.mulLeft ℂ (vSchur L α N)

theorem EminusVec_vacuum (α : L.carrier) (N : ℕ) :
    EminusVec L α N (HeisenbergN.vacuumN (rank L)) = vSchur L α N := by
  rw [EminusVec, LinearMap.mulLeft_apply, HeisenbergN.vacuumN, mul_one]

/-! ## The per-direction operator contraction -/

/-- **Per-direction contraction** `[aᵇₘ, E⁻(α)_N] = (orthCoordα b)·E⁻(α)_{N-m}` (`1 ≤ m ≤ N`): the
unit annihilation mode `aᵇₘ = m·∂_{(m-1,b)}` contracts the creation exponential, dropping its level
by `m` with the per-direction structure constant `orthCoordα b` (the operator form of
`pderiv_vSchur`).  Generalizes A₁'s `alpha_comp_EminusOp` (there the constant is `⟨α,α⟩ = 2`). -/
theorem oscN_comp_EminusVec (α : L.carrier) (b : Fin (rank L)) (m N : ℕ) (hm : 1 ≤ m) :
    (HeisenbergN.oscN (rank L) 1 b (m : ℤ)).comp (EminusVec L α N)
      = (EminusVec L α N).comp (HeisenbergN.oscN (rank L) 1 b (m : ℤ))
        + (if m ≤ N then chargeCoord L α b • EminusVec L α (N - m) else 0) := by
  refine LinearMap.ext fun q => ?_
  have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hidx : ((m : ℤ) - 1).toNat = m - 1 := by omega
  have hcast : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by rw [Nat.cast_sub hm]; push_cast; ring
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hm
  simp only [LinearMap.comp_apply, LinearMap.add_apply, EminusVec, LinearMap.mulLeft_apply]
  rw [HeisenbergN.oscN_apply_pos (rank L) 1 b hmpos, HeisenbergN.oscN_apply_pos (rank L) 1 b hmpos,
    hidx, one_smul, one_smul, pderiv_mul, pderiv_vSchur L α (m - 1) b N, hcast]
  by_cases h : m ≤ N
  · rw [if_pos (by omega), if_pos h, LinearMap.smul_apply]
    simp only [LinearMap.mulLeft_apply, show N - (m - 1 + 1) = N - m from by omega,
      Int.cast_natCast, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    rw [show (m : ℂ) * (chargeCoord L α b * (m : ℂ)⁻¹) = chargeCoord L α b from by field_simp]
    abel
  · rw [if_neg (by omega), if_neg h, LinearMap.zero_apply, add_zero]
    simp only [zero_mul, zero_add, Int.cast_natCast, mul_smul_comm]

/-! ## The charge-`α` operator contraction (the vector-charge lynchpin) -/

/-- **The charge-`α` operator contraction** `[β(m), E⁻(α)_N] = ⟨α,β⟩·E⁻(α)_{N-m}` (`1 ≤ m ≤ N`,
else the bracket vanishes): summing the per-direction contractions weighted by `orthCoordβ` turns
the per-direction constants `orthCoordα b` into `∑ b orthCoordα b · orthCoordβ b = ⟨α,β⟩`
(`orthCoord_inner`).  This is the vector-charge generalization of A₁'s `[αₘ, E⁻(cα)_N] = 2c·…`; the
lattice pairing `⟨α,β⟩` is the OPE contraction exponent that drives the charge-field locality. -/
theorem chargeOsc_comp_EminusVec (hPos : L.PosDef) (α β : L.carrier) (m N : ℕ) (hm : 1 ≤ m) :
    (chargeOsc L β (m : ℤ)).comp (EminusVec L α N)
      = (EminusVec L α N).comp (chargeOsc L β (m : ℤ))
        + (if m ≤ N then ((L.form α β : ℤ) : ℂ) • EminusVec L α (N - m) else 0) := by
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, chargeOsc, Finset.sum_mul]
  have hb : ∀ b : Fin (rank L),
      ((orthCoord L β (rankEquiv L b) : ℂ) • HeisenbergN.oscN (rank L) 1 b (m : ℤ))
          * EminusVec L α N
        = (orthCoord L β (rankEquiv L b) : ℂ) •
            (EminusVec L α N * HeisenbergN.oscN (rank L) 1 b (m : ℤ))
          + (orthCoord L β (rankEquiv L b) : ℂ) •
            (if m ≤ N then chargeCoord L α b • EminusVec L α (N - m) else 0) := by
    intro b
    rw [smul_mul_assoc, Module.End.mul_eq_comp, oscN_comp_EminusVec L α b m N hm,
      ← Module.End.mul_eq_comp, smul_add]
  rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => (mul_smul_comm _ _ _).symm)
  · by_cases h : m ≤ N
    · simp only [if_pos h, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      rw [← sum_chargeCoord L hPos α β]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    · simp only [if_neg h, smul_zero, Finset.sum_const_zero]

/-! ## Grading of the charge oscillators and `E⁺(α)` -/

/-- The charge annihilation mode `α(n)` lowers the boson weight by exactly `n`: if `p ∈ gradingZN d`
then `chargeOsc α n p ∈ gradingZN (d - n)` (each direction's `oscN` does, by `oscN_mem_gradingZN`).
Generalizes A₁'s `alpha_mem_gradingZN`. -/
theorem chargeOsc_mem_gradingZN (α : L.carrier) (n : ℤ) {d : ℤ}
    {p : HeisenbergN.FockN (rank L)} (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    chargeOsc L α n p ∈ HeisenbergN.gradingZN (rank L) (d - n) := by
  rw [chargeOsc, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ (fun b _ => ?_)
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have h := HeisenbergN.oscN_mem_gradingZN (rank L) 1 b n hp
    rwa [Int.toNat_of_nonneg hd] at h
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, map_zero]
    exact HeisenbergN.zero_mem_gradingZN (rank L) _

/-! ## The annihilation half-current `E⁺(α)` -/

/-- `E⁺(α)` annihilation half via the Newton recursion
`(N+1)·E⁺(α)_{-(N+1)} = ∑_{m} (-β(m+1)) E⁺(α)_{-(N-m)}` (for `E⁺(α,z) = exp(-∑_{n≥1} α(n)/n z^{-n})`),
driven by the charge annihilation modes `α(m+1) = chargeOsc α (m+1)`.  Generalizes A₁'s `aExpC`. -/
noncomputable def aExpVec (α : L.carrier) : ℕ → End ℂ (HeisenbergN.FockN (rank L))
  | 0 => LinearMap.id
  | (N+1) => ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1),
      (-(chargeOsc L α (m+1 : ℤ))).comp (aExpVec α (N - m))

theorem aExpVec_zero (α : L.carrier) : aExpVec L α 0 = LinearMap.id := by simp only [aExpVec]

theorem aExpVec_succ (α : L.carrier) (N : ℕ) :
    aExpVec L α (N+1) = ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1),
      (-(chargeOsc L α (m+1 : ℤ))).comp (aExpVec L α (N - m)) := by simp only [aExpVec]

/-- `E⁺(α)` fixes the vacuum: `E⁺(α)_0 |0⟩ = |0⟩`, `E⁺(α)_{-N} |0⟩ = 0` for `N ≥ 1` (the annihilation
modes `α(m+1)` kill the vacuum, `chargeOsc_vacuum`). -/
theorem aExpVec_vacuum (α : L.carrier) (N : ℕ) :
    aExpVec L α N (HeisenbergN.vacuumN (rank L))
      = if N = 0 then HeisenbergN.vacuumN (rank L) else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [aExpVec_zero]
    | (M+1) =>
      rw [aExpVec_succ, LinearMap.smul_apply, LinearMap.sum_apply]
      have hz : ∀ m ∈ Finset.range (M+1),
          ((-(chargeOsc L α (m+1 : ℤ))).comp (aExpVec L α (M - m)))
            (HeisenbergN.vacuumN (rank L)) = 0 := by
        intro m hm
        rw [LinearMap.comp_apply, ih (M - m) (by simp at hm; omega)]
        split_ifs with h
        · rw [LinearMap.neg_apply, chargeOsc_vacuum L α (m+1 : ℤ) (by positivity), neg_zero]
        · rw [map_zero]
      rw [Finset.sum_eq_zero hz, smul_zero]; simp

/-- `E⁺(α)_{-N} = aExpVec α N` lowers the boson weight by exactly `N` (generalizes
`aExpC_mem_gradingZN`). -/
theorem aExpVec_mem_gradingZN (α : L.carrier) (N : ℕ) {w : ℕ}
    {p : HeisenbergN.FockN (rank L)} (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    aExpVec L α N p ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpVec_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
           exact HeisenbergN.mem_gradingZN_of_gradingWN hp
    | (M+1) =>
      rw [aExpVec_succ, LinearMap.smul_apply, LinearMap.sum_apply]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
      simp only [Finset.mem_range] at hm
      rw [LinearMap.comp_apply, LinearMap.neg_apply]
      refine Submodule.neg_mem _ ?_
      have hrec : aExpVec L α (M - m) p
          ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) - (M - m : ℕ)) := ih (M - m) (by omega)
      have h := chargeOsc_mem_gradingZN L α ((m : ℤ) + 1) hrec
      have hgoal : (w : ℤ) - (M - m : ℕ) - ((m : ℤ) + 1) = (w : ℤ) - ((M + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : m ≤ M)]; push_cast; ring
      rwa [hgoal] at h

end VOA.LatGen
