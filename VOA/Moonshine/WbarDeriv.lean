/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.WbarDef
import VOA.Core.InvariantFormFHL2

/-!
# `W̄`: the `L₋₁`-derivative property  (Moonshine step M8c, `W̄` part 3)

* `Lp1_act` — the module `L₁`-bracket `L₁(u₍ᵣ₎x) = u₍ᵣ₎L₁x + (2p−r−2)u₍ᵣ₊₁₎x + (L₁u)₍ᵣ₎x`
  for `u ∈ 𝒱_p` (from the module Jacobi identity with `ω`).
* `Lp1_Lm1` — `[L₁, L₋₁] = 2L₀` on `M`; `Lp1_pow_Lm1` — the `sl₂` relation
  `L₁ʲ⁺¹L₋₁ x = L₋₁L₁ʲ⁺¹x + (j+1)(2w−j)L₁ʲx` on `M_w`.
* `Wdag_Lm1` — `W†(L₋₁t)₍ₙ₎ = −n·W†(t)₍ₙ₋₁₎` (no form needed).
* `WbarMode_Lm1` / `Wbar_deriv` — `W̄(L₋₁t, z) = ∂_z W̄(t, z)`.  Only `hO : WeightOrth N BM`
  is used (the identity holds already at the level of the defining functionals).

## Status
All declarations proved; no `sorry`/axioms.  Unconditional (only the displayed hypotheses).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SkewAdjoint

open Module (End Dual)
open VertexOperatorAlgebra SkewIntertwiner InvForm
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The `L₁`-bracket on a module -/

theorem cbz_two (i : ℤ) :
    cbz 2 i = if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 1 else 0 := by
  by_cases hneg : i < 0
  · rw [cbz_apply_neg 2 hneg, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [cbz_apply_nonneg 2 (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k := ⟨i.toNat, by omega⟩
  rw [Int.toNat_natCast]
  rcases k with _ | _ | _ | k
  · simp
  · simp [gBinom]
  · simp [gBinom, Finset.prod_range_succ]; norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), gBinom]
    rw [Finset.prod_eq_zero (i := 2) (by simp) (by push_cast; ring), zero_div]

/-- **The module `L₁`-bracket** for `u ∈ 𝒱_p`:
`L₁(u₍ᵣ₎x) = u₍ᵣ₎(L₁x) + (2p−r−2)·u₍ᵣ₊₁₎x + (L₁u)₍ᵣ₎x`. -/
theorem Lp1_act (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p) (r : ℤ) (x : M) :
    Lp1 N (N.act u r x) = N.act u r (Lp1 N x) + ((2 * p - r - 2 : ℤ) : ℂ) • N.act u (r + 1) x
      + N.act (W.L 1 u) r x := by
  have hj := N.jacobi W.conformalVector u x 0 2 r
  have hl : (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (mode (N.YM W.conformalVector) (0 + 2 - i) (mode (N.YM u) (r + i) x)
          - negOnePow 0 • mode (N.YM u) (0 + r - i) (mode (N.YM W.conformalVector) (2 + i) x)))
      = Lp1 N (N.act u r x) - N.act u r (Lp1 N x) := by
    rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp [negOnePow, Lp1]
  have hr : (∑ᶠ i : ℤ, cbz 2 i • mode (N.YM (W.smul W.conformalVector (0 + i) u)) (2 + r - i) x)
      = N.act (W.L (-1) u) (r + 2) x + (2 : ℂ) • N.act (W.L 0 u) (r + 1) x
        + N.act (W.L 1 u) r x := by
    rw [finsum_eq_sum_of_support_subset (s := {0, 1, 2})]
    · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [cbz_two]
      norm_num
      rw [smul_omega_zero]
      have e1 : W.smul W.conformalVector 1 u = W.L 0 u := by
        rw [L_def, PreVertexAlgebra.smul_def]; norm_num
      have e2 : W.smul W.conformalVector 2 u = W.L 1 u := by
        rw [L_def, PreVertexAlgebra.smul_def]; norm_num
      rw [e1, e2]
      ring_nf
      try abel
    · intro i hi
      rw [Function.mem_support] at hi
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      by_contra h
      apply hi
      rw [cbz_two, if_neg (by tauto), if_neg (by tauto), if_neg (by tauto), zero_smul]
  have hcov := act_T_covariance N.toWeakModule u (r + 2) x
  rw [show (r + 2 - 1 : ℤ) = r + 1 by ring] at hcov
  have hL0 : W.L 0 u = (p : ℂ) • u := W.L_zero_grading u hu
  rw [hl, hr, hcov, hL0, act_smul_left] at hj
  rw [sub_eq_iff_eq_add'] at hj
  rw [hj]
  push_cast
  module

/-- `[L₁, L₋₁] = 2L₀` on `M_α`: `L₁L₋₁x = L₋₁L₁x + 2α·x`. -/
theorem Lp1_Lm1 (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    Lp1 N (Lm1 N.toWeakModule x) = Lm1 N.toWeakModule (Lp1 N x) + (2 * α) • x := by
  have h := Lp1_act N W.conformal_mem 0 x
  rw [L1_conformal_zero] at h
  have h0 : N.act W.conformalVector 0 x = Lm1 N.toWeakModule x := rfl
  have h0' : N.act W.conformalVector 0 (Lp1 N x) = Lm1 N.toWeakModule (Lp1 N x) := rfl
  have h1 : N.act W.conformalVector (0 + 1) x = α • x := by
    rw [zero_add, WeakModule.act_def]; exact N.L0_weight α x hx
  rw [h0, h0', h1, WeakModule.act_def] at h
  rw [h, map_zero (N.YM), mode_zero, LinearMap.zero_apply, add_zero, smul_smul]
  norm_num

/-- The `sl₂` relation `L₁ʲ⁺¹L₋₁x = L₋₁L₁ʲ⁺¹x + (j+1)(2w−j)·L₁ʲx` on `M_w`. -/
theorem Lp1_pow_Lm1 (N : OrdVModule W M) {w : ℂ} {x : M} (hx : x ∈ N.weight w) (j : ℕ) :
    (Lp1 N ^ (j + 1)) (Lm1 N.toWeakModule x)
      = Lm1 N.toWeakModule ((Lp1 N ^ (j + 1)) x) + (((j : ℂ) + 1) * (2 * w - j)) • (Lp1 N ^ j) x := by
  induction j with
  | zero =>
    rw [zero_add, pow_one, pow_zero, Module.End.one_apply, Lp1_Lm1 N hx]; push_cast; ring_nf
  | succ j ih =>
    have hpow : ∀ (k : ℕ) (y : M), Lp1 N ((Lp1 N ^ k) y) = (Lp1 N ^ (k + 1)) y := by
      intro k y; rw [pow_succ', Module.End.mul_apply]
    rw [← hpow, ih, map_add, map_smul, Lp1_Lm1 N (Lp1_pow_mem N hx (j + 1)), hpow, hpow]
    push_cast
    module

/-! ## `W†(L₋₁t)₍ₙ₎ = −n·W†(t)₍ₙ₋₁₎` -/

theorem Wdag_Lm1_int (N : OrdVModule W M) (n : ℤ) {w : ℤ} {t : M} (ht : t ∈ N.weight (w : ℂ))
    (φ : 𝒱) : Wdag N n (Lm1 N.toWeakModule t) φ = (-(n : ℂ)) • Wdag N (n - 1) t φ := by
  set A := N.toWeakModule
  set R' := dagBound N w with hR'
  have hvan : ∀ j : ℕ, R' ≤ j → (Lp1 N ^ j) t = 0 := fun j hj =>
    Lp1_pow_eq_zero_of_dagBound N ht hj
  have hLt : Lm1 A t ∈ N.weight (((w + 1 : ℤ)) : ℂ) := by
    have := Lm1_mem N ht; push_cast; exact this
  have hvan' : ∀ j : ℕ, R' + 1 ≤ j → (Lp1 N ^ j) (Lm1 A t) = 0 := by
    intro j hj
    refine Lp1_pow_eq_zero N hLt ?_
    simp only [hR', dagBound] at hj; omega
  rw [Wdag_int_eq_sum N n hLt (R' + 1) hvan', Wdag_int_eq_sum N (n - 1) ht (R' + 1)
    (fun j hj => hvan j (by omega))]
  set X : ℕ → M := fun j => wMode A ((Lp1 N ^ j) t) (2 * w - n - 1 - j) φ with hX
  have hXR : X R' = 0 := by simp only [hX]; rw [hvan R' le_rfl, wMode_zero_right]
  set a : ℕ → ℂ := fun j => (j.factorial : ℂ)⁻¹ * (-(((2 * w - n - j : ℤ)) : ℂ)) with ha
  set c : ℕ → ℂ := fun j => (j.factorial : ℂ)⁻¹ * (((2 * w - j : ℤ)) : ℂ) with hc
  set f : ℕ → M := fun j => ((j.factorial : ℂ)⁻¹) •
      wMode A ((Lp1 N ^ j) (Lm1 A t)) (2 * (w + 1) - n - 2 - j) φ with hf
  have hf0 : f 0 = a 0 • X 0 := by
    simp only [hf, ha, hX, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
      inv_one, one_smul, one_mul, CharP.cast_eq_zero, sub_zero]
    rw [show (2 * (w + 1) - n - 2 : ℤ) = 2 * w - n by ring, wMode_Lm1,
      show (2 * w - n - 1 : ℤ) = 2 * w - n - 1 by ring]
  have hfs : ∀ j : ℕ, f (j + 1) = a (j + 1) • X (j + 1) + c j • X j := by
    intro j
    simp only [hf, ha, hc, hX]
    rw [Lp1_pow_Lm1 N ht j, wMode_add_right, wMode_smul_right, wMode_Lm1]
    rw [show (2 * (w + 1) - n - 2 - ((j + 1 : ℕ) : ℤ) - 1) = 2 * w - n - 1 - ((j + 1 : ℕ) : ℤ) by
          push_cast; ring,
        show (2 * (w + 1) - n - 2 - ((j + 1 : ℕ) : ℤ)) = 2 * w - n - 1 - (j : ℤ) by push_cast; ring]
    rw [smul_add, smul_smul, smul_smul, Nat.factorial_succ]
    have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hjf : ((j.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    congr 2 <;> (push_cast; field_simp; try ring)
  have hL : ∑ j ∈ Finset.range (R' + 1), f j
      = ∑ j ∈ Finset.range (R' + 1), (a j + c j) • X j := by
    rw [Finset.sum_range_succ', hf0]
    simp_rw [hfs]
    rw [Finset.sum_add_distrib, add_assoc, add_comm (∑ j ∈ Finset.range R', c j • X j), ← add_assoc,
      ← Finset.sum_range_succ' (fun j => a j • X j)]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun j => c j • X j), hXR, smul_zero, add_zero]
  have hR : ∑ j ∈ Finset.range (R' + 1), ((j.factorial : ℂ)⁻¹) •
        wMode A ((Lp1 N ^ j) t) (2 * w - (n - 1) - 2 - j) φ
      = ∑ j ∈ Finset.range (R' + 1), ((j.factorial : ℂ)⁻¹) • X j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hX]; rw [show 2 * w - (n - 1) - 2 - (j : ℤ) = 2 * w - n - 1 - j by ring]
  change (-1 : ℂ) ^ (w + 1) • ∑ j ∈ Finset.range (R' + 1), f j = _
  rw [hL, hR, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ha, hc, smul_smul]
  congr 1
  push_cast; ring

/-- `W†(L₋₁t)₍ₙ₎ = −n·W†(t)₍ₙ₋₁₎` for every `t`. -/
theorem Wdag_Lm1 (N : OrdVModule W M) (n : ℤ) (t : M) :
    Wdag N n (Lm1 N.toWeakModule t) = (-(n : ℂ)) • Wdag N (n - 1) t := by
  have ht : t ∈ ⨆ α, N.weight α := by rw [N.isInternal.submodule_iSup_eq_top]; trivial
  induction ht using Submodule.iSup_induction' with
  | mem α t ht =>
    refine LinearMap.ext fun φ => ?_
    by_cases hα : ∃ w : ℤ, (w : ℂ) = α
    · obtain ⟨w, rfl⟩ := hα
      rw [LinearMap.smul_apply, Wdag_Lm1_int N n ht φ]
    · rw [Wdag_nonint N (n - 1) ht (fun w hw => hα ⟨w, hw⟩),
        Wdag_nonint N n (Lm1_mem N ht) (fun w hw => hα ⟨w - 1, by push_cast; rw [hw]; ring⟩)]
      simp
  | zero => simp
  | add t t' _ _ h1 h2 => rw [map_add, map_add, map_add, h1, h2, smul_add]

variable (BV : LinearMap.BilinForm ℂ 𝒱) (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M)
  (hO : WeightOrth N BM)

/-- **`W̄(L₋₁t)₍ₙ₎ = −n·W̄(t)₍ₙ₋₁₎`** (no hypothesis on `BV`). -/
theorem WbarMode_Lm1 (n : ℤ) (t : M) :
    WbarMode BV N BM hO n (Lm1 N.toWeakModule t) = (-(n : ℂ)) • WbarMode BV N BM hO (n - 1) t := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.smul_apply, WbarMode_apply, WbarMode_apply,
    ← riesz_smul BV _ (gsupp_Phi_finite N hO (n - 1) t a)]
  congr 1
  simp only [Phi, Wdag_Lm1, LinearMap.comp_smul]

/-- **`Wbar_deriv`**: `W̄(L₋₁t, z) = ∂_z W̄(t, z)`. -/
theorem Wbar_deriv (t : M) :
    Wbar BV N BM hO (Lm1 N.toWeakModule t) = deriv (Wbar BV N BM hO t) := by
  funext k
  rw [deriv_apply]
  show WbarMode BV N BM hO (-k - 1) (Lm1 N.toWeakModule t)
    = (k + 1 : ℤ) • WbarMode BV N BM hO (-(k + 1) - 1) t
  rw [WbarMode_Lm1, ← Int.cast_smul_eq_zsmul ℂ, show -k - 1 - 1 = -(k + 1) - 1 by ring]
  push_cast; ring_nf

end VOA.Moonshine.SkewAdjoint
