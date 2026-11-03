/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.VnatBlock
import VOA.Modules.Translation

/-!
# M8i preparation: the Virasoro algebra on any weak module

For a vertex operator algebra `W` with conformal vector `ω` and central charge `c`, and any weak
`W`-module `A`, the modes `Lᴬₙ := ω₍ₙ₊₁₎ᴬ` satisfy the Virasoro relations with the **same**
central charge `c`.  The library's `OrdVModule` does not carry this as a field; it is derived here
from the module commutator formula (`VnatBlock.act_comm`, the `ℓ = 0` slice of the module Jacobi
identity) and the explicit conformal self-products

* `ω₍₀₎ω = L₋₁ω`, `ω₍₁₎ω = 2ω`, `ω₍₂₎ω = 0`, `ω₍₃₎ω = (c/2)𝟙`, `ω₍ⱼ₎ω = 0` for `j ≥ 4`

(read off `W.virasoro` on the vacuum and the grading), together with module translation
covariance `(L₋₁a)₍ₙ₎ᴹ = −n a₍ₙ₋₁₎ᴹ` (`act_T_covariance`).

## Main results

* `omega_smul_zero`, `omega_smul_one`, `omega_smul_two`, `omega_smul_three`,
  `omega_smul_ge_four` — the conformal self-OPE of any VOA.
* `module_virasoro` — `[Lᴬₘ, Lᴬₙ] = (m−n)Lᴬₘ₊ₙ + δ_{m+n,0}(m³−m)/12 · c` on every weak module.
* `module_YM_Lm1` — `Y_M(L₋₁a, z) = ∂_z Y_M(a, z)` (the field form of `act_T_covariance`).

## Status
`sorry`-free, no axioms beyond Lean's three; general (any VOA, any weak module), unconditional.
-/

namespace VOA.Moonshine.VnatAxioms

open Module (End)
open VertexOperatorAlgebra VnatBlock

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- `ω₍₀₎ω = L₋₁ω`. -/
theorem omega_smul_zero :
    W.smul W.conformalVector 0 W.conformalVector = W.L (-1) W.conformalVector := by
  rw [L_def]; norm_num; rfl

/-- `ω₍₁₎ω = 2ω` (`L₀ω = 2ω`). -/
theorem omega_smul_one :
    W.smul W.conformalVector 1 W.conformalVector = (2 : ℂ) • W.conformalVector := by
  have h := W.L0_grading W.conformalVector W.conformal_mem
  rw [PreVertexAlgebra.smul_def, h]
  norm_num

/-- `ω₍₂₎ω = L₁ω = 0`. -/
theorem omega_smul_two : W.smul W.conformalVector 2 W.conformalVector = 0 := by
  have hbr := W.virasoro 1 (-2)
  rw [if_neg (by norm_num : ¬(1 + -2 : ℤ) = 0), add_zero, Ring.lie_def] at hbr
  have happ := DFunLike.congr_fun hbr W.vacuum
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at happ
  rw [show (1 : ℤ) + 1 = 2 by norm_num, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (1 : ℤ) + -2 + 1 = 0 by norm_num] at happ
  have h1 : mode (W.Y W.conformalVector) (-1) W.vacuum = W.conformalVector := (W.creation _).1
  have h2 : mode (W.Y W.conformalVector) 2 W.vacuum = 0 := (W.creation _).2 2 (by norm_num)
  have h0 : mode (W.Y W.conformalVector) 0 W.vacuum = 0 := (W.creation _).2 0 le_rfl
  rw [h1, h2, h0, map_zero, sub_zero, smul_zero] at happ
  rw [PreVertexAlgebra.smul_def, happ]

/-- `ω₍₃₎ω = L₂ω = (c/2)𝟙`. -/
theorem omega_smul_three :
    W.smul W.conformalVector 3 W.conformalVector = (W.centralCharge / 2) • W.vacuum := by
  have hbr := W.virasoro 2 (-2)
  rw [if_pos (by norm_num : (2 + -2 : ℤ) = 0), Ring.lie_def] at hbr
  have happ := DFunLike.congr_fun hbr W.vacuum
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply] at happ
  rw [show (2 : ℤ) + 1 = 3 by norm_num, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (2 : ℤ) + -2 + 1 = 1 by norm_num] at happ
  have h1 : mode (W.Y W.conformalVector) (-1) W.vacuum = W.conformalVector := (W.creation _).1
  have h3 : mode (W.Y W.conformalVector) 3 W.vacuum = 0 := (W.creation _).2 3 (by norm_num)
  have h0 : mode (W.Y W.conformalVector) 1 W.vacuum = 0 := (W.creation _).2 1 (by norm_num)
  rw [h1, h3, h0, map_zero, sub_zero, smul_zero, zero_add] at happ
  rw [PreVertexAlgebra.smul_def, happ]
  congr 1
  ring

/-- `ω₍ⱼ₎ω = 0` for `j ≥ 4` (it would lie in weight `3 − j < 0`). -/
theorem omega_smul_ge_four (j : ℤ) (hj : 4 ≤ j) :
    W.smul W.conformalVector j W.conformalVector = 0 := by
  have h := W.smul_mem_grading W.conformal_mem W.conformal_mem j
  rw [W.positivity _ (by omega), Submodule.mem_bot] at h
  exact h

variable {W} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- **The Virasoro relations on any weak module**, with the central charge of `W`:
`[ω₍ₘ₊₁₎ᴬ, ω₍ₙ₊₁₎ᴬ] = (m−n) ω₍ₘ₊ₙ₊₁₎ᴬ + δ_{m+n,0} (m³−m)/12 · c`. -/
theorem module_virasoro (A : WeakModule W M) (m n : ℤ) :
    ⁅mode (A.YM W.conformalVector) (m + 1), mode (A.YM W.conformalVector) (n + 1)⁆
      = ((m : ℂ) - n) • mode (A.YM W.conformalVector) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * W.centralCharge) • (1 : End ℂ M)
           else 0) := by
  refine LinearMap.ext fun x => ?_
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hc := act_comm A W.conformalVector W.conformalVector (m + 1) (n + 1) x 4
    (fun j hj => omega_smul_ge_four W j (by omega))
  simp only [WeakModule.act_def] at hc
  rw [hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  rw [omega_smul_zero, omega_smul_one, omega_smul_two, omega_smul_three]
  have hT := act_T_covariance A W.conformalVector (m + 1 + (n + 1) - 0) x
  simp only [WeakModule.act_def] at hT
  rw [hT]
  simp only [map_smul, map_zero, mode_smul, mode_zero, LinearMap.smul_apply,
    LinearMap.zero_apply, smul_zero, add_zero, A.vacuum_YM, mode_one]
  rw [show m + 1 + (n + 1) - 0 - 1 = m + n + 1 by ring,
    show m + 1 + (n + 1) - 1 = m + n + 1 by ring]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos (by omega)]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hn : (n : ℂ) = -m := by
      have : n = -m := by omega
      rw [this]; push_cast; ring
    simp only [gBinom, Finset.prod_range_succ, Finset.prod_range_zero]
    simp only [smul_smul, ← add_smul]
    rw [hn]
    congr 1 <;> congr 1 <;> simp [Nat.factorial, hn] <;> ring
  · rw [if_neg hmn, if_neg (by omega)]
    simp only [smul_zero, add_zero, LinearMap.zero_apply, LinearMap.smul_apply]
    simp only [gBinom, Finset.prod_range_succ, Finset.prod_range_zero]
    simp only [smul_smul, ← add_smul]
    congr 1
    simp [Nat.factorial]
    ring

/-- **Module translation in field form**: `Y_M(L₋₁a, z) = ∂_z Y_M(a, z)`. -/
theorem module_YM_Lm1 (A : WeakModule W M) (a : 𝒱) :
    A.YM (W.L (-1) a) = deriv (A.YM a) := by
  funext k
  refine LinearMap.ext fun x => ?_
  have h := act_T_covariance A a (-k - 1) x
  simp only [WeakModule.act_def, mode_apply] at h
  rw [show -(-k - 1) - 1 = k by ring, show -(-k - 1 - 1) - 1 = k + 1 by ring] at h
  rw [h, deriv_apply, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]
  congr 1
  push_cast; ring

end VOA.Moonshine.VnatAxioms
