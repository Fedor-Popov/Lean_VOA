/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FiniteCheckSteps2

/-!
# The D₄ finite identity (F)/(P)

**Theorem** (`d4FiniteIdentity`, paper d4 eq. (deligne:d4-polynomial-certificate)): in
`ℤ[q^±, s^±, x^±, z₁^±, …, z₄^±]`, with `F = π_{s_θ} Q`,

  `(1 - x²) t q F = (1 - x²)(1 - t)(1 - qt) D₊(x) D₊(x⁻¹)`
  `    - (1 - qt)[P(x) D₊(x⁻¹) - x² P(x⁻¹) D₊(x)]`,

and (`d4Q_spec`) `(1 - q⁻¹ z₁ z₂) Q = P₀ - q⁻² z₁² z₂² P_θ`.  Definitions in `D4FiniteData`.

**Proof.**  `Q` and `π_{s_θ}` are transported to the smaller `(q, u, t, z)` world (`psi_d4QU`,
`psi_piSThetaU`).  There the nine Demazure steps are computed on verified term lists and checked
step by step by `decide +kernel`; each intermediate list is a literal checkpoint
(`d4L0`, …, `d4L9`), produced at elaboration time by `d4_precompute%` and then *re-verified by the
kernel*.  The checkpoint
mechanism keeps each kernel evaluation small (one Demazure step).  Finally the transferred result is
multiplied out in the `(q, s, x, z)` world and compared with the right side, again by
`decide +kernel`.
No `native_decide`, no `ofReduceBool`: `d4_precompute%` only *proposes* the literal.
-/

namespace VOA.DeligneAudit.D4Finite

open Gen

set_option maxRecDepth 100000

/-! ## The final comparison (in the `(q, s, x, z)` world) -/

noncomputable def d4FT : TList := d4_precomputeT% psiL (stepsU 9)

theorem d4FT_eq : psiL d4L9 = d4FT := by
  decide +kernel

theorem d4LHSc_eq : mulP (mulP (linP [0, 0, 2]) (monoP [1, 2] 1)) d4FT = d4RHSc := by
  decide +kernel

/-- **The D₄ finite identity (P)**: `(1 - x²) t q F = (1 - x²)(1 - t)(1 - qt) D₊ D₋ -
(1 - qt)[P(x) D₋ - x² P(x⁻¹) D₊]`, with `F = π_{s_θ} Q`. -/
theorem d4FiniteIdentity : d4LHS = d4RHS := by
  have h := eval_d4LHSc d4L9 evalU_d4L9
  rw [d4LHSc, d4FT_eq, d4LHSc_eq, eval_d4RHSc] at h
  exact h.symm

/-! ## `Q` is the exact quotient -/

/-- The two-weight core: `(1 - q⁻¹z₁z₂)(1 - qt) L = f(z₁) f(z₂) - q⁻² z₁² z₂² f(q/z₁) f(q/z₂)`. -/
theorem d4Core_c : mulU (mulU (subP oneU (monoU [-1, 1, 1] [] 1)) (subP oneU (monoU [1] [0, 1] 1)))
      d4LUc =
    subP (mulU (fUc [0, 1, 0, 0, 0]) (fUc [0, 0, 1, 0, 0]))
      (mulU (monoU [-2, 2, 2] [] 1) (mulU (fUc [1, -1, 0, 0, 0]) (fUc [1, 0, -1, 0, 0]))) := by
  decide +kernel

theorem d4Core : (1 - moU [-1, 1, 1] []) * (1 - moU [1] [0, 1]) * d4LU =
    fU [0, 1, 0, 0, 0] * fU [0, 0, 1, 0, 0] -
      moU [-2, 2, 2] [] * (fU [1, -1, 0, 0, 0] * fU [1, 0, -1, 0, 0]) := by
  have h := congrArg evalU d4Core_c
  simp only [evalU_mulU, evalU_subP, evalU_oneU, moU_eq, evalU_d4LUc, evalU_fUc] at h
  exact h

theorem wtsQZ_eq : wtsQZ = [[0, 1, 0, 0, 0], [0, -1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, -1, 0, 0],
    [0, 0, 0, 1, 0], [0, 0, 0, -1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, -1]] := by decide

theorem wtsThetaQZ_eq : wtsThetaQZ = [[0, -1, 0, 0, 0], [1, -1, 0, 0, 0], [0, 0, -1, 0, 0],
    [1, 0, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, -1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, -1]] := by
  decide

theorem wtsQQZ_eq' : wtsQQZ = [[0, -1, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, 1, 0],
    [0, 0, 0, -1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, -1]] := by decide

theorem d4QU_spec : (1 - moU [-1, 1, 1] []) * d4QU = d4P0U - moU [-2, 2, 2] [] * d4PthetaU := by
  rw [d4QU, d4P0U, d4PthetaU, wtsQZ_eq, wtsThetaQZ_eq, wtsQQZ_eq']
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  linear_combination (fU [0, -1, 0, 0, 0] * fU [0, 0, -1, 0, 0] * fU [0, 0, 0, 1, 0] *
    fU [0, 0, 0, -1, 0] * fU [0, 0, 0, 0, 1] * fU [0, 0, 0, 0, -1]) * d4Core

/-- **`Q` is the exact quotient** `(P₀ - q⁻² z₁² z₂² P_θ)/(1 - q⁻¹ z₁ z₂)`. -/
theorem d4Q_spec : (1 - mo [-1, 0, 0, 1, 1]) * d4Q = d4P0 - mo [-2, 0, 0, 2, 2] * d4Ptheta := by
  have h := congrArg psi d4QU_spec
  rw [map_mul, map_sub, map_sub, map_mul, map_one, psi_moU, psi_moU, psi_d4QU, psi_d4P0U,
    psi_d4PthetaU] at h
  simp only [List.getD_nil, pow_zero, mul_one] at h
  rw [show mo (embL [-1, 1, 1]) = mo [-1, 0, 0, 1, 1] from
      mo_congr (by funext i; fin_cases i <;> rfl),
    show mo (embL [-2, 2, 2]) = mo [-2, 0, 0, 2, 2] from
      mo_congr (by funext i; fin_cases i <;> rfl)] at h
  exact h

end VOA.DeligneAudit.D4Finite

section AxiomAudit
#print axioms VOA.DeligneAudit.D4Finite.d4FiniteIdentity
#print axioms VOA.DeligneAudit.D4Finite.d4Q_spec
end AxiomAudit
