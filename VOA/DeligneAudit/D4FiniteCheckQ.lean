/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FiniteData

/-!
# D₄ finite identity, kernel checkpoints I: the product `Q` (in the `(q, u, t, z)` world)

Each checkpoint `d4A1, …, d4A6, d4B, d4L0` is a literal term list proposed at elaboration time by
`d4_precompute%` (a metaprogram evaluating a closed term) and then *re-verified by the kernel*
(`decide +kernel`) as the result of one small multiplication.  No `native_decide`; each kernel
check takes a few seconds.
-/

namespace VOA.DeligneAudit.D4Finite

open Gen

open Lean Elab Term Meta in
/-- Evaluate a closed `UList` term at elaboration time and insert the value as a literal.  The
literal is untrusted: every use below is checked by the kernel. -/
elab "d4_precompute% " t:term : term => do
  let ty := Lean.mkConst ``VOA.DeligneAudit.D4Finite.UList
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr VOA.DeligneAudit.D4Finite.UList ty e
  return toExpr v

open Lean Elab Term Meta in
/-- As `d4_precompute%`, for `(q, s, x, z)` term lists. -/
elab "d4_precomputeT% " t:term : term => do
  let ty := Lean.mkConst ``VOA.DeligneAudit.D4Finite.TList
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr VOA.DeligneAudit.D4Finite.TList ty e
  return toExpr v

set_option maxRecDepth 100000

/-! ## Checkpoints for `Q` (in the `(q, u, t, z)` world) -/

/-- Partial products of the six `f`-factors of `Q`. -/
def prodQQc (k : ℕ) : UList := prodU ((wtsQQZ.take k).map fUc)

noncomputable def d4A1 : UList := d4_precompute% prodQQc 1
noncomputable def d4A2 : UList := d4_precompute% prodQQc 2
noncomputable def d4A3 : UList := d4_precompute% prodQQc 3
noncomputable def d4A4 : UList := d4_precompute% prodQQc 4
noncomputable def d4A5 : UList := d4_precompute% prodQQc 5
noncomputable def d4A6 : UList := d4_precompute% prodQQc 6
noncomputable def d4B : UList := d4_precompute% mulU (subP oneU (monoU [1] [0, 1] 1)) (prodQQc 6)

theorem d4A1_eq : mulU oneU (fUc (wtsQQZ.getD 0 [])) = d4A1 := by
  decide +kernel
theorem d4A2_eq : mulU d4A1 (fUc (wtsQQZ.getD 1 [])) = d4A2 := by
  decide +kernel
theorem d4A3_eq : mulU d4A2 (fUc (wtsQQZ.getD 2 [])) = d4A3 := by
  decide +kernel
theorem d4A4_eq : mulU d4A3 (fUc (wtsQQZ.getD 3 [])) = d4A4 := by
  decide +kernel
theorem d4A5_eq : mulU d4A4 (fUc (wtsQQZ.getD 4 [])) = d4A5 := by
  decide +kernel
theorem d4A6_eq : mulU d4A5 (fUc (wtsQQZ.getD 5 [])) = d4A6 := by
  decide +kernel
theorem d4B_eq : mulU (subP oneU (monoU [1] [0, 1] 1)) d4A6 = d4B := by
  decide +kernel

theorem wtsQQZ_eq : wtsQQZ = [wtsQQZ.getD 0 [], wtsQQZ.getD 1 [], wtsQQZ.getD 2 [],
    wtsQQZ.getD 3 [], wtsQQZ.getD 4 [], wtsQQZ.getD 5 []] := by decide

theorem evalU_d4A6 : evalU d4A6 = (wtsQQZ.map fU).prod := by
  rw [← d4A6_eq, ← d4A5_eq, ← d4A4_eq, ← d4A3_eq, ← d4A2_eq, ← d4A1_eq]
  simp only [evalU_mulU, evalU_oneU, evalU_fUc, one_mul]
  conv_rhs => rw [wtsQQZ_eq]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- The first `n` Demazure steps, as a computable function (used only to propose literals). -/
def stepsU (n : ℕ) : UList :=
  (d4Word.take n).foldl (fun acc i => demU (d4Roots.getD i []) acc) d4QUc

noncomputable def d4L0 : UList := d4_precompute% stepsU 0

theorem d4L0_eq : mulU d4B d4LUc = d4L0 := by
  decide +kernel

theorem evalU_d4L0 : evalU d4L0 = d4QU := by
  rw [← d4L0_eq, ← d4B_eq, evalU_mulU, evalU_mulU, evalU_subP, evalU_oneU, moU_eq, evalU_d4A6,
    evalU_d4LUc, d4QU]

end VOA.DeligneAudit.D4Finite
