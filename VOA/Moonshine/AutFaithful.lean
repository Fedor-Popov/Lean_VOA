/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.Generation
import VOA.Moonshine.LatticeMorphRigid
import VOA.Moonshine.FockSpanBase

/-!
# Faithfulness of `Aut V♮` on the Griess algebra — lattice ingredients
(Aut(V♮) campaign, step 3, route C of `Notes/MONSTER_AUT_PLAN.md`)

Route C proves directly that an automorphism of `V♮` fixing `V♮₂` pointwise is the identity,
without a generation theorem.  It scales each `x_β = e^β + e^{-β}` (`frameX0P β`) by a
scalar `c_β`, and this file supplies the lattice identity that propagates the scalars along
minimal vectors.

## Main results
* ⭐ `frameX0P_smul_frameX0P_of_neg` — the **leading product**: for `⟨α,γ⟩ < 0`,
  `x_α₍₋⟨α,γ⟩₋₁₎ x_γ = ε(α,γ) · x_{α+γ}` in `V_Λ⁺`.  There is no Fock dressing: the
  charge-`α−γ` terms vanish because their Schur index `2⟨α,γ⟩` is negative (`plusProj_smul`
  at Fock weight `0`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.AutMonster

open VOA VOA.Moonshine LatGen IntegralLattice HeisenbergN

/-- ⭐ **The leading product of two lattice vectors in `V_Λ⁺`.**  For `⟨α,γ⟩ < 0`,
`x_α₍₋⟨α,γ⟩₋₁₎ x_γ = ε(α,γ) · x_{α+γ}`. -/
theorem frameX0P_smul_frameX0P_of_neg (α γ : leech.carrier) (h : leech.form α γ < 0) :
    leechVOAPlus.smul (frameX0P α) (-(leech.form α γ) - 1) (frameX0P γ)
      = latticeCocycle leech α γ • frameX0P (α + γ) := by
  have hq : vacuumN (rank leech) ∈ HeisenbergN.gradingWN (rank leech) 0 :=
    FockSpan.one_mem_gradingWN
  have hstep := plusProj_smul α γ hq (n := -(leech.form α γ) - 1) (by push_cast; omega)
  have hlead : leechVOA.smul (latChargeGen leech α) (-(leech.form α γ) - 1)
      (latStateGen leech (vacuumN (rank leech)) γ)
        = latticeCocycle leech α γ • latChargeGen leech (α + γ) :=
    smul_latChargeGen leech leech_even leech_posDef α γ
  rw [hlead, map_smul, plusProj_latChargeGen] at hstep
  change _ = leechVOAPlus.smul (frameX0P α) _ (plusProj (latChargeGen leech γ)) at hstep
  rw [plusProj_latChargeGen, PreVertexAlgebra.smul_smul_right] at hstep
  have h2 : (2 : ℂ) • ((1 / 2 : ℂ) • leechVOAPlus.smul (frameX0P α) (-(leech.form α γ) - 1)
      (frameX0P γ)) = (2 : ℂ) • (latticeCocycle leech α γ • (1 / 2 : ℂ) • frameX0P (α + γ)) :=
    congrArg _ hstep.symm
  rw [smul_smul, smul_comm (latticeCocycle leech α γ), smul_smul] at h2
  norm_num at h2
  exact h2

end VOA.Moonshine.AutMonster
