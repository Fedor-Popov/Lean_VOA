/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNMonsterActionLift
import VOA.Moonshine.MoonshineLRLiftBlock
import VOA.Moonshine.MoonshineLRLiftWBlock

/-!
# The extraspecial automorphisms of `V♮` are lifts of elements of `AutO`

For `μ` in the Leech lattice, `extraVnatAut μ : AutVnat` (LR side, `MoonshineLRLiftExtraAut`)
acts on `V_Λ⁺` by the pairing character `x_α ↦ (−1)^{⟨μ,α⟩} x_α` (oscillators fixed) and on
`T⁺` by the normalised charge operator `c_μ · e_μ`, `c_μ² = (−1)^{⟨μ,μ⟩/2} ε(μ,μ)`
(`extraPlusFormScalar`).  In the Griess dictionary `griessNat : SpaceB → V♮₂` this is rational:

  `extraVnatAut μ (griessNat (A, x, N)) = griessNat (A, ε_μ x, σ_μ Q_μ N)`

with `ε_μ x = (c ↦ (−1)^{⟨μ, α_c⟩} x_c)` (`liftBlockExtraX`), `Q_μ = qmatR ℚ 0 a δ` Axiom's signed
permutation matrix for the coordinates `(a, δ)` of `μ̄`, and `σ_μ = c_μ · Z(μ̄) ∈ {±1}`
(`Z = signRefinement`; `σ_μ² = 1` because `Z(μ̄)² = ε(μ,μ) (−1)^{pair(a,δ)}` and
`pair(a,δ) = ⟨μ,μ⟩/2 mod 2`, `pair_coordOfRed_red`).  By the rationality criterion
`isVnatLiftable_of_rational` every extraspecial automorphism is `monsterLift g` for an explicit
`g ∈ AutO`.

## Main results
* `extraSpinPhase_mul_self` (`(c_μ Z(μ̄))² = 1`), `exists_extraSign`.
* `extraPlusIsometry_spinTopState`, ⭐ `extraPlusIsometry_spinDict`, ⭐ `extraVnatAut_griessNat`.
* ⭐ `extraVnatAut_mem_range_monsterLift`, ⭐ `exists_monsterLift_eq_extraVnatAut` (with the explicit
  rational action of the lifted element on `SpaceB`).
* `extraSign`, ⭐ `extraLiftable μ : liftableSubgroup`, `monsterLift_extraLiftable`,
  ⭐ `extraLiftable_apply`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterAction

open VOA VOA.Moonshine VOA.IntegralLattice VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.SigmaTop VOA.Moonshine.ConwayNorton.M8
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open Matrix
open scoped TensorProduct

/-! ## The sign `σ_μ = c_μ Z(μ̄)` -/

/-- **`(c_μ Z(μ̄))² = 1`**: `c_μ² = (−1)^{⟨μ,μ⟩/2} ε(μ,μ)` and, from the refinement law at `p + p = 0`,
`Z(p)² ε(μ,μ) (−1)^{⟨μ,μ⟩/2} = 1` for `p = μ̄` (`pair_coordOfRed_red`). -/
theorem extraSpinPhase_mul_self (μ : leech.carrier) :
    (extraPlusFormScalar μ * signRefinement (coordOfRed (red leech μ))) *
      (extraPlusFormScalar μ * signRefinement (coordOfRed (red leech μ))) = 1 := by
  have hZ := signRefinement_add (coordOfRed (red leech μ)) (coordOfRed (red leech μ))
  have h0 : coordOfRed (red leech μ) + coordOfRed (red leech μ) = 0 := by
    rw [← two_smul (ZMod 2) (coordOfRed (red leech μ)), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hE : Extraspecial.sgn (cocycleExp (coordOfRed (red leech μ)) (coordOfRed (red leech μ)))
      = latticeCocycle leech μ μ := by
    rw [cocycleExp_coordOfRed, latticeCocycle_eq_coc]
    rfl
  have hpair : Extraspecial.sgn (pair (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2)
      = (-1 : ℂ) ^ (leech.form μ μ / 2) := by
    rw [pair_coordOfRed_red, ← Extraspecial.neg_one_zpow_eq_sgn]
  rw [h0, signRefinement_zero, signForm_apply, Extraspecial.sgn_add, hE, hpair] at hZ
  have hc := extraPlusFormScalar_sq μ
  linear_combination
    (signRefinement (coordOfRed (red leech μ)) * signRefinement (coordOfRed (red leech μ))) * hc - hZ

/-- `σ_μ = c_μ Z(μ̄)` is a rational sign. -/
theorem exists_extraSign (μ : leech.carrier) :
    ∃ σ : ℚ, (σ = 1 ∨ σ = -1) ∧
      (σ : ℂ) = extraPlusFormScalar μ * signRefinement (coordOfRed (red leech μ)) := by
  rcases mul_self_eq_one_iff.1 (extraSpinPhase_mul_self μ) with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, Rat.cast_one]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, Rat.cast_neg, Rat.cast_one]⟩

/-! ## The twisted block -/

/-- The normalised extraspecial action on a top-level twisted state `h_v(−½) ⊗ Ψ(w)`:
`w ↦ (c_μ · spinOp(μ̄)) w`. -/
theorem extraPlusIsometry_spinTopState (μ : leech.carrier) (v : Fin (rank leech) → ℂ)
    (w : SpinIdx → ℂ) :
    extraPlusIsometry μ (spinTopState v w)
      = spinTopState v ((extraPlusFormScalar μ • spinOp (coordOfRed (red leech μ))).mulVec w) := by
  rw [spinTopState_apply, spinTopState_apply, liftWExtraIsometry_hP, ← spinIso_spinOp,
    ← spinIso_smul, Matrix.smul_mulVec]
  -- the two scalar actions on `SpinRep = SpinIdx → ℂ` agree definitionally
  rfl

/-- `c_μ · spinOp(μ̄) = σ_μ Q_μ` with `Q_μ = qmatR ℚ 0 a δ` rational. -/
theorem extraScalar_smul_spinOp (μ : leech.carrier) (σ : ℚ)
    (hσ : (σ : ℂ) = extraPlusFormScalar μ * signRefinement (coordOfRed (red leech μ))) :
    extraPlusFormScalar μ • spinOp (coordOfRed (red leech μ))
      = (σ • qmatR ℚ 0 (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2).map
          (Rat.castHom ℂ) := by
  ext s t
  have hst : ((qmatR ℚ 0 (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2 s t : ℚ) : ℂ)
      = qmatR ℂ 0 (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2 s t := by
    have := congrFun (congrFun (map_qmatR (Rat.castHom ℂ) 0 (coordOfRed (red leech μ)).1
      (coordOfRed (red leech μ)).2) s) t
    simpa only [Matrix.map_apply, Rat.coe_castHom] using this
  simp only [spinOp, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Rat.coe_castHom, ← hst,
    Rat.cast_mul, hσ]
  ring

/-- ⭐ **The extraspecial action on the `W`-block is rational**:
`extraPlusIsometry μ (spinDict N) = spinDict ((σ_μ Q_μ) N)`. -/
theorem extraPlusIsometry_spinDict (μ : leech.carrier) (σ : ℚ)
    (hσ : (σ : ℂ) = extraPlusFormScalar μ * signRefinement (coordOfRed (red leech μ)))
    (N : SpaceW) :
    extraPlusIsometry μ (spinDict N)
      = spinDict ((σ • qmatR ℚ 0 (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2) * N) := by
  rw [spinDict_apply, spinDict_apply, map_smul, spinToConway_mul_left,
    ← extraScalar_smul_spinOp μ σ hσ, spinTopVec_apply, spinTopVec_apply, map_sum]
  refine congrArg (fun y : TP => spinDictScale • y) (Finset.sum_congr rfl fun i _ => ?_)
  rw [extraPlusIsometry_spinTopState]
  rfl

/-! ## The whole Griess algebra -/

/-- ⭐ **The extraspecial automorphism on the rational dictionary**:
`extraVnatAut μ (griessNat (A, x, N)) = griessNat (A, ε_μ x, σ_μ Q_μ N)`. -/
theorem extraVnatAut_griessNat (μ : leech.carrier) (σ : ℚ)
    (hσ : (σ : ℂ) = extraPlusFormScalar μ * signRefinement (coordOfRed (red leech μ)))
    (u : SpaceB) :
    extraVnatAut μ (griessNat u : Vnat)
      = griessNat (u.1, liftBlockExtraX μ u.2.1,
          (σ • qmatR ℚ 0 (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2) * u.2.2) := by
  rw [griessNat_coe, griessNat_coe, extraVnatAut_apply]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [untwistedDict_apply, untwistedDict_apply, map_add, liftBlockExtra_matDict,
      liftBlockExtra_shortDict]
  · exact extraPlusIsometry_spinDict μ σ hσ u.2.2

/-- ⭐ **Every extraspecial automorphism of `V♮` lies in the image of the Monster lift.** -/
theorem extraVnatAut_mem_range_monsterLift (μ : leech.carrier) :
    extraVnatAut μ ∈ monsterLift.range := by
  obtain ⟨σ, -, hσ⟩ := exists_extraSign μ
  exact (mem_range_monsterLift_iff _).2 fun u => ⟨_, extraVnatAut_griessNat μ σ hσ u⟩

/-- ⭐ **The extraspecial elements of `AutO` lift, explicitly**: for every `μ` there are a sign
`σ ∈ {±1}` and a liftable `g ∈ AutO` with `monsterLift g = extraVnatAut μ`, acting on `SpaceB` by
`(A, x, N) ↦ (A, ε_μ x, σ Q_μ N)`. -/
theorem exists_monsterLift_eq_extraVnatAut (μ : leech.carrier) :
    ∃ σ : ℚ, (σ = 1 ∨ σ = -1) ∧ ∃ g : liftableSubgroup, monsterLift g = extraVnatAut μ ∧
      ∀ u : SpaceB, ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u
        = (u.1, liftBlockExtraX μ u.2.1,
            (σ • qmatR ℚ 0 (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2) * u.2.2) := by
  obtain ⟨σ, hσ1, hσ⟩ := exists_extraSign μ
  obtain ⟨g, hg⟩ := isVnatLiftable_of_rational (extraVnatAut μ)
    fun u => ⟨_, extraVnatAut_griessNat μ σ hσ u⟩
  refine ⟨σ, hσ1, g, hg, fun u => griessNat_coe_injective ?_⟩
  rw [← monsterLift_apply_griessNat, hg, extraVnatAut_griessNat μ σ hσ u]

/-! ## The extraspecial elements of `AutO`, named -/

/-- The sign `σ_μ = c_μ Z(μ̄) ∈ {±1}` as a rational number. -/
noncomputable def extraSign (μ : leech.carrier) : ℚ := (exists_extraSign μ).choose

theorem extraSign_eq_one_or (μ : leech.carrier) : extraSign μ = 1 ∨ extraSign μ = -1 :=
  (exists_extraSign μ).choose_spec.1

theorem extraSign_cast (μ : leech.carrier) :
    (extraSign μ : ℂ) = extraPlusFormScalar μ * signRefinement (coordOfRed (red leech μ)) :=
  (exists_extraSign μ).choose_spec.2

/-- ⭐ **The extraspecial element of `AutO` attached to `μ`**: the unique liftable element whose lift
is `extraVnatAut μ`. -/
noncomputable def extraLiftable (μ : leech.carrier) : liftableSubgroup :=
  (MonoidHom.ofInjective monsterLift_injective).symm
    ⟨extraVnatAut μ, extraVnatAut_mem_range_monsterLift μ⟩

/-- `monsterLift (extraLiftable μ) = extraVnatAut μ`. -/
theorem monsterLift_extraLiftable (μ : leech.carrier) :
    monsterLift (extraLiftable μ) = extraVnatAut μ :=
  MonoidHom.apply_ofInjective_symm monsterLift_injective _

/-- ⭐ **The action of `extraLiftable μ` on Axiom's Griess algebra**:
`(A, x, N) ↦ (A, ε_μ x, σ_μ Q_μ N)`. -/
theorem extraLiftable_apply (μ : leech.carrier) (u : SpaceB) :
    (((extraLiftable μ : liftableSubgroup) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u
      = (u.1, liftBlockExtraX μ u.2.1,
          (extraSign μ • qmatR ℚ 0 (coordOfRed (red leech μ)).1 (coordOfRed (red leech μ)).2)
            * u.2.2) := by
  refine griessNat_coe_injective ?_
  rw [← monsterLift_apply_griessNat, monsterLift_extraLiftable,
    extraVnatAut_griessNat μ (extraSign μ) (extraSign_cast μ) u]

end VOA.Moonshine.MonsterAction
