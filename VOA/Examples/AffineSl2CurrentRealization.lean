/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2VacuumEvaluation

/-!
# Assemble an affine sl2 representation from current modes

The inverse-DS OPE calculation naturally produces loop modes, rather than a Lie homomorphism out
of the product model of the full affine algebra.  This file supplies the formal bridge.

AffineCurrentData asks only for a linear family of loop modes, its affine commutator, an operator
representing the grading derivation, and the two vacuum-annihilation conditions.  The resulting
toVacuumCurrentRealization feeds directly into VacuumCurrentRealization.eval.
-/

namespace VOA.AffineVOA

open Module (End)
open VOA.AffineLie

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- Operator-first current data sufficient to represent the full affine algebra at level k. -/
structure AffineCurrentData (k : ℂ) (E : Type u) [AddCommGroup E] [Module ℂ E] where
  loopMode : ℤ → Sl2 →ₗ[ℂ] End ℂ E
  degree : End ℂ E
  vacuum : E
  loop_comm : ∀ (x y : Sl2) (m n : ℤ),
    ⁅loopMode m x, loopMode n y⁆
      = loopMode (m + n) ⁅x, y⁆
        + (if m + n = 0 then ((m : ℂ) * kappaForm x y) •
            (k • (1 : End ℂ E)) else 0)
  degree_comm : ∀ (x : Sl2) (n : ℤ),
    ⁅degree, loopMode n x⁆ = (n : ℂ) • loopMode n x
  pos_annihilate : ∀ (x : Sl2) (n : ℤ), 0 ≤ n → loopMode n x vacuum = 0
  degree_vacuum : degree vacuum = 0

namespace AffineCurrentData

variable {k : ℂ} (D : AffineCurrentData k E)

/-- Finite-support extension of the loop modes. -/
noncomputable def loopAction : (ℤ →₀ Sl2) →ₗ[ℂ] End ℂ E :=
  Finsupp.lsum ℂ D.loopMode

/-- A loop supported at just one mode acts by that specified current operator.
This is the link between finite loop sums and the original mode-by-mode data. -/
@[simp] theorem loopAction_single (n : ℤ) (x : Sl2) :
    D.loopAction (Finsupp.single n x) = D.loopMode n x := by
  rw [loopAction, Finsupp.lsum_single]

/-- The degree operator differentiates any finite loop sum: each mode receives
its integer index as a coefficient. Linearity extends the individual degree relations. -/
theorem degree_comm_loopAction (g : ℤ →₀ Sl2) :
    ⁅D.degree, D.loopAction g⁆ = D.loopAction (loopDeriv g) := by
  induction g using Finsupp.induction_linear with
  | zero => rw [map_zero, lie_zero, map_zero, map_zero]
  | add g₁ g₂ h₁ h₂ => rw [map_add, lie_add, h₁, h₂, map_add, map_add]
  | single n y =>
      rw [D.loopAction_single, loopDeriv_single, D.loopAction_single, D.degree_comm]
      rw [map_smul]

/-- The bracket of two finite loop actions is the action of their loop bracket
plus the central cocycle at level k. Bilinearity reduces the proof to two individual modes. -/
theorem loopAction_comm (f g : ℤ →₀ Sl2) :
    ⁅D.loopAction f, D.loopAction g⁆
      = D.loopAction (loopBracket f g)
        + (cocycle kappaForm f g) • (k • (1 : End ℂ E)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      have hsplit :
          ⁅D.loopAction (f₁ + f₂), D.loopAction g⁆
            = ⁅D.loopAction f₁, D.loopAction g⁆
              + ⁅D.loopAction f₂, D.loopAction g⁆ := by
        rw [map_add, add_lie]
      rw [hsplit, h₁, h₂]
      simp only [map_add, LinearMap.add_apply, add_smul]
      abel
  | single m x =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ h₁ h₂ =>
          have hsplit :
              ⁅D.loopAction (Finsupp.single m x), D.loopAction (g₁ + g₂)⁆
                = ⁅D.loopAction (Finsupp.single m x), D.loopAction g₁⁆
                  + ⁅D.loopAction (Finsupp.single m x), D.loopAction g₂⁆ := by
            rw [map_add, lie_add]
          rw [hsplit, h₁, h₂]
          simp only [map_add, add_smul]
          abel
      | single n y =>
          rw [D.loopAction_single, D.loopAction_single, D.loop_comm,
            loopBracket_single, D.loopAction_single, cocycle_single]
          by_cases h : m + n = 0
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, zero_smul]

/-- Product coordinates for the affine algebra. -/
noncomputable abbrev affineProdEquiv (_D : AffineCurrentData k E) :
    ((ℤ →₀ Sl2) × ℂ × ℂ) ≃ AffSl2 :=
  ofProd kappaForm kappaForm_isInvariant

/-- The underlying linear map on the three-component affine product. -/
noncomputable def rhoLinear : AffSl2 →ₗ[ℂ] End ℂ E where
  toFun X :=
    D.loopAction (D.affineProdEquiv.symm X).1
      + ((D.affineProdEquiv.symm X).2.1) • (k • (1 : End ℂ E))
      + ((D.affineProdEquiv.symm X).2.2) • D.degree
  map_add' X Y := by
    simp only [of_symm_add, Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' r X := by
    simp only [of_symm_smul, Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply,
      smul_add, smul_smul]
    module

/-- An affine element has loop, central and degree components. Its action is
the corresponding sum of the loop action, a scalar multiple of k times the identity,
and a scalar multiple of the degree operator. -/
theorem rhoLinear_apply (X : AffSl2) :
    D.rhoLinear X =
      D.loopAction (D.affineProdEquiv.symm X).1
        + ((D.affineProdEquiv.symm X).2.1) • (k • (1 : End ℂ E))
        + ((D.affineProdEquiv.symm X).2.2) • D.degree := rfl

/-- Operator commutators change sign when the two operators are exchanged.
This sign fixes the contribution of the degree derivation in the affine bracket. -/
theorem end_lie_swap (_D : AffineCurrentData k E) (A B : End ℂ E) :
    ⁅A, B⁆ = -⁅B, A⁆ :=
  (lie_skew A B).symm

/-- The identity operator commutes with every operator, so its Lie bracket
with any current or degree action vanishes. -/
@[simp] theorem end_one_lie (_D : AffineCurrentData k E) (A : End ℂ E) :
    ⁅(1 : End ℂ E), A⁆ = 0 := by
  rw [Ring.lie_def, one_mul, mul_one, sub_self]

/-- The commutator also vanishes when the identity occurs in the second slot.
This is the reversed version of the centrality calculation. -/
@[simp] theorem end_lie_one (_D : AffineCurrentData k E) (A : End ℂ E) :
    ⁅A, (1 : End ℂ E)⁆ = 0 := by
  rw [_D.end_lie_swap, _D.end_one_lie, neg_zero]

/-- Every scalar multiple of the level operator k times the identity is central.
Thus central coordinates contribute no extra commutators in the assembled action. -/
theorem lie_levelScalar_left (_D : AffineCurrentData k E) (c : ℂ) (A : End ℂ E) :
    ⁅c • (k • (1 : End ℂ E)), A⁆ = 0 := by
  rw [smul_smul, smul_lie, _D.end_one_lie, smul_zero]

/-- Central level scalars commute with arbitrary operators in the second slot
as well; skew symmetry reduces this to the first-slot calculation. -/
theorem lie_levelScalar_right (_D : AffineCurrentData k E) (c : ℂ) (A : End ℂ E) :
    ⁅A, c • (k • (1 : End ℂ E))⁆ = 0 := by
  rw [_D.end_lie_swap, _D.lie_levelScalar_left, neg_zero]

set_option maxHeartbeats 1000000 in
-- Expanding the product model produces a nine-term bracket.
/-- The affine representation assembled from the current data. -/
noncomputable def rho : AffSl2 →ₗ⁅ℂ⁆ End ℂ E :=
  { D.rhoLinear with
    map_lie' := by
      intro X Y
      change D.rhoLinear ⁅X, Y⁆ = ⁅D.rhoLinear X, D.rhoLinear Y⁆
      set f := (D.affineProdEquiv.symm X).1 with hf
      set c := (D.affineProdEquiv.symm X).2.1 with hc
      set d := (D.affineProdEquiv.symm X).2.2 with hd
      set g := (D.affineProdEquiv.symm Y).1 with hg
      set c' := (D.affineProdEquiv.symm Y).2.1 with hc'
      set d' := (D.affineProdEquiv.symm Y).2.2 with hd'
      have hbr : D.affineProdEquiv.symm ⁅X, Y⁆
          = bracketP kappaForm (D.affineProdEquiv.symm X)
              (D.affineProdEquiv.symm Y) :=
        Equiv.symm_apply_apply _ _
      have hL : D.rhoLinear ⁅X, Y⁆
          = D.loopAction (loopBracket f g + d • loopDeriv g - d' • loopDeriv f)
            + (cocycle kappaForm f g) • (k • (1 : End ℂ E)) := by
        rw [D.rhoLinear_apply, hbr]
        simp only [bracketP, zero_smul, add_zero]
        rw [← hf, ← hd, ← hg, ← hd']
      have hR : ⁅D.rhoLinear X, D.rhoLinear Y⁆
          = ⁅D.loopAction f, D.loopAction g⁆
            + d' • ⁅D.loopAction f, D.degree⁆
            + d • ⁅D.degree, D.loopAction g⁆ := by
        rw [D.rhoLinear_apply, D.rhoLinear_apply, ← hf, ← hc, ← hd, ← hg, ← hc', ← hd']
        simp only [add_lie, lie_add, smul_lie, lie_smul, D.end_one_lie, D.end_lie_one,
          lie_self, smul_zero, add_zero]
        abel
      have hDf : ⁅D.loopAction f, D.degree⁆ = -D.loopAction (loopDeriv f) := by
        rw [D.end_lie_swap, D.degree_comm_loopAction]
      rw [hL, hR, D.loopAction_comm, D.degree_comm_loopAction, hDf,
        map_sub, map_add, map_smul, map_smul]
      module }

/-- The assembled affine representation recovers exactly the supplied current
operator on each loop generator. Assembly does not change the current action. -/
@[simp] theorem rho_ofLoop (x : Sl2) (n : ℤ) :
    D.rho (ofLoop kappaForm kappaForm_isInvariant x n) = D.loopMode n x := by
  change D.rhoLinear _ = _
  rw [D.rhoLinear_apply]
  simp only [ofLoop, Equiv.symm_apply_apply, D.loopAction_single, zero_smul, add_zero]

/-- The distinguished central Lie algebra element acts by k times the identity.
This verifies the level of the assembled representation. -/
@[simp] theorem rho_C :
    D.rho (AffineLie.C kappaForm kappaForm_isInvariant) = k • (1 : End ℂ E) := by
  change D.rhoLinear _ = _
  rw [D.rhoLinear_apply]
  simp only [AffineLie.C, Equiv.symm_apply_apply, map_zero, zero_add, one_smul, zero_smul,
    add_zero]

/-- The affine grading derivation acts by the supplied degree operator.
For VOA vacuum modules this derivation is minus the conformal energy L₀. -/
@[simp] theorem rho_ell0 :
    D.rho (ell0 kappaForm kappaForm_isInvariant) = D.degree := by
  change D.rhoLinear _ = _
  rw [D.rhoLinear_apply]
  simp only [ell0, Equiv.symm_apply_apply, map_zero, zero_add, zero_smul, one_smul]

/-- Package current data for universal affine vacuum evaluation. -/
noncomputable def toVacuumCurrentRealization : VacuumCurrentRealization k E where
  rho := D.rho
  vacuum := D.vacuum
  acts_central := D.rho_C
  pos_annihilate x n hn := by
    rw [D.rho_ofLoop]
    exact D.pos_annihilate x n hn
  ell0_annihilate := by
    rw [D.rho_ell0]
    exact D.degree_vacuum

/-- Packaging the representation with its vacuum preserves the current action.
Universal vacuum evaluation can therefore intertwine the original current operators. -/
@[simp] theorem toVacuumCurrentRealization_current (x : Sl2) (n : ℤ) :
    D.toVacuumCurrentRealization.rho
        (ofLoop kappaForm kappaForm_isInvariant x n) = D.loopMode n x :=
  D.rho_ofLoop x n

end AffineCurrentData

end

end VOA.AffineVOA
