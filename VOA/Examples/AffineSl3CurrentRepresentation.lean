/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.AffineSl3CurrentEnergy

/-!
# Actual full affine sl3 action

Finite loop sums assemble the eight proved current operators into a representation
of the full affine algebra, including its central element and degree derivation.
The polynomial energy has the opposite sign from the affine degree generator.
All current-data obligations are discharged below at every complex level; no
representation premise or noncritical-level restriction is imposed.
-/
namespace VOA.AffineSl3
open Module (End)
open VOA.AffineLie
noncomputable section
universe u
variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- Current and degree operators, together with a commuting central operator.
The current commutator contains this operator rather than an assumed scalar level. -/
structure AffineCentralCurrentData (E : Type u) [AddCommGroup E] [Module ℂ E] where
  loopMode : ℤ → Sl3 →ₗ[ℂ] End ℂ E
  degree : End ℂ E
  central : End ℂ E
  loop_comm : ∀ (x y : Sl3) (m n : ℤ),
    ⁅loopMode m x, loopMode n y⁆ = loopMode (m + n) ⁅x, y⁆ +
      if m + n = 0 then ((m : ℂ) * form x y) • central else 0
  degree_comm : ∀ (x : Sl3) (n : ℤ), ⁅degree, loopMode n x⁆ = (n : ℂ) • loopMode n x
  central_comm : ∀ (x : Sl3) (n : ℤ), ⁅central, loopMode n x⁆ = 0
  central_degree : ⁅central, degree⁆ = 0

namespace AffineCentralCurrentData
variable (D : AffineCentralCurrentData E)

/-- Finite-support extension of the loop modes. -/
noncomputable def loopAction : (ℤ →₀ Sl3) →ₗ[ℂ] End ℂ E :=
  Finsupp.lsum ℂ D.loopMode

/-- A loop supported at just one mode acts by that specified current operator.
This is the link between finite loop sums and the original mode-by-mode data. -/
@[simp] theorem loopAction_single (n : ℤ) (x : Sl3) :
    D.loopAction (Finsupp.single n x) = D.loopMode n x := by
  rw [loopAction, Finsupp.lsum_single]

/-- The degree operator differentiates any finite loop sum: each mode receives
its integer index as a coefficient. Linearity extends the individual degree relations. -/
theorem degree_comm_loopAction (g : ℤ →₀ Sl3) :
    ⁅D.degree, D.loopAction g⁆ = D.loopAction (loopDeriv g) := by
  induction g using Finsupp.induction_linear with
  | zero => rw [map_zero, lie_zero, map_zero, map_zero]
  | add g₁ g₂ h₁ h₂ => rw [map_add, lie_add, h₁, h₂, map_add, map_add]
  | single n y =>
      rw [D.loopAction_single, loopDeriv_single, D.loopAction_single, D.degree_comm]
      rw [map_smul]

/-- The bracket of two finite loop actions is the action of their loop bracket
plus the cocycle multiplied by the supplied central operator. Bilinearity reduces the proof to two individual modes. -/
theorem loopAction_comm (f g : ℤ →₀ Sl3) :
    ⁅D.loopAction f, D.loopAction g⁆
      = D.loopAction (loopBracket f g)
        + (cocycle form f g) • D.central := by
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
noncomputable abbrev affineProdEquiv (_D : AffineCentralCurrentData E) :
    ((ℤ →₀ Sl3) × ℂ × ℂ) ≃ Algebra :=
  ofProd form form_invariant

/-- The underlying linear map on the three-component affine product. -/
noncomputable def rhoLinear : Algebra →ₗ[ℂ] End ℂ E where
  toFun X :=
    D.loopAction (D.affineProdEquiv.symm X).1
      + ((D.affineProdEquiv.symm X).2.1) • D.central
      + ((D.affineProdEquiv.symm X).2.2) • D.degree
  map_add' X Y := by
    simp only [of_symm_add, Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' r X := by
    simp only [of_symm_smul, Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply,
      smul_add, smul_smul]
    module

/-- An affine element has loop, central and degree components. Its action is
the corresponding sum of the loop action, the central operator multiplied by its central coordinate,
and a scalar multiple of the degree operator. -/
theorem rhoLinear_apply (X : Algebra) :
    D.rhoLinear X =
      D.loopAction (D.affineProdEquiv.symm X).1
        + ((D.affineProdEquiv.symm X).2.1) • D.central
        + ((D.affineProdEquiv.symm X).2.2) • D.degree := rfl

/-- Operator commutators change sign when the two operators are exchanged.
This sign fixes the contribution of the degree derivation in the affine bracket. -/
theorem end_lie_swap (_D : AffineCentralCurrentData E) (A B : End ℂ E) :
    ⁅A, B⁆ = -⁅B, A⁆ :=
  (lie_skew A B).symm

/-- Centrality on each loop mode extends to arbitrary finite loop sums. -/
theorem central_comm_loopAction (g : ℤ →₀ Sl3) : ⁅D.central, D.loopAction g⁆ = 0 := by
  induction g using Finsupp.induction_linear with
  | zero => rw [map_zero, lie_zero]
  | add f g hf hg => rw [map_add, lie_add, hf, hg, add_zero]
  | single n x => rw [D.loopAction_single, D.central_comm]

/-- The same centrality in the reversed bracket order. -/
theorem loopAction_comm_central (g : ℤ →₀ Sl3) : ⁅D.loopAction g, D.central⁆ = 0 := by
  rw [D.end_lie_swap, D.central_comm_loopAction, neg_zero]

/-- The degree operator also commutes with the central action. -/
theorem degree_comm_central : ⁅D.degree, D.central⁆ = 0 := by
  rw [D.end_lie_swap, D.central_degree, neg_zero]

set_option maxHeartbeats 1000000 in
-- Expanding the product model produces a nine-term bracket.
/-- The affine representation assembled from the current data. -/
noncomputable def rho : Algebra →ₗ⁅ℂ⁆ End ℂ E :=
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
          = bracketP form (D.affineProdEquiv.symm X)
              (D.affineProdEquiv.symm Y) :=
        Equiv.symm_apply_apply _ _
      have hL : D.rhoLinear ⁅X, Y⁆
          = D.loopAction (loopBracket f g + d • loopDeriv g - d' • loopDeriv f)
            + (cocycle form f g) • D.central := by
        rw [D.rhoLinear_apply, hbr]
        simp only [bracketP, zero_smul, add_zero]
        rw [← hf, ← hd, ← hg, ← hd']
      have hR : ⁅D.rhoLinear X, D.rhoLinear Y⁆
          = ⁅D.loopAction f, D.loopAction g⁆
            + d' • ⁅D.loopAction f, D.degree⁆
            + d • ⁅D.degree, D.loopAction g⁆ := by
        rw [D.rhoLinear_apply, D.rhoLinear_apply, ← hf, ← hc, ← hd, ← hg, ← hc', ← hd']
        simp only [add_lie, lie_add, smul_lie, lie_smul, D.central_comm_loopAction, D.loopAction_comm_central, D.central_degree, D.degree_comm_central,
          lie_self, smul_zero, add_zero]
        abel
      have hDf : ⁅D.loopAction f, D.degree⁆ = -D.loopAction (loopDeriv f) := by
        rw [D.end_lie_swap, D.degree_comm_loopAction]
      rw [hL, hR, D.loopAction_comm, D.degree_comm_loopAction, hDf,
        map_sub, map_add, map_smul, map_smul]
      module }

/-- The assembled affine representation recovers exactly the supplied current
operator on each loop generator. Assembly does not change the current action. -/
@[simp] theorem rho_ofLoop (x : Sl3) (n : ℤ) :
    D.rho (ofLoop form form_invariant x n) = D.loopMode n x := by
  change D.rhoLinear _ = _
  rw [D.rhoLinear_apply]
  simp only [ofLoop, Equiv.symm_apply_apply, D.loopAction_single, zero_smul, add_zero]

/-- The distinguished central Lie algebra element acts by the supplied central operator.
It need not act by a complex scalar; it can include a square-zero tangent action. -/
@[simp] theorem rho_C :
    D.rho (AffineLie.C form form_invariant) = D.central := by
  change D.rhoLinear _ = _
  rw [D.rhoLinear_apply]
  simp only [AffineLie.C, Equiv.symm_apply_apply, map_zero, zero_add, one_smul, zero_smul,
    add_zero]

/-- The affine grading derivation acts by the supplied degree operator.
For VOA vacuum modules this derivation is minus the conformal energy L₀. -/
@[simp] theorem rho_ell0 :
    D.rho (ell0 form form_invariant) = D.degree := by
  change D.rhoLinear _ = _
  rw [D.rhoLinear_apply]
  simp only [ell0, Equiv.symm_apply_apply, map_zero, zero_add, zero_smul, one_smul]


end AffineCentralCurrentData

namespace FreeField
/-- The explicit free-field currents, with central action k and degree minus
polynomial energy, satisfy every full affine representation axiom. -/
def currentData (k : ℂ) : AffineCentralCurrentData Fock where
  loopMode := currentAction k
  degree := -energy
  central := k • 1
  loop_comm x y m n := by
    rw [currentAction_bracket]
    by_cases h : m+n=0
    · simp only [if_pos h, smul_smul]; congr 2; ring
    · simp only [if_neg h]
  degree_comm x n := by
    rw [neg_lie, energy_currentAction]
    module
  central_comm x n := scalar_comm _ _
  central_degree := scalar_comm _ _

/-- The actual affine sl3 Lie representation on the polynomial Fock space,
valid at arbitrary complex level, including the critical level. -/
def representation (k : ℂ) : Algebra →ₗ⁅ℂ⁆ End ℂ Fock := (currentData k).rho

/-- Loop elements act by exactly the eight assembled current modes. -/
@[simp] theorem representation_loop (k : ℂ) (x : Sl3) (n : ℤ) :
    representation k (ofLoop form form_invariant x n) = currentAction k n x :=
  (currentData k).rho_ofLoop x n

/-- The central generator acts by the specified scalar level. -/
@[simp] theorem representation_central (k : ℂ) :
    representation k (AffineLie.C form form_invariant) = k • 1 :=
  (currentData k).rho_C

/-- The affine degree generator is minus polynomial energy. -/
@[simp] theorem representation_degree (k : ℂ) :
    representation k (ell0 form form_invariant) = -energy :=
  (currentData k).rho_ell0

/-- Every nonnegative loop mode kills the nonzero polynomial vacuum. -/
theorem representation_vacuum (k : ℂ) (x : Sl3) (n : ℤ) (hn : 0 ≤ n) :
    representation k (ofLoop form form_invariant x n) 1 = 0 := by
  rw [representation_loop, currentAction_vacuum k x hn]

/-- The affine degree generator kills the polynomial vacuum. -/
theorem representation_degree_vacuum (k : ℂ) :
    representation k (ell0 form form_invariant) 1 = 0 := by
  rw [representation_degree, LinearMap.neg_apply, energy_vacuum, neg_zero]
end FreeField
end
end VOA.AffineSl3
