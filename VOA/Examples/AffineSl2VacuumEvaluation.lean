/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2VOA

/-!
# Universal evaluation of the affine `sl2` vacuum module

This file extracts the representation-theoretic part of a free-field realization from the
Wakimoto calculation.  A `VacuumCurrentRealization k E` consists of an honest representation of
the full affine Lie algebra on `E`, a vacuum vector, level `k`, and the two vacuum-annihilation
conditions.  Its universal enveloping action then kills the defining vacuum ideal and descends to
a linear map

`WakModule k -> E`.

No vertex-algebra structure on `E` is required.  In particular this applies to an inverse-DS
free-field carrier before the ambient indefinite lattice algebra has been assembled as a
`NearVOA`.  The descended map sends the affine vacuum to the supplied vacuum and intertwines all
current modes.  Once the concrete inverse-DS currents satisfy their OPEs, they supply exactly the
affine Lie representation consumed here.
-/

namespace VOA.AffineVOA

open Module (End)
open UniversalEnvelopingAlgebra
open VOA.AffineLie

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- A cyclic level-`k` affine representation with the vacuum conditions defining `V^k(sl2)`. -/
structure VacuumCurrentRealization (k : ℂ) (E : Type u) [AddCommGroup E] [Module ℂ E] where
  /-- Representation of the full affine algebra, including the central element and `ell0`. -/
  rho : AffSl2 →ₗ⁅ℂ⁆ End ℂ E
  /-- The proposed free-field vacuum. -/
  vacuum : E
  /-- The central element acts at level `k`. -/
  acts_central : rho (AffineLie.C kappaForm kappaForm_isInvariant) =
    k • (1 : End ℂ E)
  /-- All nonnegative loop modes annihilate the vacuum. -/
  pos_annihilate : ∀ (x : Sl2) (n : ℤ), 0 ≤ n →
    rho (ofLoop kappaForm kappaForm_isInvariant x n) vacuum = 0
  /-- The grading derivation annihilates the vacuum. -/
  ell0_annihilate : rho (ell0 kappaForm kappaForm_isInvariant) vacuum = 0

namespace VacuumCurrentRealization

variable {k : ℂ} (R : VacuumCurrentRealization k E)

/-- The universal enveloping algebra of the affine `sl2` algebra. -/
noncomputable abbrev UEnvSl2 := UEnv Sl2 kappaForm kappaForm_isInvariant

/-- The associative action induced from the affine Lie representation. -/
noncomputable def envelopeAction : UEnvSl2 →ₐ[ℂ] End ℂ E :=
  UniversalEnvelopingAlgebra.lift ℂ R.rho

/-- A Lie algebra generator embedded in the universal enveloping algebra acts
by the original representation operator. This is the defining compatibility of
the enveloping-algebra extension. -/
@[simp] theorem envelopeAction_ι (X : AffSl2) :
    R.envelopeAction (UniversalEnvelopingAlgebra.ι ℂ X) = R.rho X := by
  rw [envelopeAction, UniversalEnvelopingAlgebra.lift_ι_apply]

/-- Vacuum evaluation `u |-> rho(u) vacuum` on the universal enveloping algebra. -/
noncomputable def envelopeEval : UEnvSl2 →ₗ[ℂ] E where
  toFun u := R.envelopeAction u R.vacuum
  map_add' u v := by rw [map_add, LinearMap.add_apply]
  map_smul' c u := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The identity of the enveloping algebra evaluates to the chosen vacuum: its
operator action is the identity, so it creates no descendants or corrections. -/
@[simp] theorem envelopeEval_one : R.envelopeEval 1 = R.vacuum := by
  change R.envelopeAction 1 R.vacuum = R.vacuum
  rw [map_one]
  rfl

/-- Every generator of the affine vacuum ideal has zero vacuum evaluation. -/
theorem envelopeEval_vacuumGens (u : UEnvSl2)
    (hu : u ∈ vacuumGens kappaForm kappaForm_isInvariant k) : R.envelopeEval u = 0 := by
  rcases hu with ⟨x, n, hn, rfl⟩ | rfl | rfl
  · change R.envelopeAction
      (UniversalEnvelopingAlgebra.ι ℂ (ofLoop kappaForm kappaForm_isInvariant x n))
        R.vacuum = 0
    rw [R.envelopeAction_ι]
    exact R.pos_annihilate x n hn
  · change (R.envelopeAction
      (UniversalEnvelopingAlgebra.ι ℂ (AffineLie.C kappaForm kappaForm_isInvariant) -
        algebraMap ℂ UEnvSl2 k)) R.vacuum = 0
    rw [map_sub, LinearMap.sub_apply, R.envelopeAction_ι, R.acts_central,
      AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  · change R.envelopeAction
      (UniversalEnvelopingAlgebra.ι ℂ (ell0 kappaForm kappaForm_isInvariant)) R.vacuum = 0
    rw [R.envelopeAction_ι]
    exact R.ell0_annihilate

/-- The whole left ideal defining the vacuum module has zero vacuum evaluation. -/
theorem envelopeEval_vacuumIdeal (u : UEnvSl2)
    (hu : u ∈ vacuumIdeal kappaForm kappaForm_isInvariant k) : R.envelopeEval u = 0 := by
  induction hu using Submodule.span_induction with
  | mem g hg => exact R.envelopeEval_vacuumGens g hg
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul a b _ hb =>
      rw [show (a • b : UEnvSl2) = a * b from rfl]
      change R.envelopeAction (a * b) R.vacuum = 0
      change R.envelopeAction b R.vacuum = 0 at hb
      rw [map_mul, Module.End.mul_apply, hb, map_zero]

/-- The universal free-field evaluation `V^k(sl2) -> E` supplied by a vacuum current
realization. -/
noncomputable def eval : WakModule k →ₗ[ℂ] E where
  toFun := QuotientAddGroup.lift
    (vacuumIdeal kappaForm kappaForm_isInvariant k).toAddSubgroup
    R.envelopeEval.toAddMonoidHom
    (fun u hu => R.envelopeEval_vacuumIdeal u hu)
  map_add' x y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact R.envelopeEval.map_add x y
  map_smul' c x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact R.envelopeEval.map_smul c x

/-- Evaluation of a vacuum-module quotient class is evaluation of any chosen
enveloping-algebra representative. Independence of the representative follows
from annihilation of the defining vacuum ideal. -/
@[simp] theorem eval_mk (u : UEnvSl2) :
    R.eval (Submodule.Quotient.mk u) = R.envelopeEval u := rfl

/-- The universal evaluation sends the affine vacuum to the supplied vacuum. -/
@[simp] theorem eval_vacuum :
    R.eval (vacuumVector kappaForm kappaForm_isInvariant k) = R.vacuum := by
  rw [vacuumVector, R.eval_mk, R.envelopeEval_one]

/-- Universal evaluation intertwines the whole affine Lie algebra, including
the degree derivation and central element. Multiplication in its enveloping
algebra descends through the vacuum ideal, so no extra representation input is needed. -/
theorem eval_action (X : AffSl2) (v : WakModule k) :
    R.eval (vacuumRho kappaForm kappaForm_isInvariant k X v) =
      R.rho X (R.eval v) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [vacuumRho_mk, R.eval_mk, R.eval_mk]
  change R.envelopeAction (UniversalEnvelopingAlgebra.ι ℂ X * u) R.vacuum = _
  rw [map_mul, Module.End.mul_apply, R.envelopeAction_ι]
  rfl

/-- The universal evaluation intertwines every loop action. -/
theorem eval_vacuumRho (x : Sl2) (n : ℤ) (v : WakModule k) :
    R.eval (vacuumRho kappaForm kappaForm_isInvariant k
      (ofLoop kappaForm kappaForm_isInvariant x n) v) =
      R.rho (ofLoop kappaForm kappaForm_isInvariant x n) (R.eval v) :=
  R.eval_action _ v

/-- Basis-current form of `eval_vacuumRho`. -/
theorem eval_J (a : Fin 3) (n : ℤ) (v : WakModule k) :
    R.eval (J k a n v) =
      R.rho (ofLoop kappaForm kappaForm_isInvariant (basis a) n) (R.eval v) := by
  exact R.eval_vacuumRho (basis a) n v

end VacuumCurrentRealization

end

end VOA.AffineVOA
