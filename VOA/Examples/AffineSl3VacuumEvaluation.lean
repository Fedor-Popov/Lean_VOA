/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3CurrentRepresentation

/-!
# Actual vacuum evaluation and nonvanishing for affine sl3

The explicit full affine representation kills the defining left ideal of the
universal vacuum module. Its evaluation therefore descends to that actual
quotient and sends its vacuum to the nonzero constant polynomial. This proves
nonvanishing at every level without invoking a PBW axiom. Injectivity of this
evaluation or a PBW basis is not asserted here.
-/
namespace VOA.AffineSl3
open VOA.AffineLie Module UniversalEnvelopingAlgebra
noncomputable section
/-- The actual induced affine vacuum quotient at level k. -/
abbrev Vacuum (k : ℂ) := vacuumSpace form form_invariant k
namespace FreeField
variable (k : ℂ)
/-- The universal enveloping algebra of the affine `sl3` algebra. -/
abbrev Envelope := UEnv Sl3 form form_invariant

/-- The associative action induced from the affine Lie representation. -/
noncomputable def envelopeAction : Envelope →ₐ[ℂ] End ℂ Fock :=
  UniversalEnvelopingAlgebra.lift ℂ (representation k)

/-- A Lie algebra generator embedded in the universal enveloping algebra acts
by the original representation operator. This is the defining compatibility of
the enveloping-algebra extension. -/
@[simp] theorem envelopeAction_ι (X : Algebra) :
    (envelopeAction k) (UniversalEnvelopingAlgebra.ι ℂ X) = (representation k) X := by
  rw [envelopeAction, UniversalEnvelopingAlgebra.lift_ι_apply]

/-- Vacuum evaluation `u |-> rho(u) vacuum` on the universal enveloping algebra. -/
noncomputable def envelopeEval : Envelope →ₗ[ℂ] Fock where
  toFun u := (envelopeAction k) u (1 : Fock)
  map_add' u v := by rw [map_add, LinearMap.add_apply]
  map_smul' c u := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The identity of the enveloping algebra evaluates to the chosen vacuum: its
operator action is the identity, so it creates no descendants or corrections. -/
@[simp] theorem envelopeEval_one : (envelopeEval k) 1 = (1 : Fock) := by
  change (envelopeAction k) 1 (1 : Fock) = (1 : Fock)
  rw [map_one (envelopeAction k)]
  rfl

/-- Every generator of the affine vacuum ideal has zero vacuum evaluation. -/
theorem envelopeEval_vacuumGens (u : Envelope)
    (hu : u ∈ vacuumGens form form_invariant k) : (envelopeEval k) u = 0 := by
  rcases hu with ⟨x, n, hn, rfl⟩ | rfl | rfl
  · change (envelopeAction k)
      (UniversalEnvelopingAlgebra.ι ℂ (ofLoop form form_invariant x n))
        (1 : Fock) = 0
    rw [(envelopeAction_ι k)]
    exact representation_vacuum k x n hn
  · change ((envelopeAction k)
      (UniversalEnvelopingAlgebra.ι ℂ (AffineLie.C form form_invariant) -
        algebraMap ℂ Envelope k)) (1 : Fock) = 0
    rw [map_sub, LinearMap.sub_apply, (envelopeAction_ι k), representation_central,
      AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  · change (envelopeAction k)
      (UniversalEnvelopingAlgebra.ι ℂ (ell0 form form_invariant)) (1 : Fock) = 0
    rw [(envelopeAction_ι k)]
    exact representation_degree_vacuum k

/-- The whole left ideal defining the vacuum module has zero vacuum evaluation. -/
theorem envelopeEval_vacuumIdeal (u : Envelope)
    (hu : u ∈ vacuumIdeal form form_invariant k) : (envelopeEval k) u = 0 := by
  induction hu using Submodule.span_induction with
  | mem g hg => exact (envelopeEval_vacuumGens k) g hg
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul a b _ hb =>
      rw [show (a • b : Envelope) = a * b from rfl]
      change (envelopeAction k) (a * b) (1 : Fock) = 0
      change (envelopeAction k) b (1 : Fock) = 0 at hb
      rw [map_mul, Module.End.mul_apply, hb, map_zero]

/-- The universal free-field evaluation `V^k(sl3) -> Fock` obtained from the proved actual current action. -/
noncomputable def eval : Vacuum k →ₗ[ℂ] Fock where
  toFun := QuotientAddGroup.lift
    (vacuumIdeal form form_invariant k).toAddSubgroup
    (envelopeEval k).toAddMonoidHom
    (fun u hu => (envelopeEval_vacuumIdeal k) u hu)
  map_add' x y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact (envelopeEval k).map_add x y
  map_smul' c x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (envelopeEval k).map_smul c x

/-- Evaluation of a vacuum-module quotient class is evaluation of any chosen
enveloping-algebra representative. Independence of the representative follows
from annihilation of the defining vacuum ideal. -/
@[simp] theorem eval_mk (u : Envelope) :
    (eval k) (Submodule.Quotient.mk u) = (envelopeEval k) u := rfl

/-- The universal evaluation sends the affine vacuum to the supplied vacuum. -/
@[simp] theorem eval_vacuum :
    (eval k) (vacuumVector form form_invariant k) = (1 : Fock) := by
  rw [vacuumVector, (eval_mk k), (envelopeEval_one k)]

/-- Universal evaluation intertwines the whole affine Lie algebra, including
the degree derivation and central element. Multiplication in its enveloping
algebra descends through the vacuum ideal, so no extra representation input is needed. -/
theorem eval_action (X : Algebra) (v : Vacuum k) :
    (eval k) (vacuumRho form form_invariant k X v) =
      (representation k) X ((eval k) v) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [vacuumRho_mk, (eval_mk k), (eval_mk k)]
  change (envelopeAction k) (UniversalEnvelopingAlgebra.ι ℂ X * u) (1 : Fock) = _
  rw [map_mul, Module.End.mul_apply, (envelopeAction_ι k)]
  rfl

/-- The universal evaluation intertwines every loop action. -/
theorem eval_vacuumRho (x : Sl3) (n : ℤ) (v : Vacuum k) :
    (eval k) (vacuumRho form form_invariant k
      (ofLoop form form_invariant x n) v) =
      (representation k) (ofLoop form form_invariant x n) ((eval k) v) :=
  (eval_action k) _ v


/-- The actual universal affine sl3 vacuum is nonzero at every level:
its free-field evaluation is the constant polynomial one. -/
theorem universal_vacuum_ne_zero : vacuumVector form form_invariant k ≠ 0 := by
  intro h
  have he := congrArg (eval k) h
  rw [eval_vacuum, map_zero] at he
  exact one_ne_zero he

/-- The induced affine vacuum quotient is a nontrivial vector space, established
by the explicit representation rather than any PBW independence assumption. -/
theorem universal_vacuum_nontrivial : Nontrivial (Vacuum k) :=
  ⟨⟨vacuumVector form form_invariant k, 0, universal_vacuum_ne_zero k⟩⟩
end FreeField
end
end VOA.AffineSl3
