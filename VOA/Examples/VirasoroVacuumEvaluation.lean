/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDeformationModes

/-!
# Universal evaluation from fixed-charge Virasoro modes

Mode commutators extend to the full Lie algebra and then its enveloping algebra.
Vacuum evaluation kills the defining left ideal, so it descends to the actual
universal vacuum module. No independence or PBW assumption is used here.
-/
namespace VOA.VirDeformModes
open Module (End)
open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra VirModule
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable (A : CentralVirasoroData E) {c : ℂ} (hK : A.central = c • (1 : End ℂ E))

/-- The Witt-level linear map `ℓₙ ↦ A.L n` (extended `ℂ`-linearly over `Witt = ℤ →₀ ℂ`). -/
noncomputable def rhoW : Witt →ₗ[ℂ] End ℂ E :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ (End ℂ E) (A.L n))

/-- A single Witt coefficient acts by that scalar times its mode. -/
@[simp] theorem rhoW_single (n : ℤ) (a : ℂ) :
    rhoW A (Finsupp.single n a) = a • A.L n := by
  simp only [rhoW, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- **The projective Witt identity**: `rhoW⁅u,v⁆ + ψ(u,v)·(c·id) = ⁅rhoW u, rhoW v⁆` with the
Gel'fand–Fuks cocycle and the given scalar center. Finite-support induction
extends the mode relation to arbitrary Witt elements. -/
theorem rhoW_proj (hK : A.central = c • (1 : End ℂ E)) (u v : Witt) :
    rhoW A ⁅u, v⁆ + (Witt.cocycleₗ u v) • (c • (LinearMap.id : End ℂ E))
      = ⁅rhoW A u, rhoW A v⁆ := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
      simp only [Witt.bracket_def, map_add, LinearMap.add_apply, add_lie] at h₁ h₂ ⊢
      rw [← h₁, ← h₂]; module
  | single m a =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ =>
          simp only [Witt.bracket_def, map_add, lie_add] at h₁ h₂ ⊢
          rw [← h₁, ← h₂]; module
      | single n b =>
          have hcomm : ⁅rhoW A (Finsupp.single m a), rhoW A (Finsupp.single n b)⁆
              = (a * b) • (A.L m * A.L n - A.L n * A.L m) := by
            rw [rhoW_single, rhoW_single, LieRing.of_associative_ring_bracket,
              smul_mul_assoc, mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
            module
          rw [Witt.bracket_def, Witt.bracketₗ_single, rhoW_single, Witt.cocycleₗ_single, hcomm,
            ← LieRing.of_associative_ring_bracket, A.comm, hK, Witt.gfCoeff]
          by_cases hmn : m + n = 0
          · rw [if_pos hmn, if_pos hmn]
            simp only [smul_add, smul_smul]
            module
          · rw [if_neg hmn, if_neg hmn]
            simp only [smul_smul, zero_smul, add_zero]
            module

/-- The linear map `𝔙𝔦𝔯 → End E` underlying the fixed-charge representation:
`Lₙ ↦ A.L n`, `C ↦ c·id`. -/
noncomputable def rhoLin : Virasoro →ₗ[ℂ] End ℂ E where
  toFun x := rhoW A ((ofProd gfCocycle).symm x).1
    + ((ofProd gfCocycle).symm x).2 • (c • (LinearMap.id : End ℂ E))
  map_add' x y := by
    simp only [of_symm_add, Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' r x := by
    simp only [of_symm_smul, Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    module

/-- Extend fixed-charge mode data to a representation of the full Virasoro
algebra. The scalar central terms commute with every mode. -/
noncomputable def fixedRho : Virasoro →ₗ⁅ℂ⁆ End ℂ E :=
  { rhoLin A (c := c) with
    map_lie' := by
      intro x y
      show rhoLin A (c := c) ⁅x, y⁆ = ⁅rhoLin A (c := c) x, rhoLin A (c := c) y⁆
      set u := ((ofProd gfCocycle).symm x).1 with hu
      set v := ((ofProd gfCocycle).symm y).1 with hv
      have he : ∀ z : Virasoro, rhoLin A (c := c) z = rhoW A ((ofProd gfCocycle).symm z).1
          + ((ofProd gfCocycle).symm z).2 • (c • (LinearMap.id : End ℂ E)) :=
        fun z => rfl
      -- LHS: `rhoLin ⁅x,y⁆ = ⁅rhoW u, rhoW v⁆` via the projective identity + `bracket_ofTwoCocycle`
      have h1 : ((ofProd gfCocycle).symm ⁅x, y⁆).1 = ⁅u, v⁆ := by
        rw [bracket_ofTwoCocycle, Equiv.symm_apply_apply]
      have h2 : ((ofProd gfCocycle).symm ⁅x, y⁆).2 = Witt.cocycleₗ u v := by
        rw [bracket_ofTwoCocycle, Equiv.symm_apply_apply]
        simp only [trivial_lie_zero, add_zero, sub_zero]
        rfl
      have hL : rhoLin A (c := c) ⁅x, y⁆ = ⁅rhoW A u, rhoW A v⁆ := by
        rw [← rhoW_proj A hK u v, he ⁅x, y⁆, h1, h2]
      -- RHS: the two central `id`-summands drop out of the bracket
      have hR : ⁅rhoLin A (c := c) x, rhoLin A (c := c) y⁆ = ⁅rhoW A u, rhoW A v⁆ := by
        show rhoLin A (c := c) x * rhoLin A (c := c) y - rhoLin A (c := c) y * rhoLin A (c := c) x
            = rhoW A u * rhoW A v - rhoW A v * rhoW A u
        rw [he x, he y, ← hu, ← hv]
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
          show (LinearMap.id : End ℂ E) = 1 from rfl, mul_one, one_mul]
        module
      rw [hL, hR] }

/-- The full representation recovers each supplied mode on its generator. -/
@[simp] theorem fixedRho_L (n : ℤ) : fixedRho A hK (L n) = A.L n := by
  show rhoLin A (c := c) (L n) = A.L n
  rw [rhoLin, L]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply, rhoW_single, one_smul,
    Witt.gen]
  rw [show ((0 : ℂ) : ℂ) • (c • (LinearMap.id : End ℂ E)) = 0 from by
      rw [zero_smul], add_zero]

/-- The full representation has the specified scalar central charge. -/
@[simp] theorem fixedRho_C :
    fixedRho A hK C = c • (LinearMap.id : End ℂ E) := by
  show rhoLin A (c := c) C = _
  rw [rhoLin, C]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply, map_zero, zero_add, one_smul]


/-- A Virasoro representation with a chosen vacuum, at a specified scalar
charge. The annihilation laws are precisely the generators of the vacuum ideal. -/
structure VacuumVirasoroRealization (c : ℂ) (E : Type*)
    [AddCommGroup E] [Module ℂ E] where
  rho : Virasoro →ₗ⁅ℂ⁆ End ℂ E
  vacuum : E
  acts_central : rho C = c • (1 : End ℂ E)
  pos_annihilate : ∀ n : ℤ, -1 ≤ n → rho (L n) vacuum = 0

/-- Fixed-charge mode data and a vacuum construct the full realization.
The Lie representation is derived from the mode relations, not supplied separately. -/
noncomputable def fixedVacuum (v : E) (hv : ∀ n : ℤ, -1 ≤ n → A.L n v = 0) :
    VacuumVirasoroRealization c E where
  rho := fixedRho A hK
  vacuum := v
  acts_central := fixedRho_C A hK
  pos_annihilate n hn := by rw [fixedRho_L]; exact hv n hn

namespace VacuumVirasoroRealization
variable {c : ℂ} (R : VacuumVirasoroRealization c E)

/-- Extend the Lie action to the associative enveloping algebra. -/
noncomputable def envelopeAction : UVir →ₐ[ℂ] End ℂ E :=
  UniversalEnvelopingAlgebra.lift ℂ R.rho

/-- Embedded Lie generators act by their original representation operators. -/
@[simp] theorem envelopeAction_ι (X : Virasoro) :
    R.envelopeAction (ι ℂ X) = R.rho X := by
  rw [envelopeAction, UniversalEnvelopingAlgebra.lift_ι_apply]

/-- Act on the chosen vacuum by an enveloping-algebra element. -/
noncomputable def envelopeEval : UVir →ₗ[ℂ] E where
  toFun u := R.envelopeAction u R.vacuum
  map_add' u v := by rw [map_add, LinearMap.add_apply]
  map_smul' c u := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The identity creates the vacuum itself. -/
@[simp] theorem envelopeEval_one : R.envelopeEval 1 = R.vacuum := by
  change R.envelopeAction 1 R.vacuum = R.vacuum
  rw [map_one]
  rfl

/-- Each relation defining the universal vacuum module annihilates the vacuum. -/
theorem envelopeEval_vacGens (u : UVir) (hu : u ∈ vacGens c) :
    R.envelopeEval u = 0 := by
  rcases hu with ⟨n, hn, rfl⟩ | rfl
  · change R.envelopeAction (ι ℂ (L n)) R.vacuum = 0
    rw [R.envelopeAction_ι]
    exact R.pos_annihilate n hn
  · change R.envelopeAction (ι ℂ C - algebraMap ℂ UVir c) R.vacuum = 0
    rw [map_sub, LinearMap.sub_apply, R.envelopeAction_ι, R.acts_central,
      AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]

/-- The whole left ideal evaluates to zero: left multiplication preserves
annihilation because it composes another operator with a zero vector. -/
theorem envelopeEval_vacIdeal (u : UVir) (hu : u ∈ vacIdeal c) :
    R.envelopeEval u = 0 := by
  induction hu using Submodule.span_induction with
  | mem g hg => exact R.envelopeEval_vacGens g hg
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul a b _ hb =>
      rw [show (a • b : UVir) = a * b from rfl]
      change R.envelopeAction (a * b) R.vacuum = 0
      change R.envelopeAction b R.vacuum = 0 at hb
      rw [map_mul, Module.End.mul_apply, hb, map_zero]

/-- Descend evaluation to the actual universal vacuum module. No basis or
choice of word representative is needed to define this linear map. -/
noncomputable def eval : VirUniv c →ₗ[ℂ] E where
  toFun := QuotientAddGroup.lift (vacIdeal c).toAddSubgroup
    R.envelopeEval.toAddMonoidHom (fun u hu => R.envelopeEval_vacIdeal u hu)
  map_add' x y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact R.envelopeEval.map_add x y
  map_smul' c x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact R.envelopeEval.map_smul c x

/-- Evaluation on a quotient class agrees with any representative. -/
@[simp] theorem eval_mk (u : UVir) :
    R.eval (Submodule.Quotient.mk u) = R.envelopeEval u := rfl

/-- The universal vacuum evaluates to the chosen vacuum. -/
@[simp] theorem eval_vacuum : R.eval (vacVec c) = R.vacuum := by
  rw [vacVec, R.eval_mk, R.envelopeEval_one]

/-- Evaluation intertwines every Virasoro Lie algebra element. -/
theorem eval_action (X : Virasoro) (v : VirUniv c) :
    R.eval (virVacRho c X v) = R.rho X (R.eval v) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [virVacRho_mk, R.eval_mk, R.eval_mk]
  change R.envelopeAction (ι ℂ X * u) R.vacuum = _
  rw [map_mul, Module.End.mul_apply, R.envelopeAction_ι]
  rfl

end VacuumVirasoroRealization
end VOA.VirDeformModes
