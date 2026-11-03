/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SuperNearVOA
import VOA.Modules.ZhuVermaAnArchL0Semisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Ordinary-module structures on invariant subspaces

An invariant subspace of a weak module is itself a weak module, by restricting every mode to the
subspace.  If the ambient module is ordinary, its invariant subspaces inherit the ambient weight
grading.  The only non-formal point is internality of the restricted grading: invariance under
`L₀` isolates every homogeneous component, so `Core.SuperNearVOA.isInternal_comap` applies.

This is deliberately stated for an arbitrary weak submodule, not only an ideal in the adjoint
module.  It is the missing subtype counterpart of the existing quotient construction
`OrdVModule.quotient`.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

namespace WeakModule

variable (A : WeakModule W M) (P : Submodule' A)

/-- The field action of `A` restricted coefficientwise to an invariant subspace `P`. -/
noncomputable def submoduleYM : 𝒱 →ₗ[ℂ] (End ℂ P.carrier)⟦z^±⟧ where
  toFun u k :=
    { toFun := fun x => ⟨(A.YM u) k (x : M), by
        have h := P.act_mem u (-k - 1) x.property
        rw [act_def, mode_apply, show (-(-k - 1) - 1 : ℤ) = k by ring] at h
        exact h⟩
      map_add' := fun x y => Subtype.ext (map_add ((A.YM u) k) (x : M) (y : M))
      map_smul' := fun c x => Subtype.ext (map_smul ((A.YM u) k) c (x : M)) }
  map_add' u v := by
    apply FormalDist.ext
    intro k
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (A.YM (u + v) k) (x : M) = (A.YM u k) (x : M) + (A.YM v k) (x : M)
    rw [map_add]
    rfl
  map_smul' c u := by
    apply FormalDist.ext
    intro k
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (A.YM (c • u) k) (x : M) = c • (A.YM u k) (x : M)
    rw [map_smul]
    rfl

@[simp] theorem submoduleYM_coeff_coe (u : 𝒱) (k : ℤ) (x : P.carrier) :
    ((submoduleYM A P u k x : P.carrier) : M) = (A.YM u) k (x : M) := rfl

@[simp] theorem submoduleYM_mode_coe (u : 𝒱) (n : ℤ) (x : P.carrier) :
    ((mode (submoduleYM A P u) n x : P.carrier) : M) = mode (A.YM u) n (x : M) := rfl

/-- An invariant subspace of a weak module, with the restricted action. -/
noncomputable def submodule : WeakModule W P.carrier where
  YM := submoduleYM A P
  vacuum_YM := by
    apply FormalDist.ext
    intro k
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (A.YM W.vacuum k) (x : M) =
      ((if k = 0 then (1 : End ℂ P.carrier) else 0) x : P.carrier)
    rw [A.vacuum_YM, FormalDist.one_apply]
    split_ifs <;> rfl
  truncation := by
    intro u x
    obtain ⟨N, hN⟩ := A.truncation u (x : M)
    refine ⟨N, fun n hn => ?_⟩
    apply Subtype.ext
    simpa only [submoduleYM_mode_coe, Submodule.coe_zero] using hN n hn
  jacobi := by
    intro u v x ℓ m n
    apply Subtype.ext
    let incl : P.carrier →ₗ[ℂ] M := P.carrier.subtype
    have hfinL : (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (mode (submoduleYM A P u) (ℓ + m - i) (mode (submoduleYM A P v) (n + i) x)
          - negOnePow ℓ • mode (submoduleYM A P v) (ℓ + n - i)
              (mode (submoduleYM A P u) (m + i) x))).Finite := by
      apply (jacL_fin A u v (x : M) ℓ m n).subset
      intro i hi
      rw [Function.mem_support] at hi ⊢
      intro hamb
      apply hi
      apply Subtype.ext
      simpa only [Submodule.coe_zero, Submodule.coe_smul, Submodule.coe_sub,
        submoduleYM_mode_coe] using hamb
    have hfinR : (Function.support fun i : ℤ => cbz m i •
        mode (submoduleYM A P (W.smul u (ℓ + i) v)) (m + n - i) x).Finite := by
      apply (jacR_fin A u v (x : M) ℓ m n).subset
      intro i hi
      rw [Function.mem_support] at hi ⊢
      intro hamb
      apply hi
      apply Subtype.ext
      simpa only [Submodule.coe_zero, Submodule.coe_smul,
        submoduleYM_mode_coe] using hamb
    change incl (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (submoduleYM A P u) (ℓ + m - i) (mode (submoduleYM A P v) (n + i) x)
          - negOnePow ℓ • mode (submoduleYM A P v) (ℓ + n - i)
              (mode (submoduleYM A P u) (m + i) x))) =
      incl (∑ᶠ i : ℤ, cbz m i •
        mode (submoduleYM A P (W.smul u (ℓ + i) v)) (m + n - i) x)
    rw [show incl _ = incl.toAddMonoidHom _ from rfl, map_finsum incl.toAddMonoidHom hfinL,
      show incl _ = incl.toAddMonoidHom _ from rfl, map_finsum incl.toAddMonoidHom hfinR]
    simp only [LinearMap.toAddMonoidHom_coe, incl, map_smul, map_sub,
      submoduleYM_mode_coe]
    exact A.jacobi u v (x : M) ℓ m n

@[simp] theorem submodule_act_coe (u : 𝒱) (n : ℤ) (x : P.carrier) :
    (((submodule A P).act u n x : P.carrier) : M) = A.act u n (x : M) := rfl

end WeakModule

namespace OrdVModule

variable (N : OrdVModule W M) (P : WeakModule.Submodule' N.toWeakModule)

/-- The ambient weight space pulled back to the invariant subtype. -/
def submoduleWeight (a : ℂ) : Submodule ℂ P.carrier :=
  (N.weight a).comap P.carrier.subtype

@[simp] theorem submoduleWeight_coe {a : ℂ} {x : P.carrier} :
    x ∈ submoduleWeight N P a ↔ (x : M) ∈ N.weight a := Iff.rfl

/-- Every weak submodule of an ordinary module inherits the ambient internal grading. -/
theorem submoduleWeight_isInternal : DirectSum.IsInternal (submoduleWeight N P) := by
  classical
  letI : DirectSum.Decomposition N.weight := N.isInternal.chooseDecomposition
  apply isInternal_comap N.weight P.carrier
  intro a x hx
  rw [homogProj_apply]
  by_cases hz : (DirectSum.decompose N.weight (x : M) a : N.weight a) = 0
  · simpa [hz] using P.carrier.zero_mem
  · apply N.component_mem_of_invariant P hx
    simpa only [DFinsupp.mem_support_iff] using hz

/-- Every restricted weight space is finite-dimensional. -/
theorem submoduleWeight_finiteDimensional (a : ℂ) :
    FiniteDimensional ℂ (submoduleWeight N P a) := by
  haveI := N.finrank a
  let f : submoduleWeight N P a →ₗ[ℂ] N.weight a :=
    { toFun := fun x => ⟨((x : P.carrier) : M), x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  dsimp [f] at h
  exact congrArg (fun z : N.weight a => (z : M)) h

/-- The ambient lower bound restricts to every invariant subtype. -/
theorem submoduleWeight_boundedBelow :
    ∃ B : ℝ, ∀ a : ℂ, submoduleWeight N P a ≠ ⊥ → B ≤ a.re := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine ⟨B, fun a ha => hB a ?_⟩
  intro hbot
  apply ha
  rw [submoduleWeight, hbot, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr P.carrier.subtype_injective

/-- An invariant subspace of an ordinary module, as an ordinary module on its subtype. -/
noncomputable def submodule : OrdVModule W P.carrier where
  toWeakModule := WeakModule.submodule N.toWeakModule P
  weight := submoduleWeight N P
  isInternal := submoduleWeight_isInternal N P
  L0_weight := by
    intro a x hx
    apply Subtype.ext
    simpa only [WeakModule.submoduleYM_mode_coe, Submodule.coe_smul] using
      N.L0_weight a (x : M) hx
  finrank := submoduleWeight_finiteDimensional N P
  boundedBelow := submoduleWeight_boundedBelow N P

@[simp] theorem submodule_toWeakModule :
    (submodule N P).toWeakModule = WeakModule.submodule N.toWeakModule P := rfl

@[simp] theorem submodule_weight (a : ℂ) :
    (submodule N P).weight a = submoduleWeight N P a := rfl

@[simp] theorem submodule_act_coe (u : 𝒱) (n : ℤ) (x : P.carrier) :
    (((submodule N P).act u n x : P.carrier) : M) = N.act u n (x : M) := rfl

end OrdVModule

end VOA

#print axioms VOA.WeakModule.submodule
#print axioms VOA.OrdVModule.submodule
