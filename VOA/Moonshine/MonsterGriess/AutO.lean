/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/Griess/ProductInvariance.lean
  CFSG/Monster/Griess/AutFinite.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.Algebra
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Axiom's Monster port, part 6: `AutO`, the automorphism group of the rational Griess algebra

`AutO : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)` — the ℚ-linear automorphisms of
`SpaceB = symMat × SpaceX × SpaceW` (dimension 300 + 98280 + 98304 = 196884) that preserve the
product `gmul` (`IsAlgAut`) and the form `bform`.  In Axiom Math's CFSG repository
(`CFSG/Monster/Existence/Defs.lean`) the Monster is `MGriess := ↥CFSG.Monster.Griess.AutO`, and
they prove `MonsterExistenceStatement ↥AutO`.  This file states the same subgroup in LeanVOA, so
that `Nonempty (Aut VnatVOA ≃* MonsterGriess.AutO)` (`Notes/MONSTER_AUT_PLAN.md`) refers to
their Monster.  **Only the definition is ported**: finiteness, simplicity and the order of `AutO`
are theorems of the CFSG repository (Lean v4.35.0-rc3) and are not available here.

## Port notes
* Namespace `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess`; module-system syntax dropped.
* `IsAlgAut`, `isAlgAut_one`, `IsAlgAut.mul`, `IsAlgAut.inv` come from
  `CFSG/Monster/Griess/ProductInvariance.lean`; `AutO`, `mem_AutO` from
  `CFSG/Monster/Griess/AutFinite.lean`.  All verbatim.
-/

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin Matrix Module

/-! ### From `CFSG/Monster/Griess/ProductInvariance.lean` -/
def IsAlgAut (f : SpaceB ≃ₗ[ℚ] SpaceB) : Prop := ∀ u v, f (gmul u v) = gmul (f u) (f v)

theorem isAlgAut_one : IsAlgAut 1 := fun _ _ => rfl

theorem IsAlgAut.mul {f g : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsAlgAut f) (hg : IsAlgAut g) :
    IsAlgAut (f * g) := fun u v => by
  change f (g (gmul u v)) = gmul (f (g u)) (f (g v))
  rw [hg, hf]

theorem IsAlgAut.inv {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsAlgAut f) : IsAlgAut f⁻¹ := fun u v => by
  change f.symm (gmul u v) = gmul (f.symm u) (f.symm v)
  apply f.injective
  rw [f.apply_symm_apply, hf, f.apply_symm_apply, f.apply_symm_apply]

/-! ### From `CFSG/Monster/Griess/AutFinite.lean` -/
def AutO : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) where
  carrier := {g | IsAlgAut g ∧ ∀ u v, bform (g u) (g v) = bform u v}
  mul_mem' {f g} hf hg := ⟨hf.1.mul hg.1, fun u v => by
    change bform (f (g u)) (f (g v)) = bform u v
    rw [hf.2, hg.2]⟩
  one_mem' := ⟨isAlgAut_one, fun _ _ => rfl⟩
  inv_mem' {f} hf := ⟨hf.1.inv, fun u v => by
    change bform (f.symm u) (f.symm v) = bform u v
    rw [← hf.2, f.apply_symm_apply, f.apply_symm_apply]⟩

theorem mem_AutO {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ AutO ↔ (∀ u v, g (gmul u v) = gmul (g u) (g v)) ∧ ∀ u v, bform (g u) (g v) = bform u v :=
  Iff.rfl

end VOA.Moonshine.MonsterGriess
