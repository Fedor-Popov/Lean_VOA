/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO3Assoc

/-! # O3: the ambient VOA is a haploid commutative algebra in the logarithmic category

Let `W` be a VOA, `G ≤ Aut W`, and suppose `W^G` is `C₂`-cofinite and `W` is finitely
generated over `W^G`. In the braided monoidal category `C = LogModuleCat (W^G)`
(`logarithmicMonoidalCategory`, `logarithmicBraidedCategory`), the object `V = vObj G hfg` is:

* a monoid object (`monObj`), with unit the inclusion `W^G ↪ W` and multiplication induced
  by `Y_W`;
* commutative (`isCommMonObj`) for the braiding `swapIso … 0`;
* haploid (`finrank_unit_hom`);
* acted on by `G` through monoid-object automorphisms (`isMonHom_autHom`);
* equipped with the averaging counit `ε` (`counitHom`), with `ι ≫ ε = 𝟙` and
  `ε ≫ ι = |G|⁻¹ Σ_g g`.

`V2mMonObj` specializes this to `V = V₂` and a finite `G ≤ Aut V₂`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO3
open CategoryTheory MonoidalCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
  (hC2 : C2Cofinite (orbifoldVOA G))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **Associativity**: `(μ ⊠ 1) ≫ μ = α ≫ (1 ⊠ μ) ≫ μ` in `C`. -/
theorem mulHom_assoc :
    tensorMorphism hC2 (mulHom G hfg hC2) (𝟙 (vObj G hfg)) ≫ mulHom G hfg hC2 =
      (associatorIso hC2 (vObj G hfg) (vObj G hfg) (vObj G hfg)).hom ≫
        tensorMorphism hC2 (𝟙 (vObj G hfg)) (mulHom G hfg hC2) ≫ mulHom G hfg hC2 := by
  apply hom_ext
  intro q
  exact congrArg (fun F => F q) (mulWeakHom_assoc G hC2 hfg)

set_option maxHeartbeats 4000000 in
/-- **The ambient VOA is a monoid object of the logarithmic category of `W^G`.** -/
abbrev monObj :
    letI := logarithmicMonoidalCategory hC2
    MonObj (vObj G hfg) :=
  letI := logarithmicMonoidalCategory hC2
  { one := unitHom G hfg
    mul := mulHom G hfg hC2
    one_mul := mulHom_one_mul G hfg hC2
    mul_one := mulHom_mul_one G hfg hC2
    mul_assoc := mulHom_assoc G hfg hC2 }

theorem monObj_one :
    letI := logarithmicMonoidalCategory hC2
    letI := monObj G hfg hC2
    (MonObj.one : 𝟙_ (LogModuleCat (orbifoldVOA G)) ⟶ vObj G hfg) = unitHom G hfg := rfl

theorem monObj_mul :
    letI := logarithmicMonoidalCategory hC2
    letI := monObj G hfg hC2
    (MonObj.mul : vObj G hfg ⊗ vObj G hfg ⟶ vObj G hfg) = mulHom G hfg hC2 := rfl

set_option maxHeartbeats 4000000 in
/-- **The ambient VOA is a commutative algebra** in the braided category `C`. -/
theorem isCommMonObj :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    letI := monObj G hfg hC2
    IsCommMonObj (vObj G hfg) := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  letI := monObj G hfg hC2
  exact ⟨mulHom_comm G hfg hC2⟩

set_option maxHeartbeats 4000000 in
/-- Each `g ∈ G` is an automorphism of the monoid object. -/
theorem isMonHom_autHom (g : G) :
    letI := logarithmicMonoidalCategory hC2
    letI := monObj G hfg hC2
    IsMonHom (autHom G hfg g) := by
  letI := logarithmicMonoidalCategory hC2
  letI := monObj G hfg hC2
  exact ⟨unitHom_autHom G hfg g, (autHom_mul G hfg hC2 g).symm⟩

/-- **Summary (O3, items 1–3)**: a haploid commutative algebra with `G`-action and
averaging counit. -/
theorem haploidCommAlgebra [Nontrivial V] [Fintype G] :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    letI := monObj G hfg hC2
    IsCommMonObj (vObj G hfg) ∧
      Module.finrank ℂ (𝟙_ (LogModuleCat (orbifoldVOA G)) ⟶ vObj G hfg) = 1 ∧
      (∀ g : G, IsMonHom (autHom G hfg g)) ∧
      MonObj.one ≫ counitHom G hfg = 𝟙 _ ∧
      counitHom G hfg ≫ MonObj.one =
        (Fintype.card G : ℂ)⁻¹ • ∑ g : G, autHom G hfg g :=
  ⟨isCommMonObj G hfg hC2, finrank_unit_hom G hfg, isMonHom_autHom G hfg hC2,
    unitHom_counitHom G hfg, counitHom_unitHom G hfg⟩

/-! ## The case `V₂` -/

/-- **`V₂` as a commutative algebra** in the logarithmic category of `V₂^G`, for finite
`G ≤ Aut V₂` with `C₂`-cofinite fixed-point algebra. -/
abbrev V2mMonObj (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G]
    (hC2 : C2Cofinite (orbifoldVOA G)) :
    letI := logarithmicMonoidalCategory hC2
    MonObj (V2mObj G) :=
  monObj G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2

theorem V2m_isCommMonObj (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G]
    (hC2 : C2Cofinite (orbifoldVOA G)) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    letI := V2mMonObj G hC2
    IsCommMonObj (V2mObj G) :=
  isCommMonObj G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2

end VOA.Classification.COne.McRaeO3
