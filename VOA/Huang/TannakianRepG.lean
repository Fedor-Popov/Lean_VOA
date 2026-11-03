/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.Data.Complex.Basic
import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# The regular algebra of `Rep(G)`

For a finite group `G`, the function algebra `Fun(G) = (G → ℂ)` with the right regular action
(`TannakaDuality.FiniteGroup.rightFDRep`) is the **regular algebra** of `Rep(G)`: the algebra
object whose image under the Tannakian equivalence `Rep(V)_{h∈ℤ} ≃ Rep(G)` is the conformal
extension `W ⊇ V` of GR Prop. 2.13.  Its multiplicities are the dimensions:

* `homRightFDRepEquiv : (Fun(G) ⟶ X) ≃ₗ[ℂ] X` (Frobenius reciprocity, `φ ↦ φ(δ₁)`), hence
* `finrank_hom_rightFDRep : dim Hom_G(Fun(G), X) = dim X`.

For an irreducible `X`, `dim Hom_G(Fun(G), X)` is the multiplicity of `X` in `Fun(G)` (Maschke +
Schur), so `Fun(G) ≅ ⊕_X (dim X) · X`: the source of `ch_W = ∑_a d_a ch_a` in `ITannakian`.

The algebra structure:
* `funMonObj : MonObj Fun(G)` (unit `funOne`, multiplication Mathlib's `mulRepHom`; the axioms
  are those of `ModuleCat.MonModuleEquivalenceAlgebra.inverseObj` for the algebra `G → ℂ`),
* `funIsCommMonObj` — commutative,
* `homUnitFunEquiv`, `finrank_hom_unit_fun` — **haploid**: `dim Hom_G(𝟙, Fun(G)) = 1`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.Tannakian

open CategoryTheory MonoidalCategory Module TannakaDuality.FiniteGroup

variable {G : Type} [Group G]

/-- `δ_s = rightRegular(s⁻¹) δ₁`. -/
theorem rightRegular_inv_single_one [DecidableEq G] (s : G) :
    rightRegular (k := ℂ) s⁻¹ (Pi.single 1 1) = Pi.single s 1 := by
  funext t
  simp only [rightRegular_apply, Pi.single_apply, mul_inv_eq_one]

/-- Equivariance of a `G`-map out of `Fun(G)`, on vectors. -/
theorem map_rightRegular [Finite G] (X : FDRep ℂ G) (φ : (rightFDRep : FDRep ℂ G) ⟶ X) (g : G) (f : G → ℂ) :
    φ.hom (rightRegular g f) = X.ρ g (φ.hom f) :=
  congr(($(φ.comm g)).hom f)

/-- Every `G`-map out of `Fun(G)` is determined by the image of `δ₁`. -/
theorem eq_ofRightFDRep [Fintype G] [DecidableEq G] (X : FDRep ℂ G) (φ : (rightFDRep : FDRep ℂ G) ⟶ X) :
    ofRightFDRep X (φ.hom (Pi.single 1 1)) = φ := by
  ext f
  change sumSMulInv (φ.hom (Pi.single 1 1)) f = φ.hom f
  rw [sumSMulInv_apply]
  simp_rw [← map_rightRegular, rightRegular_inv_single_one]
  conv_rhs => rw [show f = ∑ s, f s • (Pi.single s 1 : G → ℂ) from by
    funext t; simp [Pi.single_apply]]
  have hL : ∀ x : G → ℂ, φ.hom x = φ.hom.hom.hom x := fun x => rfl
  simp only [hL]
  erw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  erw [map_smul]

/-- **Frobenius reciprocity for the regular representation**:
`Hom_G(Fun(G), X) ≃ X`, `φ ↦ φ(δ₁)`. -/
def homRightFDRepEquiv [Fintype G] [DecidableEq G] (X : FDRep ℂ G) : ((rightFDRep : FDRep ℂ G) ⟶ X) ≃ₗ[ℂ] X where
  toFun φ := φ.hom (Pi.single 1 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ofRightFDRep X v
  left_inv φ := eq_ofRightFDRep X φ
  right_inv v := sumSMulInv_single_id v

/-- `dim Hom_G(Fun(G), X) = dim X`: every irreducible `X` occurs in the regular algebra with
multiplicity `dim X`. -/
theorem finrank_hom_rightFDRep [Finite G] (X : FDRep ℂ G) :
    finrank ℂ ((rightFDRep : FDRep ℂ G) ⟶ X) = finrank ℂ X := by
  classical
  haveI := Fintype.ofFinite G
  exact (homRightFDRepEquiv X).finrank_eq

/-! ## `Fun(G)` is a commutative algebra object -/

section Algebra

/-- The unit `ℂ ⟶ Fun(G)`, `c ↦ c · 1` (constant functions; `G`-equivariant). -/
def funOne [Finite G] : 𝟙_ (FDRep ℂ G) ⟶ (rightFDRep : FDRep ℂ G) where
  hom := InducedCategory.homMk (ModuleCat.ofHom (Algebra.linearMap ℂ (G → ℂ)))
  comm g := by
    ext c
    funext t
    rfl

open ModuleCat.MonModuleEquivalenceAlgebra in
/-- **The regular algebra**: `Fun(G)` with pointwise multiplication (`mulRepHom`) is a monoid
object in `Rep(G)`. -/
instance funMonObj [Finite G] : MonObj (rightFDRep : FDRep ℂ G) where
  one := funOne
  mul := mulRepHom
  one_mul := by
    apply Action.hom_ext
    apply ObjectProperty.hom_ext
    simp only [Action.comp_hom, Action.whiskerRight_hom, Action.leftUnitor_hom_hom,
      ObjectProperty.FullSubcategory.comp_hom]
    exact (inverseObj (AlgCat.of ℂ (G → ℂ))).one_mul
  mul_one := by
    apply Action.hom_ext
    apply ObjectProperty.hom_ext
    simp only [Action.comp_hom, Action.whiskerLeft_hom, Action.rightUnitor_hom_hom,
      ObjectProperty.FullSubcategory.comp_hom]
    exact (inverseObj (AlgCat.of ℂ (G → ℂ))).mul_one
  mul_assoc := by
    apply Action.hom_ext
    apply ObjectProperty.hom_ext
    simp only [Action.comp_hom, Action.whiskerRight_hom, Action.associator_hom_hom,
      Action.whiskerLeft_hom, ObjectProperty.FullSubcategory.comp_hom]
    exact (inverseObj (AlgCat.of ℂ (G → ℂ))).mul_assoc

/-- `Fun(G)` is a **commutative** algebra object. -/
instance funIsCommMonObj [Finite G] : IsCommMonObj (rightFDRep : FDRep ℂ G) where
  mul_comm := by
    apply Action.hom_ext
    apply ObjectProperty.hom_ext
    simp only [Action.comp_hom, Action.β_hom_hom, ObjectProperty.FullSubcategory.comp_hom]
    ext : 1
    apply TensorProduct.ext'
    intro f g
    change (LinearMap.mul' ℂ (G → ℂ)) (TensorProduct.comm ℂ (G → ℂ) (G → ℂ) (f ⊗ₜ g)) =
      LinearMap.mul' ℂ (G → ℂ) (f ⊗ₜ g)
    rw [TensorProduct.comm_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply, mul_comm]

/-- A `G`-map `ℂ ⟶ Fun(G)` takes `1` to a `G`-invariant function. -/
theorem unit_map_invariant [Finite G] (φ : 𝟙_ (FDRep ℂ G) ⟶ (rightFDRep : FDRep ℂ G)) (g : G) :
    rightRegular g (φ.hom (1 : ℂ)) = φ.hom (1 : ℂ) := by
  have := congr(($(φ.comm g)).hom (1 : ℂ))
  exact this.symm

/-- A `G`-invariant function is constant. -/
theorem const_of_invariant {F : G → ℂ} (h : ∀ g, rightRegular g F = F) (t : G) : F t = F 1 := by
  have := congrFun (h t) 1
  rw [rightRegular_apply, one_mul] at this
  exact this

/-- `Hom_G(ℂ, Fun(G)) ≃ ℂ`: the regular algebra is **haploid** (`φ ↦ φ(1)(e)`). -/
def homUnitFunEquiv [Finite G] : (𝟙_ (FDRep ℂ G) ⟶ (rightFDRep : FDRep ℂ G)) ≃ₗ[ℂ] ℂ where
  toFun φ := φ.hom (1 : ℂ) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := c • funOne
  left_inv φ := by
    apply Action.hom_ext
    apply ObjectProperty.hom_ext
    ext : 1
    apply LinearMap.ext_ring
    funext t
    change φ.hom (1 : ℂ) 1 * 1 = φ.hom (1 : ℂ) t
    rw [mul_one, const_of_invariant (unit_map_invariant φ) t]
  right_inv c := by
    change c * 1 = c
    rw [mul_one]

/-- `dim Hom_G(𝟙, Fun(G)) = 1`. -/
theorem finrank_hom_unit_fun [Finite G] :
    finrank ℂ (𝟙_ (FDRep ℂ G) ⟶ (rightFDRep : FDRep ℂ G)) = 1 := by
  rw [homUnitFunEquiv.finrank_eq, Module.finrank_self]

end Algebra

end VOA.Huang.Tannakian
