/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangModularityQDim

/-!
# HKL extensions: the extension property must require a NONDEGENERATE algebra

## `HKLExtensionProperty` (hence `HKLRepInput`) is FALSE as stated

`HuangRibbonRealization.HKLExtensionProperty H` asks, for **every** commutative haploid algebra
`A` with `θ_A = 𝟙` and every finite group `G` of algebra automorphisms whose average factors
through the unit, for a nice `W` with `V ≅ W^Γ` and `dim W_n = Σ_i dim Hom(A, X_i) dim (V_i)_n`.
Haploid + commutative + trivial twist does **not** make `A` an étale (separable) algebra, and the
property fails on the **square-zero extension**:

* Let `V = L_{sl₂}(10, 0)` (nice: unitary, strongly rational, pseudo-unitary) and `M = L(10, 6)`,
  `h_M = 6·8/(4·12) = 1 ∈ ℤ`, so `θ_M = 1`; `M` is not a simple current
  (`d_M = sin(7π/12)/sin(π/12) = 2 + √3`).
* `A = 𝟙 ⊕ M` with multiplication `λ ⊕ λ_M ⊕ ρ_M ⊕ 0` (zero on `M ⊗ M`) and unit the inclusion is
  a commutative monoid object in any braided additive monoidal category (`β_{M,𝟙} ≫ λ = ρ`);
  `Hom(𝟙, A) = ℂ` (haploid), `θ_A = 1 ⊕ e^{2πi} = 𝟙`.
* `G = ℤ/2` acting by `1 ⊕ (−1)` (an algebra automorphism: the product is square-zero), and
  `Σ_g ρ(g) = 2·(1 ⊕ 0) = (2 π_𝟙) ≫ ι_𝟙` factors through the unit.
* The conclusion would give a nice (in particular simple) `W` with `V ≅ W^Γ`, `Γ` finite, and
  `ch W = ch V + ch M`.  By Dong–Li–Mason Schur–Weyl duality `W = ⊕_χ W_χ ⊗ χ` with every
  `χ ∈ Irr Γ` occurring and the `W_χ` irreducible and pairwise inequivalent; linear independence
  of the characters of `L_{sl₂}(10)` forces exactly one nontrivial `χ`, one-dimensional, with
  `W_χ ≅ M`, so `Γ ≅ ℤ/2` and `M` would be a simple current (`ℤ/2`-orbifold; equivalently
  Dong–Jiao–Xu: `qdim_{W^Γ} W_χ = dim χ = 1`) — but `d_M = 2 + √3`.  Contradiction.

Through `huangRepInput_holds` (a realization pinned to `Rep V` exists), the object `𝟙 ⊕ M` and its
algebra structure exist in `H.C`, so `HKLRepInput` (which demands `HKLExtensionProperty` for every
pinned realization of every nice `V`) is **mathematically false**.  It must not be assumed.

The consumer `iTannakian_of_inputs` only ever applies the property to the **regular algebra**
`A = Φ⁻¹(Fun G)`, which is far from square-zero: its pairing `A ⊗ A → A → 𝟙` (product followed by
the averaging counit `q`) is nondegenerate — `Fun(G)` is a Frobenius algebra.

## The repair (this file)

* `IsFrobeniusCounit A q` — the pairing `μ ≫ q` has a copairing `c : 𝟙 → A ⊗ A` satisfying the
  zig-zag identity.  This is the Kirillov–Ostrik *rigidity* (nondegeneracy) of a haploid algebra
  (KO 2002, Def. 1.11 / Thm. 1.15: rigid haploid commutative algebras with `dim A ≠ 0` are
  separable, `Rep A` semisimple); it excludes the square-zero example
  (`ker_trivial_of_isFrobeniusCounit`: the right kernel of the pairing vanishes, while `M` lies in
  the kernel of the square-zero pairing).
* `HKLExtensionPropertyRigid H` — the extension property with this extra hypothesis and the
  averaging counit `q` named.  It is implied by the old property
  (`hklExtensionPropertyRigid_of_hklExtensionProperty`) and, unlike it, is TRUE for realizations
  pinned to `Rep V` (HKL 2015 Thm 3.2/3.4 + KO 2002 + CKM 2017 + GR Prop. 2.7).
* `HKLRepInputRigid`, `HuangHKLInterfaceRigid`, `huangHKLInterfaceRigid_of_hklRepRigid`.
* `iTannakian_of_rigid : DeligneTannakian → HuangHKLInterfaceRigid → ITannakian` — the
  consumer re-proved; the new obligation (the regular algebra is Frobenius) is discharged by
  `funCopair_zigzag` (`Σ_x δ_x ⊗ δ_x` in `Rep G`) transported along the monoidal functor
  `Φ⁻¹ ⋙ ι` (`zigzag_map`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLExt

open CategoryTheory MonoidalCategory Limits Module Complex
open Functor.LaxMonoidal Functor.OplaxMonoidal
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.Tannakian
open VOA.Huang.TensorCat.BraidRibbon

universe u v w

/-! ## Frobenius (nondegenerate) counits -/

section Frobenius

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **The pairing `μ ≫ q` of an algebra is nondegenerate (Frobenius / KO-rigid).**  There is a
copairing `c : 𝟙 → A ⊗ A` with `(λ⁻¹) ≫ (c ▷ A) ≫ α ≫ (A ◁ (μ ≫ q)) ≫ ρ = 𝟙_A`. -/
def IsFrobeniusCounit (A : C) [MonObj A] (q : A ⟶ 𝟙_ C) : Prop :=
  ∃ c : 𝟙_ C ⟶ A ⊗ A,
    (λ_ A).inv ≫ (c ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ (MonObj.mul ≫ q)) ≫ (ρ_ A).hom = 𝟙 A

/-- The zig-zag identity of a pairing is transported by any monoidal functor. -/
theorem zigzag_map {D : Type*} [Category D] [MonoidalCategory D] (Ψ : C ⥤ D) [Ψ.Monoidal]
    {A : C} (c : 𝟙_ C ⟶ A ⊗ A) (p : A ⊗ A ⟶ 𝟙_ C)
    (h : (λ_ A).inv ≫ (c ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ p) ≫ (ρ_ A).hom = 𝟙 A) :
    (λ_ (Ψ.obj A)).inv ≫ ((ε Ψ ≫ Ψ.map c ≫ δ Ψ A A) ▷ Ψ.obj A) ≫ (α_ _ _ _).hom ≫
      (Ψ.obj A ◁ (μ Ψ A A ≫ Ψ.map p ≫ η Ψ)) ≫ (ρ_ _).hom = 𝟙 _ := by
  have h' := congrArg Ψ.map h
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_leftUnitor_inv, Functor.Monoidal.map_rightUnitor, Category.assoc,
    Functor.Monoidal.μ_δ_assoc] at h'
  rw [CategoryTheory.Functor.map_id] at h'
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  exact h'

/-- **Nondegeneracy**: for a Frobenius counit the right kernel of the pairing `μ ≫ q` is zero.
(The square-zero algebra `𝟙 ⊕ M` violates this: `M ↪ A` pairs to zero with everything.) -/
theorem ker_trivial_of_isFrobeniusCounit [Preadditive C] [MonoidalPreadditive C]
    {A : C} [MonObj A] {q : A ⟶ 𝟙_ C} (hA : IsFrobeniusCounit A q)
    {X : C} (f : X ⟶ A) (hf : (A ◁ f) ≫ MonObj.mul ≫ q = 0) : f = 0 := by
  obtain ⟨c, hc⟩ := hA
  have key : f = (λ_ X).inv ≫ (c ▷ X) ≫ (α_ A A X).hom ≫ (A ◁ ((A ◁ f) ≫ MonObj.mul ≫ q)) ≫
      (ρ_ A).hom := by
    calc f = f ≫ 𝟙 A := (Category.comp_id f).symm
      _ = f ≫ (λ_ A).inv ≫ (c ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ (MonObj.mul ≫ q)) ≫
          (ρ_ A).hom := by rw [hc]
      _ = _ := by
        simp only [whiskerLeft_comp, Category.assoc]
        rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
          ← leftUnitor_inv_naturality_assoc]
  rw [key, hf, MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero, comp_zero, comp_zero]

end Frobenius

end VOA.Huang.HKLExt

/-! ## The repaired extension property and interfaces -/

namespace VOA.Huang.Tannakian.HuangRibbonRealization

open CategoryTheory MonoidalCategory Module VOA VOA.Classification.COne VOA.Huang.HKLExt

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : VOA.Classification.COne.ModularData V}

/-- **The extension property for nondegenerate algebras** (HKL 2015 + Kirillov–Ostrik 2002 +
CKM + GR Prop. 2.7): a commutative haploid algebra with trivial twist, a finite group of algebra
automorphisms whose average is `q ≫ η` (so `A^G = 𝟙`), and **`q` a Frobenius counit** (the pairing
`μ ≫ q` nondegenerate: KO-rigid) give a nice conformal extension `W` with `V ≅ W^Γ` and
`W ≅ ⊕_i Hom(A, X_i) ⊗ V_{lab i}` as graded spaces.  Identical to
`HKLExtensionProperty` except for the Frobenius hypothesis, without which it is false (module
docstring). -/
def HKLExtensionPropertyRigid (H : HuangRibbonRealization.{u, v, w} V D) : Prop :=
  ∀ (A : H.C) [MonObj A], IsCommMonObj A → (H.R.twist A).hom = 𝟙 A →
    finrank ℂ (𝟙_ H.C ⟶ A) = 1 →
    ∀ (G : Type) [Group G] [Fintype G] (ρ : G →* CategoryTheory.Aut A), (∀ g, IsMonHom (ρ g).hom) →
    ∀ q : A ⟶ 𝟙_ H.C, ∑ g, (ρ g).hom = q ≫ MonObj.one → IsFrobeniusCounit A q →
    ∃ (𝒲 : Type u) (_ : AddCommGroup 𝒲) (_ : Module ℂ 𝒲) (W : VertexOperatorAlgebra 𝒲)
      (Γ : Subgroup (Aut W)), Nice W ∧ Finite Γ ∧ W.centralCharge = V.centralCharge ∧
      VOAIsomorphic V (orbifoldVOA Γ) ∧
      ∀ n : ℕ, (finrank ℂ (W.grading n) : ℝ) =
        ∑ i, (finrank ℂ (A ⟶ H.fusion.simple i) : ℝ) *
          (finrank ℂ ((D.module (H.lab i)).weight (n : ℂ)) : ℝ)

/-- The repaired property is weaker than the original one. -/
theorem hklExtensionPropertyRigid_of_hklExtensionProperty
    (H : HuangRibbonRealization.{u, v, w} V D) (h : H.HKLExtensionProperty) :
    H.HKLExtensionPropertyRigid := by
  intro A _ hc ht hh G _ _ ρ hρ q hq _
  exact h A hc ht hh G ρ hρ ⟨q, hq⟩

end VOA.Huang.Tannakian.HuangRibbonRealization

namespace VOA.Huang.HKLExt

open CategoryTheory MonoidalCategory Limits Module Complex
open Functor.LaxMonoidal Functor.OplaxMonoidal
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.Tannakian
open VOA.Huang.TensorCat.BraidRibbon

universe u v w

/-- **The repaired Huang–HKL interface**: every nice `V` with modular data has a ribbon realization
on which the (nondegenerate) HKL extension property holds. -/
def HuangHKLInterfaceRigid : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData →
      ∃ H : Tannakian.HuangRibbonRealization.{u, v, w} V D, H.HKLExtensionPropertyRigid

/-- **HKL on `Rep V`, repaired**: every realization pinned to `Rep V` has the extension property
for nondegenerate (Frobenius) algebras.  TRUE (HKL 2015, KO 2002, CKM 2017, GR Prop. 2.7); compare
`HKLRepInput`, which is false (module docstring). -/
def HKLRepInputRigid : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData →
      ∀ H : Tannakian.HuangRibbonRealization.{u, 0, 0} V D, IsRepRealization H →
        H.HKLExtensionPropertyRigid

/-- The repaired input is implied by the old one (so nothing provable was lost). -/
theorem hklRepInputRigid_of_hklRepInput (h : HKLRepInput.{u}) : HKLRepInputRigid.{u} :=
  fun 𝒱 _ _ V hV D hD H hH =>
    HuangRibbonRealization.hklExtensionPropertyRigid_of_hklExtensionProperty H
      (h 𝒱 V hV D hD H hH)

/-- **The repaired interface from the repaired HKL input**, with Huang's half proved
(`huangRepInput_holds`). -/
theorem huangHKLInterfaceRigid_of_hklRepRigid (h : HKLRepInputRigid.{u}) :
    HuangHKLInterfaceRigid.{u, 0, 0} := by
  intro 𝒱 _ _ V hV D hD
  obtain ⟨H, hH⟩ := VOA.Huang.HuangModularity.huangRepInput_holds 𝒱 V hV D hD
  exact ⟨H, h 𝒱 V hV D hD H hH⟩

/-! ## The regular algebra `Fun(G)` is Frobenius -/

section Regular

open TannakaDuality.FiniteGroup

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- The copairing vector `Σ_x δ_x ⊗ δ_x ∈ Fun(G) ⊗ Fun(G)`. -/
def copairVec : TensorProduct ℂ (G → ℂ) (G → ℂ) :=
  ∑ x : G, (Pi.single x (1 : ℂ) : G → ℂ) ⊗ₜ (Pi.single x (1 : ℂ) : G → ℂ)

/-- `Σ_x δ_x ⊗ δ_x` is invariant under the diagonal right regular action. -/
theorem copairVec_invariant (h : G) :
    TensorProduct.map (rightRegular (k := ℂ) h) (rightRegular (k := ℂ) h) copairVec =
      copairVec := by
  unfold copairVec
  rw [map_sum]
  simp only [TensorProduct.map_tmul]
  have : ∀ x : G, (rightRegular (k := ℂ) h (Pi.single x 1 : G → ℂ)) = Pi.single (x * h⁻¹) 1 := by
    intro x; funext t; simp [rightRegular_apply, Pi.single_apply, eq_mul_inv_iff_mul_eq]
  simp_rw [this]
  exact Fintype.sum_equiv (Equiv.mulRight h⁻¹) _ _ (fun _ => rfl)

/-- The copairing `ℂ ⟶ Fun(G) ⊗ Fun(G)`, `1 ↦ Σ_x δ_x ⊗ δ_x`, a map in `Rep G`. -/
def funCopair : 𝟙_ (FDRep ℂ G) ⟶ (rightFDRep : FDRep ℂ G) ⊗ rightFDRep where
  hom := InducedCategory.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton ℂ _ copairVec))
  comm h := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rw [Action.tensorUnit_ρ, Action.tensor_ρ]
    change (1 : ℂ) • copairVec =
      TensorProduct.map (rightRegular (k := ℂ) h) (rightRegular (k := ℂ) h) ((1 : ℂ) • copairVec)
    rw [one_smul, copairVec_invariant]

/-- **`Fun(G)` is a Frobenius algebra** with counit `Σ_x ev_x`: the zig-zag identity
`f = Σ_x f(x) δ_x` in `Rep G`. -/
theorem funCopair_zigzag :
    (λ_ (rightFDRep : FDRep ℂ G)).inv ≫ (funCopair ▷ rightFDRep) ≫
      (α_ (rightFDRep : FDRep ℂ G) rightFDRep rightFDRep).hom ≫
      ((rightFDRep : FDRep ℂ G) ◁ (MonObj.mul ≫ funSum)) ≫ (ρ_ (rightFDRep : FDRep ℂ G)).hom =
      𝟙 _ := by
  apply Action.hom_ext
  apply ObjectProperty.hom_ext
  simp only [Action.comp_hom, Action.whiskerRight_hom, Action.leftUnitor_inv_hom,
    Action.associator_hom_hom, Action.whiskerLeft_hom, Action.rightUnitor_hom_hom,
    ObjectProperty.FullSubcategory.comp_hom, Action.id_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (ConcreteCategory.hom (ρ_ (ModuleCat.of ℂ (G → ℂ))).hom)
    ((ConcreteCategory.hom ((ModuleCat.of ℂ (G → ℂ)) ◁
      (ModuleCat.ofHom ((LinearMap.mul' ℂ (G → ℂ)).comp (LinearMap.id)) ≫ funSum.hom.hom)))
    ((ConcreteCategory.hom (α_ (ModuleCat.of ℂ (G → ℂ)) (ModuleCat.of ℂ (G → ℂ))
      (ModuleCat.of ℂ (G → ℂ))).hom)
    ((ConcreteCategory.hom ((ModuleCat.ofHom (LinearMap.toSpanSingleton ℂ _ copairVec)) ▷
      (ModuleCat.of ℂ (G → ℂ))))
    ((ConcreteCategory.hom (λ_ (ModuleCat.of ℂ (G → ℂ))).inv) f)))) = f
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul, copairVec,
    TensorProduct.sum_tmul, map_sum]
  have hf : f = ∑ x : G, f x • (Pi.single x (1 : ℂ) : G → ℂ) := by
    funext t; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hf]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 := ModuleCat.MonoidalCategory.associator_hom_apply (R := ℂ)
    (M := ModuleCat.of ℂ (G → ℂ)) (N := ModuleCat.of ℂ (G → ℂ)) (K := ModuleCat.of ℂ (G → ℂ))
    (Pi.single x 1 : G → ℂ) (Pi.single x 1 : G → ℂ) f
  rw [h1]
  have h2 := ModuleCat.MonoidalCategory.whiskerLeft_apply (ModuleCat.of ℂ (G → ℂ))
    (ModuleCat.ofHom (LinearMap.mul' ℂ (G → ℂ) ∘ₗ LinearMap.id) ≫ funSum.hom.hom)
    (Pi.single x 1 : G → ℂ) ((Pi.single x 1 : G → ℂ) ⊗ₜ[ℂ] f)
  rw [h2]
  have h3 := ModuleCat.MonoidalCategory.rightUnitor_hom_apply (M := ModuleCat.of ℂ (G → ℂ))
    (Pi.single x 1 : G → ℂ)
    ((ConcreteCategory.hom (ModuleCat.ofHom (LinearMap.mul' ℂ (G → ℂ) ∘ₗ LinearMap.id) ≫
      funSum.hom.hom)) ((Pi.single x 1 : G → ℂ) ⊗ₜ[ℂ] f))
  rw [h3]
  congr 1
  change ∑ t, (Pi.single x (1 : ℂ) : G → ℂ) t * f t = f x
  simp [Pi.single_apply]

end Regular

/-! ## The consumer, re-proved from the repaired interface -/

/-- **`ITannakian` from Deligne and the repaired Huang–HKL interface.**  The proof of
`iTannakian_of_inputs`, with the one new obligation — the regular algebra `A = Φ⁻¹(Fun G)` has a
Frobenius counit `q = Ψ(Σ_x ev_x) ≫ η` — discharged by `funCopair_zigzag` and `zigzag_map`. -/
theorem iTannakian_of_rigid (hDel : DeligneTannakian.{v, w})
    (hHK : HuangHKLInterfaceRigid.{u, v, w}) : ITannakian.{u} := by
  intro 𝒱 _ _ V hV D hD hfact
  obtain ⟨H, hHKL⟩ := hHK 𝒱 V hV D hD
  set U := H.pseudoUnitaryData hD
  have hS := H.sTilde_eq_of_factorized hD hfact
  letI := isMonoidal_trivialTwist_of_factorized U hS
  letI := symmetricTrivialTwist_of_factorized U hS
  obtain ⟨G, hG, hGf, Φ, ⟨hbr⟩, hlin, heq, hdim⟩ := tannakian_dims_of_factorized hDel U hS H.symDim_eq
  letI := hbr
  let e := Φ.asEquivalence
  letI : e.functor.Braided := hbr
  letI : e.inverse.Braided := Equivalence.inverseBraided e
  let Fun : FDRep ℂ G := TannakaDuality.FiniteGroup.rightFDRep
  haveI : HasBinaryBiproducts (TT H.R) := hasBinaryBiproducts_of_finite_biproducts _
  haveI : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  haveI : e.functor.Additive := (inferInstance : Φ.Additive)
  let Ψ : FDRep ℂ G ⥤ H.C := e.inverse ⋙ (trivialTwist H.R).ι
  haveI : Ψ.Additive := inferInstanceAs (e.inverse ⋙ (trivialTwist H.R).ι).Additive
  letI : MonObj (Ψ.obj Fun) := Functor.monObjObj Fun
  have hcomm : IsCommMonObj (Ψ.obj Fun) := Functor.isCommMonObj_obj
  have htw : (H.R.twist (Ψ.obj Fun)).hom = 𝟙 _ := (e.inverse.obj Fun).2
  -- haploid
  have hhap : finrank ℂ (𝟙_ H.C ⟶ Ψ.obj Fun) = 1 := by
    have h1 : finrank ℂ (𝟙_ (TT H.R) ⟶ e.inverse.obj Fun) = 1 := by
      rw [(homLinearEquivOfFullyFaithful Φ _ _).finrank_eq]
      exact (Linear.homCongr ℂ (Functor.Monoidal.εIso Φ).symm (e.counitIso.app Fun)).finrank_eq.trans
        VOA.Huang.Tannakian.finrank_hom_unit_fun
    rw [← h1, (homLinearEquivOfFullyFaithful (trivialTwist H.R).ι _ _).finrank_eq]
    rfl
  -- the group action
  let ρ : G →* CategoryTheory.Aut (Ψ.obj Fun) := (Ψ.mapAut Fun).comp leftTransl
  have hρ : ∀ g, IsMonHom (ρ g).hom := fun g => by
    change IsMonHom (Ψ.map (leftTranslHom g))
    infer_instance
  let q : Ψ.obj Fun ⟶ 𝟙_ H.C := Ψ.map funSum ≫ (Functor.Monoidal.εIso Ψ).inv
  have havg : ∑ g, (ρ g).hom = q ≫ MonObj.one := by
    change ∑ g, Ψ.map (leftTranslHom g) = _
    rw [← Functor.map_sum, sum_leftTranslHom, Functor.map_comp]
    change _ = (Ψ.map funSum ≫ (Functor.Monoidal.εIso Ψ).inv) ≫ (Functor.LaxMonoidal.ε Ψ ≫ Ψ.map MonObj.one)
    simp
  -- the regular algebra is Frobenius
  have hfrob : IsFrobeniusCounit (Ψ.obj Fun) q := by
    classical
    refine ⟨ε Ψ ≫ Ψ.map funCopair ≫ δ Ψ Fun Fun, ?_⟩
    have hz := zigzag_map Ψ funCopair (MonObj.mul ≫ funSum) funCopair_zigzag
    have hp : (MonObj.mul : Ψ.obj Fun ⊗ Ψ.obj Fun ⟶ Ψ.obj Fun) ≫ q =
        μ Ψ Fun Fun ≫ Ψ.map (MonObj.mul ≫ funSum) ≫ η Ψ := by
      change (μ Ψ Fun Fun ≫ Ψ.map MonObj.mul) ≫ Ψ.map funSum ≫ η Ψ = _
      rw [Functor.map_comp]
      simp only [Category.assoc]
    rw [hp]
    exact hz
  obtain ⟨𝒲, i1, i2, W, Γ, hW, hΓ, hc, hiso, hdW⟩ :=
    hHKL (Ψ.obj Fun) hcomm htw hhap G ρ hρ q havg hfrob
  refine ⟨𝒲, i1, i2, W, Γ, hW, hΓ, hc, hiso, fun n => ?_⟩
  rw [hdW n]
  have hmult : ∀ i, (finrank ℂ (Ψ.obj Fun ⟶ H.fusion.simple i) : ℝ) =
      if D.IsIntWeight (H.lab i) then D.d (H.lab i) else 0 := by
    intro i
    split_ifs with hint
    · have hi : H.R.T i = 1 := (H.T_eq_one_iff i).mpr hint
      have h0 : finrank ℂ (Ψ.obj Fun ⟶ H.fusion.simple i) =
          finrank ℂ (e.inverse.obj Fun ⟶ ttSimple H.R ⟨i, hi⟩) :=
        ((homLinearEquivOfFullyFaithful (trivialTwist H.R).ι (e.inverse.obj Fun)
          (ttSimple H.R ⟨i, hi⟩)).finrank_eq).symm
      have hC : (finrank ℂ (e.inverse.obj Fun ⟶ ttSimple H.R ⟨i, hi⟩) : ℂ) = U.d i := by
        rw [(homLinearEquivOfFullyFaithful Φ _ _).finrank_eq]
        have h := (Linear.homCongr ℂ (e.counitIso.app Fun)
          (Iso.refl (Φ.obj (ttSimple H.R ⟨i, hi⟩)))).finrank_eq
        change _ = finrank ℂ (Fun ⟶ Φ.obj (ttSimple H.R ⟨i, hi⟩)) at h
        rw [VOA.Huang.Tannakian.finrank_hom_rightFDRep] at h
        change (finrank ℂ ((e.inverse ⋙ e.functor).obj Fun ⟶ Φ.obj (ttSimple H.R ⟨i, hi⟩)) : ℂ) = _
        rw [h, (hdim i hi).1]
      rw [h0]
      exact_mod_cast hC
    · have hi : H.R.T i ≠ 1 := fun h => hint ((H.T_eq_one_iff i).mp h)
      haveI : Subsingleton (Ψ.obj Fun ⟶ H.fusion.simple i) :=
        ⟨fun f g => by
          rw [hom_simple_eq_zero_of_twist H.R htw i hi f, hom_simple_eq_zero_of_twist H.R htw i hi g]⟩
      rw [finrank_zero_of_subsingleton]
      simp
  simp_rw [hmult, ite_mul, zero_mul]
  rw [VOA.Classification.COne.ModularData.intLabels, Finset.sum_filter]
  exact Fintype.sum_equiv H.lab _ _ (fun _ => rfl)

end VOA.Huang.HKLExt
