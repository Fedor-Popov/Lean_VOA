/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO3MonObj

/-! # O3: right exactness of `N ⊠ –` in the logarithmic category (concrete form)

`LogModuleCat W` has no cokernel (or abelian) structure in the library yet. This file proves
right exactness of `N ⊠ –` in concrete form, from the universal property of the logarithmic
tensor product (HLZ III, Prop. 4.26). Let `X →f Y →q Q` with `q` surjective and
`ker q = im f`. Then:

* `tensorMorphism_epi`: `N ⊠ q` is an epimorphism of `C`.
* `tensor_desc`: every `g : N ⊠ Y ⟶ Z` with `(N ⊠ f) ≫ g = 0` factors uniquely through
  `N ⊠ q`.

The algebraic input is `descend`: a logarithmic intertwining operator of type `(Z / N Y)` that
vanishes on `ker q` in its second slot descends to type `(Z / N Q)`.

For `N = V` (the ambient algebra) this is right exactness of the induction functor `V ⊠ –`
(McRae §2.2), in the form `induction_right_exact`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO3
open CategoryTheory VOA.LogTensor VOA.LogTensor.LogModuleCat VOA.C2Rigid.LocalInjective
open VOA.Classification.COne.McRaeM1
universe u

section Descend
variable {U M₁ MB MC M₃ : Type u} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup MB] [Module ℂ MB]
  [AddCommGroup MC] [Module ℂ MC] [AddCommGroup M₃] [Module ℂ M₃]
  {W' : VertexOperatorAlgebra U}
  {A₁ : WeakModule W' M₁} {B : WeakModule W' MB} {C : WeakModule W' MC} {A₃ : WeakModule W' M₃}
variable (q : B.Hom C) (hq : Function.Surjective q.toLinearMap)
  (Y : LogIntertwiningOperator A₁ B A₃)
  (hY : ∀ (n : ℂ) (k : ℕ) (x : M₁) (y : MB), q.toLinearMap y = 0 → Y.1 n k x y = 0)

include hY in
theorem descend_ker_le (n : ℂ) (k : ℕ) :
    LinearMap.ker q.toLinearMap ≤ LinearMap.ker (Y.1 n k).flip := by
  intro y hy
  rw [LinearMap.mem_ker] at hy ⊢
  ext x
  exact hY n k x y hy

/-- The descended mode data. -/
def descendModes : LogModes M₁ MC M₃ := fun n k =>
  (((LinearMap.ker q.toLinearMap).liftQ (Y.1 n k).flip (descend_ker_le q Y hY n k)) ∘ₗ
    (q.toLinearMap.quotKerEquivOfSurjective hq).symm.toLinearMap).flip

theorem descendModes_apply (n : ℂ) (k : ℕ) (x : M₁) (y : MB) :
    descendModes q hq Y hY n k x (q.toLinearMap y) = Y.1 n k x y := by
  have he : (q.toLinearMap.quotKerEquivOfSurjective hq).symm (q.toLinearMap y) =
      Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  change ((LinearMap.ker q.toLinearMap).liftQ (Y.1 n k).flip (descend_ker_le q Y hY n k)
    ((q.toLinearMap.quotKerEquivOfSurjective hq).symm (q.toLinearMap y))) x = _
  rw [he, Submodule.liftQ_apply]
  rfl

theorem isLogIntertwining_descend :
    IsLogIntertwining A₁ C A₃ (descendModes q hq Y hY) := by
  have hap := descendModes_apply q hq Y hY
  have hmap : ∀ (u : U) (p : ℤ) (y : MB),
      mode (C.YM u) p (q.toLinearMap y) = q.toLinearMap (mode (B.YM u) p y) :=
    fun u p y => (q.map_act u p y).symm
  refine ⟨fun x w n => ?_, fun x w n => ?_, fun x n k => ?_, fun u x w ℓ m n k => ?_⟩
  · obtain ⟨y, rfl⟩ := hq w
    obtain ⟨K, hK⟩ := Y.2.logFinite x y n
    exact ⟨K, fun k hk => by rw [hap, hK k hk]⟩
  · obtain ⟨y, rfl⟩ := hq w
    obtain ⟨N, hN⟩ := Y.2.truncation x y n
    exact ⟨N, fun m hm k => by rw [hap, hN m hm k]⟩
  · ext w
    obtain ⟨y, rfl⟩ := hq w
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hap]
    have h := congrArg (fun F => F y) (Y.2.L_neg_one x n k)
    simpa only [LinearMap.add_apply, LinearMap.smul_apply] using h
  · obtain ⟨y, rfl⟩ := hq w
    simp only [hmap, hap]
    exact Y.2.jacobi u x y ℓ m n k

/-- **Descent**: an intertwining operator vanishing on `ker q` in the second slot, as an
operator of type `(A₃ / A₁ C)`. -/
def descend : LogIntertwiningOperator A₁ C A₃ :=
  ⟨descendModes q hq Y hY, isLogIntertwining_descend q hq Y hY⟩

theorem precompose_descend :
    precompose (weakIdentity A₁) q (descend q hq Y hY) = Y := by
  apply Subtype.ext
  funext n k
  ext x y
  exact descendModes_apply q hq Y hY n k x y

include hq in
/-- Precomposition with a surjection is injective on intertwining operators. -/
theorem precompose_injective_of_surjective {Y₁ Y₂ : LogIntertwiningOperator A₁ C A₃}
    (h : precompose (weakIdentity A₁) q Y₁ = precompose (weakIdentity A₁) q Y₂) : Y₁ = Y₂ := by
  apply Subtype.ext
  funext n k
  ext x w
  obtain ⟨y, rfl⟩ := hq w
  exact congrArg (fun Z : LogIntertwiningOperator A₁ B A₃ => Z.1 n k x y) h

end Descend

section Category
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- `N ⊠ q` composed with a map is computed on intertwiners by precomposition with `q`. -/
theorem postcompose_tensorMorphism {N Y Q Z : LogModuleCat W} (q : Y ⟶ Q)
    (a : tensorObject hC2 N Q ⟶ Z) :
    postcompose (toWeakHom (tensorMorphism hC2 (𝟙 N) q ≫ a))
        (tensorIntertwiner hC2 N.act Y.act N.finiteGeneration Y.finiteGeneration) =
      precompose (weakIdentity N.act.toWeakModule) (toWeakHom q)
        (postcompose (toWeakHom a)
          (tensorIntertwiner hC2 N.act Q.act N.finiteGeneration Q.finiteGeneration)) := by
  have h := tensorMap_intertwiner hC2 N.act Y.act N.finiteGeneration Y.finiteGeneration
    N.act Q.act N.finiteGeneration Q.finiteGeneration (toWeakHom (𝟙 N)) (toWeakHom q)
  change postcompose (homComp (toWeakHom a)
    (tensorMap hC2 N.act Y.act N.finiteGeneration Y.finiteGeneration
      N.act Q.act N.finiteGeneration Q.finiteGeneration (toWeakHom (𝟙 N)) (toWeakHom q)))
    (tensorIntertwiner hC2 N.act Y.act N.finiteGeneration Y.finiteGeneration) = _
  rw [postcompose_homComp']
  exact (congrArg (postcompose (toWeakHom a)) h).trans (postcompose_precompose' _ _ _ _)

set_option maxHeartbeats 1000000 in
/-- Maps out of `N ⊠ Q` are determined after precomposition with `N ⊠ q`, `q` surjective. -/
theorem tensor_hom_ext_of_surjective {N Y Q Z : LogModuleCat W} (q : Y ⟶ Q)
    (hq : Function.Surjective q.1) {a b : tensorObject hC2 N Q ⟶ Z}
    (h : tensorMorphism hC2 (𝟙 N) q ≫ a = tensorMorphism hC2 (𝟙 N) q ≫ b) : a = b := by
  have hpre : precompose (weakIdentity N.act.toWeakModule) (toWeakHom q)
        (postcompose (toWeakHom a)
          (tensorIntertwiner hC2 N.act Q.act N.finiteGeneration Q.finiteGeneration)) =
      precompose (weakIdentity N.act.toWeakModule) (toWeakHom q)
        (postcompose (toWeakHom b)
          (tensorIntertwiner hC2 N.act Q.act N.finiteGeneration Q.finiteGeneration)) := by
    have h1 := postcompose_tensorMorphism hC2 q a
    have h2 := postcompose_tensorMorphism hC2 q b
    rw [h] at h1
    exact h1.symm.trans h2
  have hq' : Function.Surjective (toWeakHom q).toLinearMap := hq
  have hpost := precompose_injective_of_surjective (A₁ := N.act.toWeakModule)
    (B := Y.act.toWeakModule) (C := Q.act.toWeakModule) (A₃ := Z.act.toWeakModule)
    (toWeakHom q) hq' hpre
  have he := tensor_morphism_ext hC2 N.act Q.act N.finiteGeneration Q.finiteGeneration Z.act
    hpost
  apply hom_ext
  intro x
  exact congrArg (fun F => F x) he

/-- **`N ⊠ –` preserves surjections**: `N ⊠ q` is an epimorphism for surjective `q`. -/
theorem tensorMorphism_epi {N Y Q : LogModuleCat W} (q : Y ⟶ Q)
    (hq : Function.Surjective q.1) : Epi (tensorMorphism hC2 (𝟙 N) q) :=
  ⟨fun _ _ h => tensor_hom_ext_of_surjective hC2 q hq h⟩

set_option maxHeartbeats 1000000 in
/-- **Right exactness of `N ⊠ –`**: for `X →f Y →q Q` with `q` surjective and
`ker q = im f`, every `g : N ⊠ Y ⟶ Z` killing `N ⊠ f` factors uniquely through `N ⊠ q`. -/
theorem tensor_desc {N X Y Q Z : LogModuleCat W} (f : X ⟶ Y) (q : Y ⟶ Q)
    (hq : Function.Surjective q.1) (hex : LinearMap.ker q.1 = LinearMap.range f.1)
    (g : tensorObject hC2 N Y ⟶ Z) (hg : tensorMorphism hC2 (𝟙 N) f ≫ g = 0) :
    ∃! g' : tensorObject hC2 N Q ⟶ Z, tensorMorphism hC2 (𝟙 N) q ≫ g' = g := by
  let Yg := postcompose (toWeakHom g)
    (tensorIntertwiner hC2 N.act Y.act N.finiteGeneration Y.finiteGeneration)
  have hvan : ∀ (n : ℂ) (k : ℕ) (v : N) (y : Y), (toWeakHom q).toLinearMap y = 0 →
      Yg.1 n k v y = 0 := by
    intro n k v y hy
    have hy' : y ∈ LinearMap.range f.1 := by
      rw [← hex]
      exact hy
    obtain ⟨x, rfl⟩ := hy'
    have h := postcompose_tensorMorphism hC2 f g
    have h0 := congrArg (fun Z' : LogIntertwiningOperator N.act.toWeakModule X.act.toWeakModule
      Z.act.toWeakModule => Z'.1 n k v x) h
    simp only [hg] at h0
    exact h0.symm
  let Yq := descend (toWeakHom q) hq Yg hvan
  let g' : tensorObject hC2 N Q ⟶ Z :=
    fromWeakHom (tensorFactor hC2 N.act Q.act N.finiteGeneration Q.finiteGeneration Z.act Yq)
  have hg' : tensorMorphism hC2 (𝟙 N) q ≫ g' = g := by
    apply hom_ext
    intro x
    have he := tensor_morphism_ext hC2 N.act Y.act N.finiteGeneration Y.finiteGeneration Z.act
      (f := toWeakHom (tensorMorphism hC2 (𝟙 N) q ≫ g')) (g := toWeakHom g) (by
        refine (postcompose_tensorMorphism hC2 q g').trans ?_
        have hf := tensorFactor_comp_intertwiner hC2 N.act Q.act N.finiteGeneration
          Q.finiteGeneration Z.act Yq
        refine (congrArg (precompose _ _) hf).trans ?_
        exact precompose_descend (toWeakHom q) hq Yg hvan)
    exact congrArg (fun F => F x) he
  refine ⟨g', hg', fun g'' h'' => ?_⟩
  exact tensor_hom_ext_of_surjective hC2 q hq (h''.trans hg'.symm)

end Category

/-! ## The induction functor `V ⊠ –` -/

section Induction
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
  (hC2 : C2Cofinite (orbifoldVOA G))

/-- **Right exactness of induction** `V ⊠ –` on `C = LogModuleCat (W^G)` (concrete form):
`V ⊠ q` is epi, and maps killing `V ⊠ f` factor uniquely through `V ⊠ q`. -/
theorem induction_right_exact {X Y Q : LogModuleCat (orbifoldVOA G)} (f : X ⟶ Y) (q : Y ⟶ Q)
    (hq : Function.Surjective q.1) (hex : LinearMap.ker q.1 = LinearMap.range f.1) :
    Epi (tensorMorphism hC2 (𝟙 (vObj G hfg)) q) ∧
      ∀ (Z : LogModuleCat (orbifoldVOA G)) (g : tensorObject hC2 (vObj G hfg) Y ⟶ Z),
        tensorMorphism hC2 (𝟙 (vObj G hfg)) f ≫ g = 0 →
          ∃! g' : tensorObject hC2 (vObj G hfg) Q ⟶ Z,
            tensorMorphism hC2 (𝟙 (vObj G hfg)) q ≫ g' = g :=
  ⟨tensorMorphism_epi hC2 q hq, fun _ g hg => tensor_desc hC2 f q hq hex g hg⟩

end Induction

end VOA.Classification.COne.McRaeO3
