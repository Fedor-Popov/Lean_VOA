/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberSym

/-!
# Deligne's fiber functor — tensoring a commutative algebra of `Ind(D)` with a graded
commutative monoid

For a lax braided `G : C ⥤ ModuleCat ℂ` (a commutative algebra `A` of `Ind(C)`) and a graded
commutative monoid `B = (B_k)` of `C` (`GCMon`), the lax braided functor
`tensorG G B : Y ↦ ⨁_k G(B_k ⊗ Y)` encodes the commutative algebra `A ⊗ (⨁_k B_k)` of `Ind(C)`.
For `B = Sym X` (`symGCMon`) this is the **free extension** `A[X^∨]` used by the Gram–Schmidt step.

* D-level coherence `Φ_natural_left/right`, `Φ_assoc`, `Φ_unit_left/right`, `Φ_braid`
  (`Φ = tensorμ ≫ (m ▷ _)`), from Mathlib's `tensor_associativity`, `tensor_left_unitality`,
  `tensor_right_unitality` and the symmetric identity `tensorμ_braiding`;
* `tensorG G B` with `LaxMonoidal`, `LaxBraided`, `Additive`, `Linear` instances;
* the inclusion `inclG : G Y → tensorG G B Y` (degree `0`), multiplicative and natural.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal Cardinal
open scoped TensorProduct DirectSum

universe v u

section TensorMuBraid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- In a symmetric category the tensor functor is braided:
`tensorμ ≫ (β ⊗ β) = β ≫ tensorμ`. -/
theorem tensorμ_braiding (A Y B Z : C) :
    tensorμ A Y B Z ≫ ((β_ A B).hom ⊗ₘ (β_ Y Z).hom) = (β_ (A ⊗ Y) (B ⊗ Z)).hom ≫ tensorμ B Z A Y := by
  calc tensorμ A Y B Z ≫ ((β_ A B).hom ⊗ₘ (β_ Y Z).hom)
      = 𝟙 _ ⊗≫ (A ◁ (β_ Y B).hom ▷ Z) ⊗≫ ((β_ A B).hom ▷ (Y ⊗ Z) ≫ (B ⊗ A) ◁ (β_ Y Z).hom) ⊗≫ 𝟙 _ := by
        simp only [tensorμ, tensorHom_def]
        monoidal
    _ = 𝟙 _ ⊗≫ (A ◁ (β_ Y B).hom ▷ Z) ⊗≫ ((β_ A B).hom ▷ Y ▷ Z) ⊗≫ (B ◁ A ◁ (β_ Y Z).hom) ⊗≫
          (B ◁ ((β_ A Z).hom ≫ (β_ Z A).hom) ▷ Y) ⊗≫ 𝟙 _ := by
        rw [SymmetricCategory.symmetry]
        monoidal
    _ = _ := by
        simp only [tensorμ, BraidedCategory.braiding_tensor_left_hom,
          BraidedCategory.braiding_tensor_right_hom, comp_whiskerRight, whiskerLeft_comp]
        monoidal

end TensorMuBraid

namespace GCMon

section Phi

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] (B : GCMon C)

/-- The index transport `B a ⟶ B b` for `a = b`. -/
def castB {a b : ℕ} (h : a = b) : B.B a ⟶ B.B b := eqToHom (congrArg B.B h)

/-- `Φ = tensorμ ≫ (m ▷ _) : (B_a ⊗ Y) ⊗ (B_b ⊗ Z) ⟶ B_{a+b} ⊗ (Y ⊗ Z)`. -/
def Φ (a b : ℕ) (Y Z : C) : (B.B a ⊗ Y) ⊗ (B.B b ⊗ Z) ⟶ B.B (a + b) ⊗ (Y ⊗ Z) :=
  tensorμ (B.B a) Y (B.B b) Z ≫ (B.m a b ▷ (Y ⊗ Z))

/-- The degree-`0` inclusion `Y ⟶ B_0 ⊗ Y`. -/
def ι0 (Y : C) : Y ⟶ B.B 0 ⊗ Y := (λ_ Y).inv ≫ (B.u ▷ Y)

theorem Φ_natural_left (a b : ℕ) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    ((B.B a ◁ f) ▷ (B.B b ⊗ Z)) ≫ B.Φ a b Y' Z = B.Φ a b Y Z ≫ (B.B (a + b) ◁ (f ▷ Z)) := by
  have h := tensorμ_natural_left (𝟙 (B.B a)) f (B.B b) Z
  rw [id_tensorHom, id_whiskerRight, id_tensorHom] at h
  rw [Φ, Φ, reassoc_of% h, whisker_exchange, Category.assoc]

theorem Φ_natural_right (a b : ℕ) (Y : C) {Z Z' : C} (g : Z ⟶ Z') :
    ((B.B a ⊗ Y) ◁ (B.B b ◁ g)) ≫ B.Φ a b Y Z' = B.Φ a b Y Z ≫ (B.B (a + b) ◁ (Y ◁ g)) := by
  have h := tensorμ_natural_right (B.B a) Y (𝟙 (B.B b)) g
  rw [id_tensorHom, MonoidalCategory.whiskerLeft_id, id_tensorHom] at h
  rw [Φ, Φ, reassoc_of% h, whisker_exchange, Category.assoc]

theorem Φ_assoc (a b c : ℕ) (Y Z W : C) :
    (B.Φ a b Y Z ▷ (B.B c ⊗ W)) ≫ B.Φ (a + b) c (Y ⊗ Z) W ≫ (B.B (a + b + c) ◁ (α_ Y Z W).hom) ≫
        (B.castB (Nat.add_assoc a b c) ▷ (Y ⊗ (Z ⊗ W))) =
      (α_ _ _ _).hom ≫ ((B.B a ⊗ Y) ◁ B.Φ b c Z W) ≫ B.Φ a (b + c) Y (Z ⊗ W) := by
  have hA := tensor_associativity (B.B a) Y (B.B b) Z (B.B c) W
  have hL := tensorμ_natural_left (B.m a b) (𝟙 (Y ⊗ Z)) (B.B c) W
  have hR := tensorμ_natural_right (B.B a) Y (B.m b c) (𝟙 (Z ⊗ W))
  rw [tensorHom_id] at hL hR
  rw [MonoidalCategory.whiskerLeft_id, tensorHom_id] at hR
  rw [id_whiskerRight, tensorHom_id] at hL
  have hm := B.assoc a b c
  simp only [Φ, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hL]
  calc tensorμ (B.B a) Y (B.B b) Z ▷ (B.B c ⊗ W) ≫ tensorμ (B.B a ⊗ B.B b) (Y ⊗ Z) (B.B c) W ≫
        (B.m a b ▷ B.B c) ▷ ((Y ⊗ Z) ⊗ W) ≫ B.m (a + b) c ▷ ((Y ⊗ Z) ⊗ W) ≫
          B.B (a + b + c) ◁ (α_ Y Z W).hom ≫ B.castB (Nat.add_assoc a b c) ▷ (Y ⊗ Z ⊗ W)
      = tensorμ (B.B a) Y (B.B b) Z ▷ (B.B c ⊗ W) ≫ tensorμ (B.B a ⊗ B.B b) (Y ⊗ Z) (B.B c) W ≫
          ((α_ _ _ _).hom ⊗ₘ (α_ Y Z W).hom) ≫ ((B.B a ◁ B.m b c) ≫ B.m a (b + c)) ▷ (Y ⊗ Z ⊗ W) := by
        congr 2
        rw [tensorHom_comp_whiskerRight, ← Category.assoc, ← Category.assoc, ← hm, tensorHom_def]
        simp only [castB, comp_whiskerRight, Category.assoc]
        rw [whisker_exchange]
    _ = _ := by
        rw [reassoc_of% hA, comp_whiskerRight, reassoc_of% hR]

theorem Φ_unit_left (b : ℕ) (Y : C) :
    (λ_ (B.B b ⊗ Y)).inv ≫ (B.ι0 (𝟙_ C) ▷ (B.B b ⊗ Y)) ≫ B.Φ 0 b (𝟙_ C) Y ≫
        (B.B (0 + b) ◁ (λ_ Y).hom) ≫ (B.castB (Nat.zero_add b) ▷ Y) = 𝟙 _ := by
  have hU := tensor_left_unitality (B.B b) Y
  have hU' : (λ_ (B.B b ⊗ Y)).inv ≫ (λ_ (𝟙_ C)).inv ▷ (B.B b ⊗ Y) ≫ tensorμ (𝟙_ C) (𝟙_ C) (B.B b) Y =
      ((λ_ (B.B b)).inv ⊗ₘ (λ_ Y).inv) := by
    rw [← cancel_mono ((λ_ (B.B b)).hom ⊗ₘ (λ_ Y).hom)]
    simp only [Category.assoc, ← hU, Iso.inv_hom_id, tensorHom_comp_tensorHom, id_tensorHom_id]
  have hN := tensorμ_natural_left B.u (𝟙 (𝟙_ C)) (B.B b) Y
  rw [tensorHom_id, id_whiskerRight, tensorHom_id] at hN
  have hm := B.unit_left b
  calc (λ_ (B.B b ⊗ Y)).inv ≫ (B.ι0 (𝟙_ C) ▷ (B.B b ⊗ Y)) ≫ B.Φ 0 b (𝟙_ C) Y ≫
        (B.B (0 + b) ◁ (λ_ Y).hom) ≫ (B.castB (Nat.zero_add b) ▷ Y)
      = ((λ_ (B.B b ⊗ Y)).inv ≫ (λ_ (𝟙_ C)).inv ▷ (B.B b ⊗ Y) ≫ tensorμ (𝟙_ C) (𝟙_ C) (B.B b) Y) ≫
          (((B.u ▷ B.B b) ≫ B.m 0 b ≫ B.castB (Nat.zero_add b)) ⊗ₘ (λ_ Y).hom) := by
        simp only [ι0, Φ, comp_whiskerRight, Category.assoc]
        rw [reassoc_of% hN, tensorHom_def]
        simp only [comp_whiskerRight, Category.assoc]
        rw [whisker_exchange]
    _ = 𝟙 _ := by
        rw [hU', castB, hm, tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id]

theorem Φ_unit_right (a : ℕ) (Y : C) :
    (ρ_ (B.B a ⊗ Y)).inv ≫ ((B.B a ⊗ Y) ◁ B.ι0 (𝟙_ C)) ≫ B.Φ a 0 Y (𝟙_ C) ≫
        (B.B (a + 0) ◁ (ρ_ Y).hom) = 𝟙 _ := by
  have hU := tensor_right_unitality (B.B a) Y
  have hU' : (ρ_ (B.B a ⊗ Y)).inv ≫ (B.B a ⊗ Y) ◁ (λ_ (𝟙_ C)).inv ≫ tensorμ (B.B a) Y (𝟙_ C) (𝟙_ C) =
      ((ρ_ (B.B a)).inv ⊗ₘ (ρ_ Y).inv) := by
    rw [← cancel_mono ((ρ_ (B.B a)).hom ⊗ₘ (ρ_ Y).hom)]
    simp only [Category.assoc, ← hU, Iso.inv_hom_id, tensorHom_comp_tensorHom, id_tensorHom_id]
  have hN := tensorμ_natural_right (B.B a) Y B.u (𝟙 (𝟙_ C))
  rw [tensorHom_id, MonoidalCategory.whiskerLeft_id, tensorHom_id] at hN
  have hm := B.unit_right a
  calc (ρ_ (B.B a ⊗ Y)).inv ≫ ((B.B a ⊗ Y) ◁ B.ι0 (𝟙_ C)) ≫ B.Φ a 0 Y (𝟙_ C) ≫ (B.B (a + 0) ◁ (ρ_ Y).hom)
      = ((ρ_ (B.B a ⊗ Y)).inv ≫ (B.B a ⊗ Y) ◁ (λ_ (𝟙_ C)).inv ≫ tensorμ (B.B a) Y (𝟙_ C) (𝟙_ C)) ≫
          (((B.B a ◁ B.u) ≫ B.m a 0) ⊗ₘ (ρ_ Y).hom) := by
        simp only [ι0, Φ, whiskerLeft_comp, Category.assoc]
        rw [reassoc_of% hN, tensorHom_def]
        simp only [comp_whiskerRight, Category.assoc]
    _ = 𝟙 _ := by
        rw [hU', hm, tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id]

theorem Φ_braid (a b : ℕ) (Y Z : C) :
    B.Φ a b Y Z ≫ (B.B (a + b) ◁ (β_ Y Z).hom) =
      (β_ (B.B a ⊗ Y) (B.B b ⊗ Z)).hom ≫ B.Φ b a Z Y ≫ (B.castB (Nat.add_comm b a) ▷ (Z ⊗ Y)) := by
  have hm := B.comm a b
  have hT := tensorμ_braiding (B.B a) Y (B.B b) Z
  calc B.Φ a b Y Z ≫ (B.B (a + b) ◁ (β_ Y Z).hom)
      = tensorμ (B.B a) Y (B.B b) Z ≫ (B.m a b ⊗ₘ (β_ Y Z).hom) := by
        rw [Φ, Category.assoc, ← tensorHom_def]
    _ = (tensorμ (B.B a) Y (B.B b) Z ≫ ((β_ (B.B a) (B.B b)).hom ⊗ₘ (β_ Y Z).hom)) ≫
          ((B.m b a ≫ B.castB (Nat.add_comm b a)) ▷ (Z ⊗ Y)) := by
        rw [← hm, Category.assoc, tensorHom_comp_whiskerRight, castB]
    _ = _ := by
        rw [hT, Φ, comp_whiskerRight]
        simp only [Category.assoc]

theorem ι0_natural {Y Y' : C} (f : Y ⟶ Y') : B.ι0 Y ≫ (B.B 0 ◁ f) = f ≫ B.ι0 Y' := by
  rw [ι0, ι0, Category.assoc, ← whisker_exchange, leftUnitor_inv_naturality_assoc]

theorem ι0_tensor (Y Z : C) : (B.ι0 Y ⊗ₘ B.ι0 Z) ≫ B.Φ 0 0 Y Z = B.ι0 (Y ⊗ Z) := by
  have hT := tensorμ_natural B.u (𝟙 Y) B.u (𝟙 Z)
  rw [tensorHom_id, tensorHom_id, id_tensorHom_id] at hT
  have hL := leftUnitor_monoidal Y Z
  have hL' : ((λ_ Y).inv ⊗ₘ (λ_ Z).inv) ≫ tensorμ (𝟙_ C) Y (𝟙_ C) Z =
      (λ_ (Y ⊗ Z)).inv ≫ (λ_ (𝟙_ C)).inv ▷ (Y ⊗ Z) := by
    rw [← cancel_mono ((λ_ (𝟙_ C)).hom ▷ (Y ⊗ Z) ≫ (λ_ (Y ⊗ Z)).hom)]
    simp only [Category.assoc, ← hL, tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id]
    simp
  have hm : (λ_ (𝟙_ C)).inv ≫ (B.u ⊗ₘ B.u) ≫ B.m 0 0 = B.u := by
    rw [tensorHom_def, Category.assoc, B.unit_right, rightUnitor_naturality, unitors_inv_equal,
      Iso.inv_hom_id_assoc]
  calc (B.ι0 Y ⊗ₘ B.ι0 Z) ≫ B.Φ 0 0 Y Z
      = (((λ_ Y).inv ⊗ₘ (λ_ Z).inv) ≫ tensorμ (𝟙_ C) Y (𝟙_ C) Z) ≫ ((B.u ⊗ₘ B.u) ≫ B.m 0 0) ▷ (Y ⊗ Z) := by
        rw [ι0, ι0, Φ, ← tensorHom_comp_tensorHom, Category.assoc, reassoc_of% hT, tensorHom_id,
          comp_whiskerRight]
        simp only [Category.assoc]
    _ = B.ι0 (Y ⊗ Z) := by
        have hm' : ((λ_ (𝟙_ C)).inv ≫ (B.u ⊗ₘ B.u)) ≫ B.m 0 0 = B.u := by rw [Category.assoc, hm]
        rw [hL', Category.assoc, ← comp_whiskerRight, ← Category.assoc, hm']
        rfl

end Phi

end GCMon

section TensorG

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) (B : GCMon C)

/-- The components `G(B_k ⊗ Y)`. -/
abbrev tcomp (Y : C) (k : ℕ) : Type := (G.obj (B.B k ⊗ Y) : Type)

/-- The underlying module `⨁_k G(B_k ⊗ Y)`. -/
abbrev tsum (Y : C) : Type := ⨁ k, tcomp G B Y k

/-- The inclusion of the `k`-th component. -/
def tlof (Y : C) (k : ℕ) : tcomp G B Y k →ₗ[ℂ] tsum G B Y := DirectSum.lof ℂ ℕ (tcomp G B Y) k

/-- The action on morphisms. -/
def tmap {Y Y' : C} (f : Y ⟶ Y') : tsum G B Y →ₗ[ℂ] tsum G B Y' :=
  DirectSum.toModule ℂ ℕ _ fun k => tlof G B Y' k ∘ₗ (G.map (B.B k ◁ f)).hom

theorem tmap_lof {Y Y' : C} (f : Y ⟶ Y') (k : ℕ) (x : tcomp G B Y k) :
    tmap G B f (tlof G B Y k x) = tlof G B Y' k ((G.map (B.B k ◁ f)).hom x) := by
  simp only [tmap, tlof, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem tsum_ext {Y : C} {M : Type} [AddCommGroup M] [Module ℂ M] {f g : tsum G B Y →ₗ[ℂ] M}
    (h : ∀ k x, f (tlof G B Y k x) = g (tlof G B Y k x)) : f = g :=
  DirectSum.linearMap_ext ℂ fun k => LinearMap.ext (h k)

theorem tlof_cast (Y : C) {a b : ℕ} (h : a = b) (x : tcomp G B Y a) :
    tlof G B Y a x = tlof G B Y b ((G.map (B.castB h ▷ Y)).hom x) := by
  subst h
  simp [GCMon.castB]

/-- **The free extension** `Y ↦ ⨁_k G(B_k ⊗ Y)` (the algebra `A ⊗ ⨁_k B_k` of `Ind(C)`). -/
def tensorG : C ⥤ ModuleCat.{0} ℂ where
  obj Y := ModuleCat.of ℂ (tsum G B Y)
  map f := ModuleCat.ofHom (tmap G B f)
  map_id Y := by
    apply ModuleCat.hom_ext
    refine tsum_ext G B fun k x => ?_
    simp [tmap_lof]
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine tsum_ext G B fun k x => ?_
    simp [tmap_lof]

theorem tensorG_map_lof {Y Y' : C} (f : Y ⟶ Y') (k : ℕ) (x : tcomp G B Y k) :
    ((tensorG G B).map f).hom (tlof G B Y k x) = tlof G B Y' k ((G.map (B.B k ◁ f)).hom x) :=
  tmap_lof G B f k x

variable [G.LaxBraided]

/-- The product on homogeneous components. -/
def tmul (Y Z : C) : tsum G B Y →ₗ[ℂ] tsum G B Z →ₗ[ℂ] tsum G B (Y ⊗ Z) :=
  DirectSum.toModule ℂ ℕ _ fun a => LinearMap.flip (DirectSum.toModule ℂ ℕ _ fun b => LinearMap.flip
    ((TensorProduct.mk ℂ (tcomp G B Y a) (tcomp G B Z b)).compr₂
      (tlof G B (Y ⊗ Z) (a + b) ∘ₗ (G.map (B.Φ a b Y Z)).hom ∘ₗ (μ G (B.B a ⊗ Y) (B.B b ⊗ Z)).hom)))

theorem tmul_lof (Y Z : C) (a b : ℕ) (x : tcomp G B Y a) (y : tcomp G B Z b) :
    tmul G B Y Z (tlof G B Y a x) (tlof G B Z b y) =
      tlof G B (Y ⊗ Z) (a + b) ((G.map (B.Φ a b Y Z)).hom ((μ G _ _).hom (x ⊗ₜ y))) := by
  simp only [tmul, tlof, DirectSum.toModule_lof, LinearMap.flip_apply, LinearMap.compr₂_apply,
    TensorProduct.mk_apply, LinearMap.comp_apply]

theorem tensorG_tensor_ext {Y Z : C} {M : ModuleCat.{0} ℂ}
    {f g : (tensorG G B).obj Y ⊗ (tensorG G B).obj Z ⟶ M}
    (h : ∀ a b x y, f.hom (tlof G B Y a x ⊗ₜ tlof G B Z b y) = g.hom (tlof G B Y a x ⊗ₜ tlof G B Z b y)) :
    f = g := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  have h1 : ∀ b y, f.hom (p ⊗ₜ tlof G B Z b y) = g.hom (p ⊗ₜ tlof G B Z b y) := by
    intro b y
    have := tsum_ext G B (f := f.hom ∘ₗ (TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z)).flip (tlof G B Z b y))
      (g := g.hom ∘ₗ (TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z)).flip (tlof G B Z b y))
      (fun a x => h a b x y)
    exact LinearMap.congr_fun this p
  have := tsum_ext G B (f := f.hom ∘ₗ TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z) p)
    (g := g.hom ∘ₗ TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z) p) h1
  exact LinearMap.congr_fun this q

theorem tensorG_tensor_ext₃ {Y Z W : C} {M : ModuleCat.{0} ℂ}
    {f g : ((tensorG G B).obj Y ⊗ (tensorG G B).obj Z) ⊗ (tensorG G B).obj W ⟶ M}
    (h : ∀ a b c x y z, f.hom ((tlof G B Y a x ⊗ₜ tlof G B Z b y) ⊗ₜ tlof G B W c z) =
      g.hom ((tlof G B Y a x ⊗ₜ tlof G B Z b y) ⊗ₜ tlof G B W c z)) : f = g := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro p q r
  let F := (TensorProduct.mk ℂ (tsum G B Y ⊗[ℂ] tsum G B Z) (tsum G B W))
  have h1 : ∀ a b c x y z, f.hom ((tlof G B Y a x ⊗ₜ tlof G B Z b y) ⊗ₜ tlof G B W c z) =
      g.hom ((tlof G B Y a x ⊗ₜ tlof G B Z b y) ⊗ₜ tlof G B W c z) := h
  have h2 : ∀ b c y z, f.hom ((p ⊗ₜ tlof G B Z b y) ⊗ₜ tlof G B W c z) =
      g.hom ((p ⊗ₜ tlof G B Z b y) ⊗ₜ tlof G B W c z) := by
    intro b c y z
    have := tsum_ext G B
      (f := f.hom ∘ₗ F.flip (tlof G B W c z) ∘ₗ (TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z)).flip (tlof G B Z b y))
      (g := g.hom ∘ₗ F.flip (tlof G B W c z) ∘ₗ (TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z)).flip (tlof G B Z b y))
      (fun a x => h1 a b c x y z)
    exact LinearMap.congr_fun this p
  have h3 : ∀ c z, f.hom ((p ⊗ₜ q) ⊗ₜ tlof G B W c z) = g.hom ((p ⊗ₜ q) ⊗ₜ tlof G B W c z) := by
    intro c z
    have := tsum_ext G B
      (f := f.hom ∘ₗ F.flip (tlof G B W c z) ∘ₗ TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z) p)
      (g := g.hom ∘ₗ F.flip (tlof G B W c z) ∘ₗ TensorProduct.mk ℂ (tsum G B Y) (tsum G B Z) p)
      (fun b y => h2 b c y z)
    exact LinearMap.congr_fun this q
  have := tsum_ext G B (f := f.hom ∘ₗ F (p ⊗ₜ q)) (g := g.hom ∘ₗ F (p ⊗ₜ q)) h3
  exact LinearMap.congr_fun this r

theorem unit_left_inv_apply {Z : C} (c : ℂ) (b : G.obj Z) :
    (μ G (𝟙_ C) Z).hom ((ε G).hom c ⊗ₜ b) = (G.map (λ_ Z).inv).hom (c • b) := by
  rw [← unit_left_apply G c b, map_map_apply, Iso.hom_inv_id, G.map_id]
  rfl

theorem unit_right_inv_apply {Z : C} (c : ℂ) (b : G.obj Z) :
    (μ G Z (𝟙_ C)).hom (b ⊗ₜ (ε G).hom c) = (G.map (ρ_ Z).inv).hom (c • b) := by
  rw [← unit_right_apply G c b, map_map_apply, Iso.hom_inv_id, G.map_id]
  rfl

instance : (tensorG G B).LaxMonoidal where
  ε := ModuleCat.ofHom (tlof G B (𝟙_ C) 0 ∘ₗ (G.map (B.ι0 (𝟙_ C))).hom ∘ₗ (ε G).hom)
  μ Y Z := ModuleCat.ofHom (TensorProduct.lift (tmul G B Y Z))
  μ_natural_left {Y Y'} f Z := by
    refine tensorG_tensor_ext G B fun a b x y => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    change tmul G B Y' Z (tmap G B f (tlof G B Y a x)) (tlof G B Z b y) =
      tmap G B (f ▷ Z) (tmul G B Y Z (tlof G B Y a x) (tlof G B Z b y))
    rw [tmap_lof, tmul_lof, tmul_lof, tmap_lof, ← μ_whiskerRight_apply, map_map_apply, map_map_apply,
      GCMon.Φ_natural_left]
  μ_natural_right {Z Z'} Y g := by
    refine tensorG_tensor_ext G B fun a b x y => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    change tmul G B Y Z' (tlof G B Y a x) (tmap G B g (tlof G B Z b y)) =
      tmap G B (Y ◁ g) (tmul G B Y Z (tlof G B Y a x) (tlof G B Z b y))
    rw [tmap_lof, tmul_lof, tmul_lof, tmap_lof, ← μ_whiskerLeft_apply, map_map_apply, map_map_apply,
      GCMon.Φ_natural_right]
  associativity Y Z W := by
    refine tensorG_tensor_ext₃ G B fun a b c x y z => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    change tmap G B (α_ Y Z W).hom (tmul G B (Y ⊗ Z) W (tmul G B Y Z (tlof G B Y a x) (tlof G B Z b y))
        (tlof G B W c z)) = tmul G B Y (Z ⊗ W) (tlof G B Y a x) (tmul G B Z W (tlof G B Z b y) (tlof G B W c z))
    rw [tmul_lof, tmul_lof, tmap_lof, tmul_lof, tmul_lof, tlof_cast G B _ (Nat.add_assoc a b c),
      ← μ_whiskerRight_apply, map_map_apply, map_map_apply, map_map_apply,
      ← μ_whiskerLeft_apply, map_map_apply, ← μ_assoc_apply, map_map_apply]
    try simp only [Category.assoc]
    rw [GCMon.Φ_assoc]
  left_unitality Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro c p
    have key : ∀ k (y : tcomp G B Y k), (λ_ ((tensorG G B).obj Y)).hom.hom (c ⊗ₜ tlof G B Y k y) =
        tmap G B (λ_ Y).hom (tmul G B (𝟙_ C) Y ((tlof G B (𝟙_ C) 0 ∘ₗ (G.map (B.ι0 (𝟙_ C))).hom ∘ₗ
          (ε G).hom) c) (tlof G B Y k y)) := by
      intro k y
      rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        tmul_lof, tmap_lof, tlof_cast G B Y (Nat.zero_add k), ← μ_whiskerRight_apply,
        unit_left_inv_apply, map_map_apply, map_map_apply, map_map_apply, map_map_apply]
      try simp only [Category.assoc]
      rw [GCMon.Φ_unit_left, G.map_id]
      simp only [ModuleCat.hom_id, LinearMap.id_apply, map_smul]
      rfl
    have := tsum_ext G B (f := (λ_ ((tensorG G B).obj Y)).hom.hom ∘ₗ TensorProduct.mk ℂ ℂ (tsum G B Y) c)
      (g := tmap G B (λ_ Y).hom ∘ₗ tmul G B (𝟙_ C) Y ((tlof G B (𝟙_ C) 0 ∘ₗ (G.map (B.ι0 (𝟙_ C))).hom ∘ₗ
          (ε G).hom) c)) key
    exact LinearMap.congr_fun this p
  right_unitality Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p c
    have key : ∀ k (y : tcomp G B Y k), (ρ_ ((tensorG G B).obj Y)).hom.hom (tlof G B Y k y ⊗ₜ c) =
        tmap G B (ρ_ Y).hom (tmul G B Y (𝟙_ C) (tlof G B Y k y) ((tlof G B (𝟙_ C) 0 ∘ₗ
          (G.map (B.ι0 (𝟙_ C))).hom ∘ₗ (ε G).hom) c)) := by
      intro k y
      rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        tmul_lof, tmap_lof, ← μ_whiskerLeft_apply, unit_right_inv_apply, map_map_apply, map_map_apply,
        map_map_apply]
      try simp only [Category.assoc]
      rw [GCMon.Φ_unit_right, G.map_id]
      simp only [ModuleCat.hom_id, LinearMap.id_apply, map_smul]
      rfl
    have := tsum_ext G B (f := (ρ_ ((tensorG G B).obj Y)).hom.hom ∘ₗ (TensorProduct.mk ℂ (tsum G B Y) ℂ).flip c)
      (g := tmap G B (ρ_ Y).hom ∘ₗ (tmul G B Y (𝟙_ C)).flip ((tlof G B (𝟙_ C) 0 ∘ₗ
          (G.map (B.ι0 (𝟙_ C))).hom ∘ₗ (ε G).hom) c)) key
    exact LinearMap.congr_fun this p

theorem tensorG_μ_lof (Y Z : C) (a b : ℕ) (x : tcomp G B Y a) (y : tcomp G B Z b) :
    (μ (tensorG G B) Y Z).hom (tlof G B Y a x ⊗ₜ tlof G B Z b y) =
      tlof G B (Y ⊗ Z) (a + b) ((G.map (B.Φ a b Y Z)).hom ((μ G _ _).hom (x ⊗ₜ y))) :=
  tmul_lof G B Y Z a b x y

theorem tensorG_ε_apply (c : ℂ) :
    (ε (tensorG G B)).hom c = tlof G B (𝟙_ C) 0 ((G.map (B.ι0 (𝟙_ C))).hom ((ε G).hom c)) := rfl

instance : (tensorG G B).LaxBraided where
  braided Y Z := by
    refine tensorG_tensor_ext G B fun a b x y => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.braiding_hom_apply]
    rw [tensorG_μ_lof, tensorG_μ_lof, tensorG_map_lof, tlof_cast G B _ (Nat.add_comm b a),
      ← μ_braid_apply G x y, map_map_apply, map_map_apply, map_map_apply, GCMon.Φ_braid]

instance [G.Additive] : (tensorG G B).Additive where
  map_add {Y Y' f g} := by
    apply ModuleCat.hom_ext
    refine tsum_ext G B fun k x => ?_
    change tmap G B (f + g) _ = tmap G B f _ + tmap G B g _
    rw [tmap_lof, tmap_lof, tmap_lof, MonoidalPreadditive.whiskerLeft_add, G.map_add, ← map_add]
    rfl

instance [G.Linear ℂ] : (tensorG G B).Linear ℂ where
  map_smul {Y Y'} f c := by
    apply ModuleCat.hom_ext
    refine tsum_ext G B fun k x => ?_
    change tmap G B (c • f) _ = c • tmap G B f _
    rw [tmap_lof, tmap_lof, MonoidalLinear.whiskerLeft_smul, Functor.map_smul, ← map_smul]
    rfl

/-- The inclusion `G Y → tensorG G B Y` (degree `0`). -/
def inclG (Y : C) : G.obj Y →ₗ[ℂ] (tensorG G B).obj Y :=
  tlof G B Y 0 ∘ₗ (G.map (B.ι0 Y)).hom

theorem inclG_apply (Y : C) (x : G.obj Y) : inclG G B Y x = tlof G B Y 0 ((G.map (B.ι0 Y)).hom x) := rfl

theorem inclG_map {Y Y' : C} (f : Y ⟶ Y') (x : G.obj Y) :
    ((tensorG G B).map f).hom (inclG G B Y x) = inclG G B Y' ((G.map f).hom x) := by
  rw [inclG_apply, inclG_apply, tensorG_map_lof, map_map_apply, map_map_apply, GCMon.ι0_natural]

theorem μ_tensorHom_apply' {A A' D D' : C} (f : A ⟶ A') (g : D ⟶ D') (a : G.obj A) (b : G.obj D) :
    (μ G A' D').hom ((G.map f).hom a ⊗ₜ (G.map g).hom b) = (G.map (f ⊗ₘ g)).hom ((μ G A D).hom (a ⊗ₜ b)) := by
  rw [tensorHom_def, map_comp_apply, μ_whiskerRight_apply, μ_whiskerLeft_apply]

theorem inclG_μ (Y Z : C) (x : G.obj Y) (y : G.obj Z) :
    (μ (tensorG G B) Y Z).hom (inclG G B Y x ⊗ₜ inclG G B Z y) = inclG G B (Y ⊗ Z) ((μ G Y Z).hom (x ⊗ₜ y)) := by
  rw [inclG_apply, inclG_apply, tensorG_μ_lof, inclG_apply, μ_tensorHom_apply', map_map_apply,
    GCMon.ι0_tensor]

theorem inclG_ε (c : ℂ) : (ε (tensorG G B)).hom c = inclG G B (𝟙_ C) ((ε G).hom c) := rfl

theorem inclG_injective (Y : C) : Function.Injective (inclG G B Y) := by
  intro x y h
  rw [inclG_apply, inclG_apply] at h
  have h1 := DirectSum.of_injective (β := tcomp G B Y) 0 h
  have hr : B.ι0 Y ≫ ((B.uinv ▷ Y) ≫ (λ_ Y).hom) = 𝟙 Y := by
    rw [GCMon.ι0, Category.assoc, ← Category.assoc (B.u ▷ Y), ← comp_whiskerRight, B.u_uinv,
      id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
  have := congrArg (G.map ((B.uinv ▷ Y) ≫ (λ_ Y).hom)).hom h1
  rwa [map_map_apply, map_map_apply, hr, G.map_id] at this

theorem rank_tensorG_le {Y : C} (h : ∀ k, Module.rank ℂ (G.obj (B.B k ⊗ Y)) ≤ ℵ₀) :
    Module.rank ℂ ((tensorG G B).obj Y) ≤ ℵ₀ := by
  change Module.rank ℂ (⨁ k, tcomp G B Y k) ≤ ℵ₀
  rw [rank_directSum]
  calc Cardinal.sum (fun k => Module.rank ℂ (tcomp G B Y k)) ≤ Cardinal.sum (fun _ : ℕ => ℵ₀) :=
        Cardinal.sum_le_sum _ _ h
    _ = ℵ₀ := by simp

end TensorG

end VOA.Huang.TensorCat.DeligneFiber
