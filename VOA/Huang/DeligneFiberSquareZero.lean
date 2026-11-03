/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberProduct

/-!
# Deligne's fiber functor — square-zero extensions of lax braided functors

For a lax braided `G : C ⥤ ModuleCat ℂ` (a commutative algebra `A` of `Ind(C)`) and an object `V`,
the **square-zero extension** `A ⊕ (A ⊗ V)` (with `(A ⊗ V)² = 0`) is the lax braided functor
`sqZero G V : Y ↦ G Y × G (Y ⊗ V)`, with
`(a, b) · (c, d) = (a c, α⁻¹(a d) + τ(b c))`, `τ = α ≫ (Y ◁ β_{V,Y'}) ≫ α⁻¹`.
It packages "vectors with a `V`-tail" as honest vectors, so that the product calculus of
`DeligneFiberProduct` applies to them.

* `sqZero G V` with `LaxMonoidal`, `LaxBraided`, `Additive`, `Linear` instances;
* `sqZero_μ_apply`, `sqZero_ε_apply`, `sqZero_map_apply`; the inclusion `inclSq` of `G`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal
open scoped TensorProduct

universe v u

section Coherence

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] (V : C)

/-- Moving the tail `V` past `Y'`. -/
def tauSq (Y Y' : C) : (Y ⊗ V) ⊗ Y' ⟶ (Y ⊗ Y') ⊗ V :=
  (α_ Y V Y').hom ≫ (Y ◁ (β_ V Y').hom) ≫ (α_ Y Y' V).inv

theorem tauSq_natural_left {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) (Y' : C) :
    ((f ▷ V) ▷ Y') ≫ tauSq V Y₂ Y' = tauSq V Y₁ Y' ≫ ((f ▷ Y') ▷ V) := by
  simp only [tauSq, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, associator_inv_naturality_left]

theorem tauSq_natural_right (Y : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    ((Y ⊗ V) ◁ g) ≫ tauSq V Y Y₂ = tauSq V Y Y₁ ≫ ((Y ◁ g) ▷ V) := by
  simp only [tauSq, Category.assoc]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right,
    whiskerLeft_comp_assoc, associator_inv_naturality_middle]

theorem sq_assoc_coh (Y Y' Y'' : C) :
    (α_ (Y ⊗ Y') Y'' V).inv ≫ ((α_ Y Y' Y'').hom ▷ V) =
      (α_ Y Y' (Y'' ⊗ V)).hom ≫ (Y ◁ (α_ Y' Y'' V).inv) ≫ (α_ Y (Y' ⊗ Y'') V).inv := by
  monoidal

theorem sq_mixed_coh (Y Y' Y'' : C) :
    ((α_ Y Y' V).inv ▷ Y'') ≫ tauSq V (Y ⊗ Y') Y'' ≫ ((α_ Y Y' Y'').hom ▷ V) =
      (α_ Y (Y' ⊗ V) Y'').hom ≫ (Y ◁ tauSq V Y' Y'') ≫ (α_ Y (Y' ⊗ Y'') V).inv := by
  simp only [tauSq]
  monoidal

theorem sq_hexagon_coh (Y Y' Y'' : C) :
    (tauSq V Y Y' ▷ Y'') ≫ tauSq V (Y ⊗ Y') Y'' ≫ ((α_ Y Y' Y'').hom ▷ V) =
      (α_ (Y ⊗ V) Y' Y'').hom ≫ tauSq V Y (Y' ⊗ Y'') := by
  simp only [tauSq, BraidedCategory.braiding_tensor_right_hom]
  monoidal

theorem sq_left_unit_coh (Y : C) :
    (α_ (𝟙_ C) Y V).inv ≫ ((λ_ Y).hom ▷ V) = (λ_ (Y ⊗ V)).hom := by
  monoidal

theorem sq_right_unit_coh (Y : C) :
    tauSq V Y (𝟙_ C) ≫ ((ρ_ Y).hom ▷ V) = (ρ_ (Y ⊗ V)).hom := by
  simp only [tauSq, braiding_tensorUnit_right]
  monoidal

theorem sq_braid_coh₁ (Y Y' : C) :
    (β_ (Y' ⊗ V) Y).hom ≫ (α_ Y Y' V).inv ≫ ((β_ Y Y').hom ▷ V) = tauSq V Y' Y := by
  simp only [tauSq, BraidedCategory.braiding_tensor_left_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight, Category.comp_id]

theorem sq_braid_coh₂ (Y Y' : C) :
    (β_ Y' (Y ⊗ V)).hom ≫ tauSq V Y Y' ≫ ((β_ Y Y').hom ▷ V) = (α_ Y' Y V).inv := by
  simp only [tauSq, BraidedCategory.braiding_tensor_right_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id_assoc, ← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight,
    Category.comp_id]

end Coherence

section Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] (V : C)

/-- The square-zero extension `Y ↦ G Y × G (Y ⊗ V)`. -/
def sqZero : C ⥤ ModuleCat.{0} ℂ where
  obj Y := ModuleCat.of ℂ (G.obj Y × G.obj (Y ⊗ V))
  map f := ModuleCat.ofHom ((G.map f).hom.prodMap (G.map (f ▷ V)).hom)
  map_id Y := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro p
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro p
    simp

@[simp] theorem sqZero_map_fst {Y Y' : C} (f : Y ⟶ Y') (p : (sqZero G V).obj Y) :
    ((sqZero G V).map f).hom p = ((G.map f).hom p.1, (G.map (f ▷ V)).hom p.2) := rfl

theorem map_map_apply {A B E : C} (f : A ⟶ B) (g : B ⟶ E) (a : G.obj A) :
    (G.map g).hom ((G.map f).hom a) = (G.map (f ≫ g)).hom a := (map_comp_apply G f g a).symm

/-- The second component of the product. -/
def mulSnd (Y Y' : C) (p : G.obj Y × G.obj (Y ⊗ V)) (q : G.obj Y' × G.obj (Y' ⊗ V)) :
    G.obj ((Y ⊗ Y') ⊗ V) :=
  (G.map (α_ Y Y' V).inv).hom ((μ G Y (Y' ⊗ V)).hom (p.1 ⊗ₜ q.2)) +
    (G.map (tauSq V Y Y')).hom ((μ G (Y ⊗ V) Y').hom (p.2 ⊗ₜ q.1))

/-- The bilinear product of the square-zero extension. -/
def mulSq (Y Y' : C) : (G.obj Y × G.obj (Y ⊗ V)) →ₗ[ℂ] (G.obj Y' × G.obj (Y' ⊗ V)) →ₗ[ℂ]
    (G.obj (Y ⊗ Y') × G.obj ((Y ⊗ Y') ⊗ V)) :=
  LinearMap.mk₂ ℂ (fun p q => ((μ G Y Y').hom (p.1 ⊗ₜ q.1), mulSnd G V Y Y' p q))
    (fun p p' q => by
      ext
      · simp [TensorProduct.add_tmul]
      · simp only [mulSnd, Prod.fst_add, Prod.snd_add, TensorProduct.add_tmul, map_add, Prod.snd_add]
        abel)
    (fun c p q => by
      ext
      · simp [← TensorProduct.smul_tmul']
      · simp only [mulSnd, Prod.smul_fst, Prod.smul_snd, ← TensorProduct.smul_tmul', map_smul, smul_add])
    (fun p q q' => by
      ext
      · simp [TensorProduct.tmul_add]
      · simp only [mulSnd, Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, map_add]
        abel)
    (fun c p q => by
      ext
      · simp [TensorProduct.tmul_smul]
      · simp only [mulSnd, Prod.smul_fst, Prod.smul_snd, TensorProduct.tmul_smul, map_smul, smul_add])

theorem mulSq_apply (Y Y' : C) (p : G.obj Y × G.obj (Y ⊗ V)) (q : G.obj Y' × G.obj (Y' ⊗ V)) :
    mulSq G V Y Y' p q = ((μ G Y Y').hom (p.1 ⊗ₜ q.1), mulSnd G V Y Y' p q) := rfl

end Functor

section Axioms

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] (V : C)

theorem mulSnd_natural_left {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) (X' : C) (p : G.obj Y₁ × G.obj (Y₁ ⊗ V))
    (q : G.obj X' × G.obj (X' ⊗ V)) :
    mulSnd G V Y₂ X' ((G.map f).hom p.1, (G.map (f ▷ V)).hom p.2) q =
      (G.map ((f ▷ X') ▷ V)).hom (mulSnd G V Y₁ X' p q) := by
  simp only [mulSnd, map_add]
  congr 1
  · rw [← μ_whiskerRight_apply, map_map_apply, map_map_apply, associator_inv_naturality_left]
  · rw [← μ_whiskerRight_apply, map_map_apply, map_map_apply, tauSq_natural_left]

theorem mulSnd_natural_right (Y : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (p : G.obj Y × G.obj (Y ⊗ V))
    (q : G.obj Y₁ × G.obj (Y₁ ⊗ V)) :
    mulSnd G V Y Y₂ p ((G.map g).hom q.1, (G.map (g ▷ V)).hom q.2) =
      (G.map ((Y ◁ g) ▷ V)).hom (mulSnd G V Y Y₁ p q) := by
  simp only [mulSnd, map_add]
  congr 1
  · rw [← μ_whiskerLeft_apply, map_map_apply, map_map_apply, associator_inv_naturality_middle]
  · rw [← μ_whiskerLeft_apply, map_map_apply, map_map_apply, tauSq_natural_right]

theorem mulSnd_assoc (Y Y' Y'' : C) (p : G.obj Y × G.obj (Y ⊗ V)) (q : G.obj Y' × G.obj (Y' ⊗ V))
    (r : G.obj Y'' × G.obj (Y'' ⊗ V)) :
    (G.map ((α_ Y Y' Y'').hom ▷ V)).hom
        (mulSnd G V (Y ⊗ Y') Y'' ((μ G Y Y').hom (p.1 ⊗ₜ q.1), mulSnd G V Y Y' p q) r) =
      mulSnd G V Y (Y' ⊗ Y'') p ((μ G Y' Y'').hom (q.1 ⊗ₜ r.1), mulSnd G V Y' Y'' q r) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  obtain ⟨e, f⟩ := r
  simp only [mulSnd, map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
  have t1 : (G.map ((α_ Y Y' Y'').hom ▷ V)).hom ((G.map (α_ (Y ⊗ Y') Y'' V).inv).hom
        ((μ G (Y ⊗ Y') (Y'' ⊗ V)).hom ((μ G Y Y').hom (a ⊗ₜ c) ⊗ₜ f))) =
      (G.map (α_ Y (Y' ⊗ Y'') V).inv).hom ((μ G Y ((Y' ⊗ Y'') ⊗ V)).hom
        (a ⊗ₜ (G.map (α_ Y' Y'' V).inv).hom ((μ G Y' (Y'' ⊗ V)).hom (c ⊗ₜ f)))) := by
    rw [← μ_whiskerLeft_apply, ← μ_assoc_apply, map_map_apply, map_map_apply, map_map_apply,
      sq_assoc_coh]
  have t2 : (G.map ((α_ Y Y' Y'').hom ▷ V)).hom ((G.map (tauSq V (Y ⊗ Y') Y'')).hom
        ((μ G ((Y ⊗ Y') ⊗ V) Y'').hom ((G.map (α_ Y Y' V).inv).hom ((μ G Y (Y' ⊗ V)).hom (a ⊗ₜ d)) ⊗ₜ e))) =
      (G.map (α_ Y (Y' ⊗ Y'') V).inv).hom ((μ G Y ((Y' ⊗ Y'') ⊗ V)).hom
        (a ⊗ₜ (G.map (tauSq V Y' Y'')).hom ((μ G (Y' ⊗ V) Y'').hom (d ⊗ₜ e)))) := by
    rw [← μ_whiskerRight_apply, ← μ_whiskerLeft_apply, ← μ_assoc_apply, map_map_apply,
      map_map_apply, map_map_apply, map_map_apply, sq_mixed_coh]
  have t3 : (G.map ((α_ Y Y' Y'').hom ▷ V)).hom ((G.map (tauSq V (Y ⊗ Y') Y'')).hom
        ((μ G ((Y ⊗ Y') ⊗ V) Y'').hom ((G.map (tauSq V Y Y')).hom ((μ G (Y ⊗ V) Y').hom (b ⊗ₜ c)) ⊗ₜ e))) =
      (G.map (tauSq V Y (Y' ⊗ Y''))).hom ((μ G (Y ⊗ V) (Y' ⊗ Y'')).hom (b ⊗ₜ (μ G Y' Y'').hom (c ⊗ₜ e))) := by
    rw [← μ_whiskerRight_apply, ← μ_assoc_apply, map_map_apply, map_map_apply, map_map_apply,
      sq_hexagon_coh]
  rw [t1, t2, t3, add_assoc]

theorem unit_left_apply {Z : C} (c : ℂ) (b : G.obj Z) :
    (G.map (λ_ Z).hom).hom ((μ G (𝟙_ C) Z).hom ((ε G).hom c ⊗ₜ b)) = c • b := by
  have h := congrArg (fun φ => φ.hom (c ⊗ₜ b)) (Functor.LaxMonoidal.left_unitality G Z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply] at h
  exact h.symm

theorem unit_right_apply {Z : C} (c : ℂ) (b : G.obj Z) :
    (G.map (ρ_ Z).hom).hom ((μ G Z (𝟙_ C)).hom (b ⊗ₜ (ε G).hom c)) = c • b := by
  have h := congrArg (fun φ => φ.hom (b ⊗ₜ c)) (Functor.LaxMonoidal.right_unitality G Z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply] at h
  exact h.symm

theorem mulSnd_left_unit (Y : C) (c : ℂ) (p : G.obj Y × G.obj (Y ⊗ V)) :
    (G.map ((λ_ Y).hom ▷ V)).hom (mulSnd G V (𝟙_ C) Y ((ε G).hom c, 0) p) = c • p.2 := by
  simp only [mulSnd, TensorProduct.zero_tmul, map_zero, add_zero]
  rw [map_map_apply, sq_left_unit_coh, unit_left_apply]

theorem mulSnd_right_unit (Y : C) (c : ℂ) (p : G.obj Y × G.obj (Y ⊗ V)) :
    (G.map ((ρ_ Y).hom ▷ V)).hom (mulSnd G V Y (𝟙_ C) p ((ε G).hom c, 0)) = c • p.2 := by
  simp only [mulSnd, TensorProduct.tmul_zero, map_zero, zero_add]
  rw [map_map_apply, sq_right_unit_coh, unit_right_apply]

theorem mulSnd_braid (Y Y' : C) (p : G.obj Y × G.obj (Y ⊗ V)) (q : G.obj Y' × G.obj (Y' ⊗ V)) :
    (G.map ((β_ Y Y').hom ▷ V)).hom (mulSnd G V Y Y' p q) = mulSnd G V Y' Y q p := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [mulSnd, map_add]
  rw [add_comm]
  congr 1
  · rw [← μ_braid_apply G c b, map_map_apply, map_map_apply, sq_braid_coh₂]
  · rw [← μ_braid_apply G d a, map_map_apply, map_map_apply, sq_braid_coh₁]

instance : (sqZero G V).LaxMonoidal where
  ε := ModuleCat.ofHom (LinearMap.prod (ε G).hom 0)
  μ Y Y' := ModuleCat.ofHom (TensorProduct.lift (mulSq G V Y Y'))
  μ_natural_left f X' := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    refine Prod.ext ?_ ?_
    · exact (μ_whiskerRight_apply G f p.1 q.1).symm
    · exact mulSnd_natural_left G V f X' p q
  μ_natural_right X' f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    refine Prod.ext ?_ ?_
    · exact (μ_whiskerLeft_apply G f p.1 q.1).symm
    · exact mulSnd_natural_right G V X' f p q
  associativity Y Y' Y'' := by
    apply ModuleCat.MonoidalCategory.tensor_ext₃'
    intro p q r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    refine Prod.ext ?_ ?_
    · exact μ_assoc_apply G p.1 q.1 r.1
    · exact mulSnd_assoc G V Y Y' Y'' p q r
  left_unitality Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro c p
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply, ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    refine Prod.ext ?_ ?_
    · exact (unit_left_apply G c p.1).symm
    · exact (mulSnd_left_unit G V Y c p).symm
  right_unitality Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply, ModuleCat.hom_ofHom, TensorProduct.lift.tmul]
    refine Prod.ext ?_ ?_
    · exact (unit_right_apply G c p.1).symm
    · exact (mulSnd_right_unit G V Y c p).symm

theorem sqZero_μ_apply (Y Y' : C) (p : (sqZero G V).obj Y) (q : (sqZero G V).obj Y') :
    (μ (sqZero G V) Y Y').hom (p ⊗ₜ q) = ((μ G Y Y').hom (p.1 ⊗ₜ q.1), mulSnd G V Y Y' p q) := rfl

theorem sqZero_ε_apply (c : ℂ) : (ε (sqZero G V)).hom c = ((ε G).hom c, 0) := rfl

instance : (sqZero G V).LaxBraided where
  braided Y Y' := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.braiding_hom_apply]
    rw [sqZero_μ_apply, sqZero_μ_apply, sqZero_map_fst]
    refine Prod.ext ?_ ?_
    · exact μ_braid_apply G p.1 q.1
    · exact mulSnd_braid G V Y Y' p q

instance [G.Additive] : (sqZero G V).Additive where
  map_add {Y Y' f g} := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro p
    simp [Functor.map_add, MonoidalPreadditive.add_whiskerRight]
    rfl

instance [G.Linear ℂ] : (sqZero G V).Linear ℂ where
  map_smul {Y Y'} f c := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro p
    simp [Functor.map_smul, MonoidalLinear.smul_whiskerRight]
    rfl

end Axioms

end VOA.Huang.TensorCat.DeligneFiber
