/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ReconstructionCoalgebra
import Mathlib.RepresentationTheory.FDRep

/-!
# Tannaka reconstruction — the group `Aut⊗(ω)` and the functor `D ⥤ FDRep ℂ G`

For a braided, additive, `ℂ`-linear `ω : D ⥤ FGModuleCat ℂ` out of a symmetric fusion category:

* group-like elements of the bialgebra `RAlg ω` are **monoidal**
  (`tensor_of_groupLike`, `unit_of_groupLike`) and, by rigidity, **invertible**
  (`leftInv_of_groupLike`, `isUnit_of_groupLike`);
* `AutG ω` — the finite group of group-like units (`Aut⊗(ω)`); `span_GL` (density, from the
  finite Cartier theorem `span_isGroupLikeElem_eq_top` of `ReconstructionCartier`);
* `fiberRep ω : D ⥤ FDRep ℂ (AutG ω)`, `X ↦ (ω X, g ↦ ext g X)`; faithful, `ℂ`-linear, **full**
  (density + the fullness criterion of R1), braided monoidal (`fiberRepBraided`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.Reconstruction

open CategoryTheory MonoidalCategory Limits Module TensorProduct Functor.LaxMonoidal
  Functor.OplaxMonoidal

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

variable (ω : D ⥤ FGModuleCat ℂ) [ω.Braided] [ω.Additive] [ω.Linear ℂ]

theorem comulLin_of_groupLike {g : RAlg ω} (hg : IsGroupLikeElem ℂ g) : comulLin ω g = g ⊗ₜ g := by
  have := hg.comul_eq_tmul_self
  rwa [comul_eq] at this

/-- Group-like elements are monoidal. -/
@[reassoc]
theorem tensor_of_groupLike {g : RAlg ω} (hg : IsGroupLikeElem ℂ g) (X Y : D) :
    (extMor ω g X ⊗ₘ extMor ω g Y) ≫ μ ω X Y = μ ω X Y ≫ extMor ω g (X ⊗ Y) := by
  have h := evPair_comul ω g X Y
  rw [comulLin_of_groupLike ω hg, evPair_tmul] at h
  rw [h, conjTensor]
  simp only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]

theorem unit_of_groupLike {g : RAlg ω} (hg : IsGroupLikeElem ℂ g) :
    extMor ω g (𝟙_ D) = 𝟙 _ := by
  have := hg.counit_eq_one
  rw [counit_eq] at this
  rw [extMor_unit, this, one_smul]

/-- Rigidity: a group-like element acts by a left-invertible map on every fiber. -/
theorem leftInv_of_groupLike {g : RAlg ω} (hg : IsGroupLikeElem ℂ g) (X : D) :
    ∃ h : ω.obj X ⟶ ω.obj X, extMor ω g X ≫ h = 𝟙 _ := by
  letI P : ExactPairing (ω.obj X) (ω.obj Xᘁ) := exactPairingMap ω X Xᘁ
  have hε : (extMor ω g Xᘁ ⊗ₘ extMor ω g X) ≫ ε_ (ω.obj X) (ω.obj Xᘁ) =
      ε_ (ω.obj X) (ω.obj Xᘁ) := by
    change (_ ⊗ₘ _) ≫ μ ω Xᘁ X ≫ ω.map (ε_ X Xᘁ) ≫ η ω = μ ω Xᘁ X ≫ ω.map (ε_ X Xᘁ) ≫ η ω
    rw [tensor_of_groupLike_assoc ω hg, extMor_natural_assoc, unit_of_groupLike ω hg,
      Category.id_comp]
  refine ⟨(λ_ _).inv ≫ (η_ (ω.obj X) (ω.obj Xᘁ) ▷ ω.obj X) ≫ (α_ _ _ _).hom ≫
      (ω.obj X ◁ ((extMor ω g Xᘁ ▷ ω.obj X) ≫ ε_ (ω.obj X) (ω.obj Xᘁ))) ≫ (ρ_ _).hom, ?_⟩
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, ← tensorHom_def'_assoc, hε,
    ExactPairing.evaluation_coevaluation_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- **Group-like elements of `End(ω)` are invertible** (rigidity). -/
theorem isUnit_of_groupLike {g : RAlg ω} (hg : IsGroupLikeElem ℂ g) : IsUnit g := by
  choose h hh using fun i => leftInv_of_groupLike ω hg (F.simple i)
  let h' : RAlg ω := fun i => h i
  have hl : h' * g = 1 := RAlg.ext ω fun i => by
    rw [RAlg.mul_apply, RAlg.one_apply]
    have := hh i
    rwa [extMor_simple] at this
  have hinj : Function.Injective (LinearMap.mulLeft ℂ g) := by
    intro x y hxy
    have : h' * (g * x) = h' * (g * y) := congrArg (h' * ·) hxy
    rwa [← mul_assoc, ← mul_assoc, hl, one_mul, one_mul] at this
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  have hy' : g * y = 1 := hy
  have : y = h' := by
    calc y = h' * g * y := by rw [hl, one_mul]
      _ = h' := by rw [mul_assoc, hy', mul_one]
  rw [this] at hy'
  exact ⟨⟨g, h', hy', hl⟩, rfl⟩

/-- The group `Aut⊗(ω)` of group-like units of `End(ω)`. -/
def groupLikeUnits : Subgroup (RAlg ω)ˣ where
  carrier := {u | IsGroupLikeElem ℂ (u : RAlg ω)}
  mul_mem' {a b} ha hb := by
    change IsGroupLikeElem ℂ ((a : RAlg ω) * b)
    exact ha.mul hb
  one_mem' := IsGroupLikeElem.one
  inv_mem' {a} ha := isGroupLikeElem_unitsInv.mpr ha

/-- `G = Aut⊗(ω)`. -/
abbrev AutG := ↥(groupLikeUnits ω)

/-- The underlying element of `RAlg ω`. -/
def AutG.val (u : AutG ω) : RAlg ω := ((u : (RAlg ω)ˣ) : RAlg ω)

theorem AutG.isGroupLike (u : AutG ω) : IsGroupLikeElem ℂ (AutG.val ω u) := u.2

@[simp] theorem AutG.val_mul (u v : AutG ω) : AutG.val ω (u * v) = AutG.val ω u * AutG.val ω v := rfl
@[simp] theorem AutG.val_one : AutG.val ω 1 = 1 := rfl

theorem AutG.val_injective : Function.Injective (AutG.val ω) := fun u v h =>
  Subtype.ext (Units.ext h)

instance : Finite (AutG ω) := by
  have hli := linearIndepOn_isGroupLikeElem (R := ℂ) (A := RAlg ω)
  haveI : Finite {a : RAlg ω | IsGroupLikeElem ℂ a} := LinearIndependent.finite hli
  exact Finite.of_injective (fun u : AutG ω => (⟨AutG.val ω u, AutG.isGroupLike ω u⟩ :
    {a : RAlg ω | IsGroupLikeElem ℂ a})) fun u v h => AutG.val_injective ω (congrArg Subtype.val h)

/-- **Density**: the group-like units span `End(ω)`. -/
theorem span_GL : Submodule.span ℂ (Set.range (AutG.val ω)) = ⊤ := by
  rw [eq_top_iff, ← span_isGroupLikeElem_eq_top (A := RAlg ω) fun a ha => isUnit_of_groupLike ω ha]
  apply Submodule.span_mono
  intro a ha
  obtain ⟨u, rfl⟩ := isUnit_of_groupLike ω ha
  exact ⟨⟨u, ha⟩, rfl⟩

/-- The action of `G` on the fiber `ω X`. -/
def fiberAction (X : D) : AutG ω →* End (ω.obj X) where
  toFun u := extMor ω (AutG.val ω u) X
  map_one' := by rw [AutG.val_one, extMor_one]; rfl
  map_mul' u v := by rw [AutG.val_mul, extMor_mul, End.mul_def]

@[simp] theorem fiberAction_apply (X : D) (u : AutG ω) :
    fiberAction ω X u = extMor ω (AutG.val ω u) X := rfl

/-- The **reconstruction functor** `D ⥤ FDRep ℂ (Aut⊗ ω)`. -/
def fiberRep : D ⥤ FDRep ℂ (AutG ω) where
  obj X := ⟨ω.obj X, fiberAction ω X⟩
  map f := ⟨ω.map f, fun u => extMor_natural ω _ f⟩
  map_id X := Action.Hom.ext (ω.map_id X)
  map_comp f g := Action.Hom.ext (ω.map_comp f g)

@[simp] theorem fiberRep_obj_V (X : D) : ((fiberRep ω).obj X).V = ω.obj X := rfl
@[simp] theorem fiberRep_map_hom {X Y : D} (f : X ⟶ Y) : ((fiberRep ω).map f).hom = ω.map f := rfl

instance [ω.Faithful] : (fiberRep ω).Faithful where
  map_injective {X Y} f g h := ω.map_injective (congrArg Action.Hom.hom h)

instance : (fiberRep ω).Linear ℂ where
  map_smul {X Y} f r := Action.Hom.ext (by rw [Action.smul_hom]; exact Functor.map_smul ω r f)

/-- The reconstruction functor is **full** (density + fullness criterion). -/
instance : (fiberRep ω).Full where
  map_surjective {X Y} φ := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ω.obj X ⟶ ω.obj Y, ψ = φ.hom := ⟨_, rfl⟩
    have hcomm : ∀ a : RAlg ω, extMor ω a X ≫ ψ = ψ ≫ extMor ω a Y := by
      intro a
      have ha : a ∈ Submodule.span ℂ (Set.range (AutG.val ω)) := by
        rw [span_GL]; exact Submodule.mem_top
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, rfl⟩ := hx
        rw [hψ]
        exact φ.comm u
      | zero => simp
      | add x y _ _ hx hy =>
        rw [extMor_add, extMor_add, Preadditive.add_comp, Preadditive.comp_add, hx, hy]
      | smul t x _ hx =>
        rw [extMor_smul, extMor_smul, Linear.smul_comp, Linear.comp_smul, hx]
    obtain ⟨h, hh⟩ := exists_map_eq_of_commute ω ψ hcomm
    exact ⟨h, Action.Hom.ext (hh.trans hψ)⟩

/-- The monoidal structure of the reconstruction functor. -/
def fiberRepCore : (fiberRep ω).CoreMonoidal where
  εIso := Action.mkIso (Functor.Monoidal.εIso ω) (fun u => by
    change 𝟙 _ ≫ ε ω = ε ω ≫ extMor ω (AutG.val ω u) (𝟙_ D)
    rw [unit_of_groupLike ω (AutG.isGroupLike ω u), Category.id_comp, Category.comp_id])
  μIso X Y := Action.mkIso (Functor.Monoidal.μIso ω X Y) (fun u =>
    tensor_of_groupLike ω (AutG.isGroupLike ω u) X Y)
  μIso_hom_natural_left f X' := Action.Hom.ext (Functor.LaxMonoidal.μ_natural_left ω f X')
  μIso_hom_natural_right X' f := Action.Hom.ext (Functor.LaxMonoidal.μ_natural_right ω X' f)
  associativity X Y Z := by
    ext1
    simp only [Action.comp_hom, Action.whiskerRight_hom, Action.whiskerLeft_hom,
      Action.associator_hom_hom, Action.mkIso_hom_hom, fiberRep_map_hom, fiberRep_obj_V]
    exact Functor.LaxMonoidal.associativity ω X Y Z
  left_unitality X := by
    ext1
    simp only [Action.comp_hom, Action.whiskerRight_hom, Action.leftUnitor_hom_hom,
      Action.mkIso_hom_hom, fiberRep_map_hom, fiberRep_obj_V]
    exact Functor.LaxMonoidal.left_unitality ω X
  right_unitality X := by
    ext1
    simp only [Action.comp_hom, Action.whiskerLeft_hom, Action.rightUnitor_hom_hom,
      Action.mkIso_hom_hom, fiberRep_map_hom, fiberRep_obj_V]
    exact Functor.LaxMonoidal.right_unitality ω X

instance fiberRepMonoidal : (fiberRep ω).Monoidal := (fiberRepCore ω).toMonoidal

/-- The reconstruction functor is **braided**. -/
instance fiberRepBraided : (fiberRep ω).Braided :=
  { fiberRepMonoidal ω with
    braided := fun X Y => Action.Hom.ext (Functor.LaxBraided.braided (F := ω) X Y) }

end VOA.Huang.TensorCat.Reconstruction
