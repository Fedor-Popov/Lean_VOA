import VOA.Huang.FusionUnit

/-! # Fusion products: the representing universal property

All morphisms commute with every VOA mode. Universality concerns the full FHL
intertwiner space, not only top coefficients or numerical fusion rules.
-/

noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ T N Q : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup T] [Module ℂ T] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup Q] [Module ℂ Q]

/-- Postcomposition by an actual module map, linear in the map. -/
def postcompose {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {AT : OrdVModule W T} (Y : IntertwiningOperator A₁ A₂ AT)
    (AN : OrdVModule W N) : homSpace AT AN →ₗ[ℂ] IntertwiningOperator A₁ A₂ AN where
  toFun f := ⟨fun n => (Y.val n).compr₂ f.val, isIntertwiningOperator_compHom Y.property f.property⟩
  map_add' f g := by apply Subtype.ext; funext n; ext x y; rfl
  map_smul' c f := by apply Subtype.ext; funext n; ext x y; rfl

@[simp] theorem postcompose_apply {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {AT : OrdVModule W T} (Y : IntertwiningOperator A₁ A₂ AT)
    (AN : OrdVModule W N) (f : homSpace AT AN) (n : ℂ) (x : M₁) (y : M₂) :
    (postcompose Y AN f).val n x y = f.val (Y.val n x y) := rfl

/-- Universality for one specified target. -/
def UniversalFor {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {AT : OrdVModule W T} (Y : IntertwiningOperator A₁ A₂ AT)
    (AN : OrdVModule W N) : Prop := Function.Bijective (postcompose Y AN)

/-- The full ordinary-module universal property, including uniqueness. -/
def IsUniversal {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {AT : OrdVModule W T} (Y : IntertwiningOperator A₁ A₂ AT) : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module ℂ N] (AN : OrdVModule W N), UniversalFor Y AN

/-- The representing linear equivalence. -/
def homEquiv {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {AT : OrdVModule W T} {Y : IntertwiningOperator A₁ A₂ AT}
    {AN : OrdVModule W N} (h : UniversalFor Y AN) :
    homSpace AT AN ≃ₗ[ℂ] IntertwiningOperator A₁ A₂ AN := LinearEquiv.ofBijective _ h

/-- Every intertwiner factors through the universal intertwiner by exactly one module map. -/
theorem existsUnique_factor {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {AT : OrdVModule W T} {Y : IntertwiningOperator A₁ A₂ AT}
    {AN : OrdVModule W N} (h : UniversalFor Y AN) (Z : IntertwiningOperator A₁ A₂ AN) :
    ∃! f : homSpace AT AN, postcompose Y AN f = Z := by
  obtain ⟨f, hf⟩ := h.2 Z
  exact ⟨f, hf, fun g hg => h.1 (hg.trans hf.symm)⟩

/-- A fusion-product object includes an ordinary module and its universal intertwiner. -/
structure Product (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  isMod : OrdVModule W carrier
  intertwiner : IntertwiningOperator A₁ A₂ isMod
  universal : IsUniversal intertwiner

attribute [instance] Product.addCommGroup Product.module

/-- The vacuum is a genuine left tensor unit for every ordinary module. -/
theorem moduleIntertwiner_isUniversal (A : OrdVModule W M₂) :
    IsUniversal (moduleIntertwiner A) := by
  intro N _ _ AN
  have he (f : homSpace A AN) :
      vacModeMap A AN (postcompose (moduleIntertwiner A) AN f) = f := by
    apply Subtype.ext
    ext x
    change f.val (moduleModes A (-1) W.vacuum x) = f.val x
    rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by simp, moduleModes_apply_intCast]
    rw [← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]
  constructor
  · intro f g h
    simpa only [he] using congrArg (vacModeMap A AN) h
  · intro Z
    refine ⟨vacModeMap A AN Z, vacModeMap_injective ?_⟩
    exact he _

/-- An unconditional inhabitant of the fusion-product interface. -/
def unitProduct (A : OrdVModule W M₂) : Product (adjointModule W) A where
  carrier := M₂
  isMod := A
  intertwiner := moduleIntertwiner A
  universal := moduleIntertwiner_isUniversal A

end VOA.Huang.FusionProduct
