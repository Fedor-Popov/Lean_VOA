import VOA.Huang.FusionProductMain

/-! # Uniqueness of fusion products as actual VOA modules

Changing the finite family or the intertwiner bases gives a unique compatible
module isomorphism, because both constructions represent the same functor.
-/
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}

/-- The unique factor map provided by a fusion product. -/
def Product.lift (P : Product A₁ A₂)
    {N : Type u} [AddCommGroup N] [Module ℂ N] (AN : OrdVModule W N)
    (Y : IntertwiningOperator A₁ A₂ AN) : homSpace P.isMod AN :=
  (homEquiv (P.universal N AN)).symm Y

@[simp] theorem Product.lift_spec (P : Product A₁ A₂)
    {N : Type u} [AddCommGroup N] [Module ℂ N] (AN : OrdVModule W N)
    (Y : IntertwiningOperator A₁ A₂ AN) : postcompose P.intertwiner AN (P.lift AN Y) = Y :=
  (homEquiv (P.universal N AN)).apply_symm_apply Y

/-- Maps out of a fusion product agree if they agree on all universal modes. -/
theorem Product.hom_ext (P : Product A₁ A₂)
    {N : Type u} [AddCommGroup N] [Module ℂ N] (AN : OrdVModule W N)
    (f g : homSpace P.isMod AN)
    (h : ∀ n x y, f.val (P.intertwiner.val n x y) = g.val (P.intertwiner.val n x y)) : f = g := by
  apply (P.universal N AN).1
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  exact h n x

private theorem lift_inverse (P Q : Product A₁ A₂) (x : P.carrier) :
    (Q.lift P.isMod P.intertwiner).val ((P.lift Q.isMod Q.intertwiner).val x) = x := by
  let idP : homSpace P.isMod P.isMod := ⟨LinearMap.id, fun _ _ _ => rfl⟩
  have hh : compHom (Q.lift P.isMod P.intertwiner) (P.lift Q.isMod Q.intertwiner) = idP := by
    apply P.hom_ext P.isMod
    intro n a b
    have h₁ := congrArg (fun Y : IntertwiningOperator A₁ A₂ Q.isMod => Y.val n a b)
      (P.lift_spec Q.isMod Q.intertwiner)
    have h₂ := congrArg (fun Y : IntertwiningOperator A₁ A₂ P.isMod => Y.val n a b)
      (Q.lift_spec P.isMod P.intertwiner)
    change (Q.lift P.isMod P.intertwiner).val
      ((P.lift Q.isMod Q.intertwiner).val (P.intertwiner.val n a b)) = P.intertwiner.val n a b
    exact (congrArg (Q.lift P.isMod P.intertwiner).val h₁).trans h₂
  exact congrArg (fun f : homSpace P.isMod P.isMod => f.val x) hh

/-- Any two fusion products are isomorphic as ordinary VOA modules. -/
def productIso (P Q : Product A₁ A₂) : ModuleEquiv W P.isMod Q.isMod where
  toLinearEquiv :=
    { (P.lift Q.isMod Q.intertwiner).val with
      invFun := (Q.lift P.isMod P.intertwiner).val
      left_inv := lift_inverse P Q
      right_inv := lift_inverse Q P }
  map_act := (P.lift Q.isMod Q.intertwiner).property

/-- The isomorphism carries every universal mode to its counterpart. -/
theorem productIso_intertwiner (P Q : Product A₁ A₂) (n : ℂ) (x : M₁) (y : M₂) :
    (productIso P Q).toLinearEquiv (P.intertwiner.val n x y) = Q.intertwiner.val n x y :=
  congrArg (fun Y : IntertwiningOperator A₁ A₂ Q.isMod => Y.val n x y)
    (P.lift_spec Q.isMod Q.intertwiner)

end VOA.Huang.FusionProduct
