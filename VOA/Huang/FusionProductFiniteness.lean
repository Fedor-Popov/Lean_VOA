import VOA.Huang.FusionProductOrdinary

/-! # Finite fusion spaces for arbitrary ordinary inputs

Restriction to finite simple presentations is injective by bilinearity.
Thus the irreducible finite-fusion theorem extends to reducible inputs.
-/
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit Module
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ E₁ E₂ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup E₁] [Module ℂ E₁]
  [AddCommGroup E₂] [Module ℂ E₂]

/-- Precomposition in the second input preserves all FHL axioms. -/
theorem precomp_right {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {AE : OrdVModule W E₂}
    (Y : IntertwiningOperator A₁ A₂ A₃) (f : homSpace AE A₂) :
    IsIntertwiningOperator A₁ AE A₃ (fun n => (Y.val n).compl₂ f.val) := by
  refine ⟨fun x y n => Y.property.truncation x (f.val y) n, ?_, ?_⟩
  · intro x n
    apply LinearMap.ext
    intro y
    change Y.val n (A₁.Lm1 x) (f.val y) = _
    rw [Y.property.L_neg_one]
    rfl
  · intro a x y l m n
    have hf := fun a m y => f.property a m y
    simp only [LinearMap.compl₂_apply, hf]
    exact Y.property.jacobi a x (f.val y) l m n

/-- Simultaneous restriction along two actual module maps. -/
def restrictInputs {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {AE₁ : OrdVModule W E₁} {AE₂ : OrdVModule W E₂}
    (f : homSpace AE₁ A₁) (g : homSpace AE₂ A₂) :
    IntertwiningOperator A₁ A₂ A₃ →ₗ[ℂ] IntertwiningOperator AE₁ AE₂ A₃ where
  toFun Y := ⟨fun n => ((Y.val n).compl₂ g.val).comp f.val,
    isIntertwiningOperator_precomp (precomp_right Y g) f.property⟩
  map_add' _ _ := by apply Subtype.ext; funext n; ext x y; rfl
  map_smul' _ _ := by apply Subtype.ext; funext n; ext x y; rfl

/-- Finite fusion for two finite semisimple input presentations and an
irreducible target. The inputs need not themselves be irreducible. -/
theorem finiteDimensional_intertwining_of_finiteTargets
    (hV : StronglyRational W) (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    {ι : Type u} (R : ι → LWModule W) (iR : ∀ i, (R i).IsIrreducibleLW)
    (h₁ : FiniteTarget R A₁) (h₂ : FiniteTarget R A₂)
    (Q : LWModule W) (iQ : Q.IsIrreducibleLW) :
    FiniteDimensional ℂ (IntertwiningOperator A₁ A₂ Q.isMod) := by
  obtain ⟨r, lab₁, inc₁, proj₁, total₁⟩ := h₁
  obtain ⟨s, lab₂, inc₂, proj₂, total₂⟩ := h₂
  let F : IntertwiningOperator A₁ A₂ Q.isMod →ₗ[ℂ]
      (∀ p : Fin r × Fin s, IntertwiningOperator (R (lab₁ p.1)).isMod (R (lab₂ p.2)).isMod Q.isMod) :=
    LinearMap.pi fun p => restrictInputs (inc₁ p.1) (inc₂ p.2)
  letI (p : Fin r × Fin s) : FiniteDimensional ℂ
      (IntertwiningOperator (R (lab₁ p.1)).isMod (R (lab₂ p.2)).isMod Q.isMod) :=
    ModuleC2.finiteDimensional_intertwiningSpace_of_stronglyRational hV (iR _) (iR _) iQ
  apply Module.Finite.of_injective F
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have hz (j : Fin r) (k : Fin s) (n : ℂ) (x : (R (lab₁ j)).carrier)
      (y : (R (lab₂ k)).carrier) : Y.val n ((inc₁ j).val x) ((inc₂ k).val y) = 0 :=
    congrArg (fun f => (f (j,k)).val n x y) hY
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change Y.val n x y = 0
  rw [← total₁ x, ← total₂ y, map_sum]
  simp only [LinearMap.sum_apply, map_sum, hz, Finset.sum_const_zero]

/-- General ordinary-input finiteness, retaining only the irreducible target. -/
theorem finiteDimensional_intertwining_ordinary (hV : StronglyRational W)
    (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    {ι : Type u} (R : ι → LWModule W) (iR : ∀ i, (R i).IsIrreducibleLW)
    (hR : FiniteTargets R) (Q : LWModule W) (iQ : Q.IsIrreducibleLW) :
    FiniteDimensional ℂ (IntertwiningOperator A₁ A₂ Q.isMod) :=
  finiteDimensional_intertwining_of_finiteTargets hV A₁ A₂ R iR
    (hR M₁ A₁) (hR M₂ A₂) Q iQ

end VOA.Huang.FusionProduct
