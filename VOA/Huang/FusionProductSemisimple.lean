import VOA.Huang.FusionProductSum

/-! # The finite semisimple fusion-product model

The carrier has one copy of R_k per basis element of I(R_k; A1,A2).
These coordinates identify it with the direct sum of I(R_k; A1,A2)^* ⊗ R_k.
No completeness or semisimplicity assumption is hidden in the definitions.
-/
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit Module
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]
  (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
  {ι : Type u} [Fintype ι] (R : ι → LWModule W)
  (κ : ι → Type u) [∀ i, Fintype (κ i)]

/-- A finite direct sum in coordinates (dual multiplicity basis). -/
abbrev Carrier := ∀ p : Sigma κ, (R p.1).carrier

/-- The ordinary module on the semisimple candidate. -/
def model : OrdVModule W (Carrier R κ) := sumOrd (fun p : Sigma κ => (R p.1).isMod)

variable (B : ∀ i, Basis (κ i) ℂ (IntertwiningOperator A₁ A₂ (R i).isMod))

/-- The canonical intertwiner in the chosen dual basis. -/
def universalIntertwiner : IntertwiningOperator A₁ A₂ (model R κ) :=
  sumIntertwiner (fun p : Sigma κ => (R p.1).isMod) (fun p => B p.1 p.2)

@[simp] theorem universalIntertwiner_apply (n : ℂ) (x : M₁) (y : M₂) (p : Sigma κ) :
    (universalIntertwiner A₁ A₂ R κ B).val n x y p = (B p.1 p.2).val n x y :=
  sumIntertwiner_apply _ _ n x y p

/-- The explicit factor of an intertwiner into a chosen simple channel. -/
def channelFactor (i : ι) (Z : IntertwiningOperator A₁ A₂ (R i).isMod) :
    homSpace (model R κ) (R i).isMod :=
  ∑ b, (B i).repr Z b • sumProjection (fun p : Sigma κ => (R p.1).isMod) ⟨i,b⟩

theorem channelFactor_spec (i : ι) (Z : IntertwiningOperator A₁ A₂ (R i).isMod) :
    postcompose (universalIntertwiner A₁ A₂ R κ B) (R i).isMod
      (channelFactor A₁ A₂ R κ B i Z) = Z := by
  unfold channelFactor
  rw [map_sum]
  have he (b : κ i) : postcompose (universalIntertwiner A₁ A₂ R κ B) (R i).isMod
      (sumProjection (fun p : Sigma κ => (R p.1).isMod) ⟨i,b⟩) = B i b := by
    apply Subtype.ext
    funext n
    ext x y
    exact universalIntertwiner_apply A₁ A₂ R κ B n x y ⟨i,b⟩
  calc
    _ = ∑ b, (B i).repr Z b • B i b := by
      apply Finset.sum_congr rfl
      intro b _
      exact ((postcompose (universalIntertwiner A₁ A₂ R κ B) (R i).isMod).map_smul _ _).trans
        (congrArg ((B i).repr Z b • ·) (he b))
    _ = Z := (B i).sum_repr Z

/-- Existence of factors into every chosen channel is unconditional on Schur. -/
theorem channel_surjective (i : ι) :
    Function.Surjective (postcompose (universalIntertwiner A₁ A₂ R κ B) (R i).isMod) :=
  fun Z => ⟨channelFactor A₁ A₂ R κ B i Z, channelFactor_spec A₁ A₂ R κ B i Z⟩

end VOA.Huang.FusionProduct
