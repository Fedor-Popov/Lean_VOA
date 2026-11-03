import VOA.Huang.FusionProductFiniteness
import VOA.Huang.AssocConverseRepresentatives

/-! # Fusion products of ordinary modules of a strongly rational VOA

The semisimple model represents the full intertwiner functor on every ordinary
target. Finiteness of irreducible classes is explicit in the axiom-clean theorem;
the separate PBW corollary uses the existing project witness VOA.pbw.

No associator, monoidal coherence, braiding, rigidity, or ribbon structure is
asserted by this file. Those require the subsequent TC stages.
-/
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit Module
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]

/-- The semisimple construction, with a finite complete family presented explicitly. -/
theorem nonempty_product_of_finiteTargets (hV : StronglyRational W)
    (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    {ι : Type u} [Finite ι] (R : ι → LWModule W)
    (iR : ∀ i, (R i).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j)
    (hR : FiniteTargets R) : Nonempty (Product A₁ A₂) := by
  letI := Fintype.ofFinite ι
  letI (i : ι) : FiniteDimensional ℂ (IntertwiningOperator A₁ A₂ (R i).isMod) :=
    finiteDimensional_intertwining_ordinary hV A₁ A₂ R iR hR (R i) (iR i)
  let κ (i : ι) := Module.Free.ChooseBasisIndex ℂ (IntertwiningOperator A₁ A₂ (R i).isMod)
  letI (i : ι) : Fintype (κ i) := Fintype.ofFinite _
  exact ⟨productOfFiniteTargets A₁ A₂ R κ
    (fun i => Module.Free.chooseBasis ℂ (IntertwiningOperator A₁ A₂ (R i).isMod)) iR hne hR⟩

/-- Fusion products exist for arbitrary ordinary input modules. The finiteness
hypothesis is explicit, so this theorem does not depend on VOA.pbw. -/
theorem nonempty_product (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) : Nonempty (Product A₁ A₂) := by
  obtain ⟨n, R, iR, hcomplete, hne⟩ := AssocConverse.exists_completeIrredundantFamily hΦ
  let S : ULift.{u} (Fin n) → LWModule W := fun i => R i.down
  have iS : ∀ i, (S i).IsIrreducibleLW := fun i => iR i.down
  have hS : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (S i) := by
    intro Q iQ
    obtain ⟨i, hi⟩ := hcomplete Q iQ
    exact ⟨⟨i⟩, hi⟩
  have hneS : ∀ i j, LWModule.Iso W (S i) (S j) → i = j := by
    intro i j hij
    exact ULift.ext _ _ (hne i.down j.down hij)
  exact nonempty_product_of_finiteTargets hV A₁ A₂ S iS hneS
    (finiteTargets_of_stronglyRational hV hΦ S hS)

/-- PBW-relative existence, with no remaining mathematical input beyond strong rationality. -/
theorem nonempty_product_pbw (hV : StronglyRational W)
    (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) : Nonempty (Product A₁ A₂) :=
  nonempty_product hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV) A₁ A₂

/-- A chosen fusion product, including its universal intertwiner and ordinary structure. -/
def fusionProduct (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) : Product A₁ A₂ :=
  Classical.choice (nonempty_product hV hΦ A₁ A₂)

/-- Full unique factorization into an arbitrary ordinary target, at every complex mode. -/
theorem fusionProduct_factor (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    {N : Type u} [AddCommGroup N] [Module ℂ N] (AN : OrdVModule W N)
    (Z : IntertwiningOperator A₁ A₂ AN) :
    ∃! f : homSpace (fusionProduct hV hΦ A₁ A₂).isMod AN,
      postcompose (fusionProduct hV hΦ A₁ A₂).intertwiner AN f = Z :=
  existsUnique_factor ((fusionProduct hV hΦ A₁ A₂).universal N AN) Z

end VOA.Huang.FusionProduct
