import VOA.Huang.FusionProductUniversal

/-! # Universality for finite semisimple targets

The remaining module-theoretic interface is finite domination by the specified
family: a finite sum of inclusion/projection composites is the identity.
It contains no intertwiner or tensor-product existence assumption.
-/
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit Module
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ T N Q : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup T] [Module ℂ T] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup Q] [Module ℂ Q]

/-- Composition in the module-map space. -/
def compHom {AT : OrdVModule W T} {AN : OrdVModule W N} {AQ : OrdVModule W Q}
    (g : homSpace AN AQ) (f : homSpace AT AN) : homSpace AT AQ :=
  ⟨g.val.comp f.val, fun a n x => by
    change g.val (f.val (mode (AT.YM a) n x)) = _
    rw [f.property, g.property]; rfl⟩

/-- A finite split presentation by members of R. Repeated labels are allowed. -/
def FiniteTarget {ι : Type u} (R : ι → LWModule W) (AN : OrdVModule W N) : Prop :=
  ∃ (r : ℕ) (lab : Fin r → ι)
    (inc : ∀ j, homSpace (R (lab j)).isMod AN)
    (proj : ∀ j, homSpace AN (R (lab j)).isMod),
    ∀ x : N, ∑ j, (inc j).val ((proj j).val x) = x

/-- Pure module-theoretic target; true for a complete simple family under
strong rationality. It is not asserted for incomplete families. -/
def FiniteTargets {ι : Type u} (R : ι → LWModule W) : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module ℂ N] (AN : OrdVModule W N), FiniteTarget R AN

/-- Representability on a family extends to every finite split target. -/
theorem universalFor_of_finiteTarget
    {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {AT : OrdVModule W T}
    (Y : IntertwiningOperator A₁ A₂ AT) {ι : Type u} (R : ι → LWModule W)
    (hY : ∀ i, UniversalFor Y (R i).isMod) (AN : OrdVModule W N)
    (hN : FiniteTarget R AN) : UniversalFor Y AN := by
  classical
  obtain ⟨r, lab, inc, proj, htotal⟩ := hN
  constructor
  · intro f g hfg
    have hj (j : Fin r) : compHom (proj j) f = compHom (proj j) g := by
      apply (hY (lab j)).1
      apply Subtype.ext
      funext n
      ext x y
      exact congrArg (fun Z : IntertwiningOperator A₁ A₂ AN =>
        (proj j).val (Z.val n x y)) hfg
    apply Subtype.ext
    ext x
    rw [← htotal (f.val x), ← htotal (g.val x)]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (inc j).val (congrArg (fun h : homSpace AT (R (lab j)).isMod => h.val x) (hj j))
  · intro Z
    choose f hf using fun j => (hY (lab j)).2 (postcompose Z (R (lab j)).isMod (proj j))
    refine ⟨∑ j, compHom (inc j) (f j), ?_⟩
    apply Subtype.ext
    funext n
    ext x y
    have hj (j : Fin r) := congrArg
      (fun Z : IntertwiningOperator A₁ A₂ (R (lab j)).isMod => Z.val n x y) (hf j)
    change (∑ j, compHom (inc j) (f j)).val (Y.val n x y) = Z.val n x y
    have he (t : T) : (∑ j, compHom (inc j) (f j)).val t =
        ∑ j, (inc j).val ((f j).val t) := by
      change ((homSpace AT AN).subtype (∑ j, compHom (inc j) (f j))) t = _
      rw [map_sum]
      simp only [LinearMap.sum_apply]
      rfl
    rw [he]
    change (∑ j, (inc j).val ((f j).val (Y.val n x y))) = _
    simp only [postcompose_apply] at hj
    simp_rw [hj]
    exact htotal _

variable (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
  {ι : Type u} [Fintype ι] (R : ι → LWModule W)
  (κ : ι → Type u) [∀ i, Fintype (κ i)]
  (B : ∀ i, Basis (κ i) ℂ (IntertwiningOperator A₁ A₂ (R i).isMod))

/-- Full ordinary-target universality, conditional only on the displayed
pure module decomposition and the finite intertwiner bases. -/
theorem isUniversal_of_finiteTargets (iR : ∀ i, (R i).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j)
    (hR : FiniteTargets R) : IsUniversal (universalIntertwiner A₁ A₂ R κ B) := by
  intro N _ _ AN
  exact universalFor_of_finiteTarget _ R (universalFor_channel A₁ A₂ R κ B iR hne) AN (hR N AN)

/-- The concrete semisimple fusion product with its full universal property. -/
def productOfFiniteTargets (iR : ∀ i, (R i).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j)
    (hR : FiniteTargets R) : Product A₁ A₂ where
  carrier := Carrier R κ
  isMod := model R κ
  intertwiner := universalIntertwiner A₁ A₂ R κ B
  universal := isUniversal_of_finiteTargets A₁ A₂ R κ B iR hne hR

end VOA.Huang.FusionProduct
