import VOA.Huang.NgSchauenburgTraceChannels

/-! # The trace projection onto central morphisms

For trace-compatible spherical structures, forgetting central morphisms has a
canonical retraction characterized by the categorical trace pairing. This
constructs the projection, and proves its uniqueness, without assuming a
half-braiding averaging formula. Identifying it with a dimension-weighted loop
sum, and proving the Fourier identity needed for S-equivariance, remain open.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- Forget a central morphism, as a complex linear map of Hom spaces. -/
def centralForgetHom (X Y : Center C) : (X ⟶ Y) →ₗ[ℂ] (X.1 ⟶ Y.1) where
  toFun f := f.f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The transpose of forgetting reverse morphisms, using the two perfect
categorical trace pairings. Compatibility is needed for the retraction theorem. -/
def centralTraceRetraction (F : SphericalFusion C) (Z : SphericalFusion (Center C))
    (X Y : Center C) : (X.1 ⟶ Y.1) →ₗ[ℂ] (X ⟶ Y) :=
  (Z.tracePairingEquiv Y X).symm.toLinearMap ∘ₗ
    (centralForgetHom Y X).dualMap ∘ₗ F.tracePairing Y.1 X.1

/-- The defining trace identity, valid even before trace compatibility is imposed. -/
theorem centralTraceRetraction_pair (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {X Y : Center C}
    (f : X.1 ⟶ Y.1) (g : Y ⟶ X) :
    Z.scalarTrace Y (g ≫ centralTraceRetraction F Z X Y f) =
      F.scalarTrace Y.1 (g.f ≫ f) := by
  change Z.tracePairingEquiv Y X (centralTraceRetraction F Z X Y f) g = _
  simp [centralTraceRetraction, centralForgetHom]

/-- The pairing characterization uniquely determines the central lift. -/
theorem centralTraceRetraction_unique (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {X Y : Center C}
    (f : X.1 ⟶ Y.1) (q : X ⟶ Y)
    (hq : ∀ g : Y ⟶ X, Z.scalarTrace Y (g ≫ q) = F.scalarTrace Y.1 (g.f ≫ f)) :
    q = centralTraceRetraction F Z X Y f := by
  apply (Z.tracePairingEquiv Y X).injective
  ext g
  exact (hq g).trans (centralTraceRetraction_pair F Z f g).symm

/-- Under the pinned center trace, a central morphism is fixed. -/
theorem centralTraceRetraction_forget (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    {X Y : Center C} (f : X ⟶ Y) :
    centralTraceRetraction F Z X Y f.f = f := by
  symm
  apply centralTraceRetraction_unique
  intro g
  exact hc Y (g ≫ f)

/-- The idempotent on underlying Hom spaces whose image is the central Hom space. -/
def centralTraceProjection (F : SphericalFusion C) (Z : SphericalFusion (Center C))
    (X Y : Center C) : Module.End ℂ (X.1 ⟶ Y.1) :=
  centralForgetHom X Y ∘ₗ centralTraceRetraction F Z X Y

theorem centralTraceProjection_idempotent (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (X Y : Center C) :
    centralTraceProjection F Z X Y * centralTraceProjection F Z X Y =
      centralTraceProjection F Z X Y := by
  ext f
  change (centralTraceRetraction F Z X Y
    (centralTraceRetraction F Z X Y f).f).f = _
  rw [centralTraceRetraction_forget F Z hc]
  rfl

/-- Fixed underlying morphisms are exactly those satisfying the half-braiding
naturality equations. Thus this projection has the intended categorical image. -/
theorem centralTraceProjection_fixed_iff (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    {X Y : Center C} (f : X.1 ⟶ Y.1) :
    centralTraceProjection F Z X Y f = f ↔
      ∀ U, f ▷ U ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ U ◁ f := by
  constructor
  · intro hf
    change (centralTraceRetraction F Z X Y f).f = f at hf
    rw [← hf]
    exact (centralTraceRetraction F Z X Y f).comm
  · intro hf
    exact congrArg Center.Hom.f
      (centralTraceRetraction_forget F Z hc (⟨f, hf⟩ : X ⟶ Y))

/-- The trace of the central projector is the actual central Hom multiplicity. -/
theorem centralTraceProjection_trace (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (X Y : Center C) :
    LinearMap.trace ℂ (X.1 ⟶ Y.1) (centralTraceProjection F Z X Y) =
      (Module.finrank ℂ (X ⟶ Y) : ℂ) := by
  letI := F.homFinite
  letI := Z.homFinite
  have h : centralTraceRetraction F Z X Y ∘ₗ centralForgetHom X Y = LinearMap.id := by
    apply LinearMap.ext
    intro f
    exact centralTraceRetraction_forget F Z hc f
  rw [centralTraceProjection, LinearMap.trace_comp_comm', h, LinearMap.trace_id]

/-- Projection is self-adjoint for the categorical trace pairing, across the
two opposite Hom spaces; this is a bilinear, not Hermitian, assertion. -/
theorem centralTraceProjection_pair (F : SphericalFusion C)
    (Z : SphericalFusion (Center C))
    {X Y : Center C} (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ X.1) :
    F.scalarTrace X.1 (centralTraceProjection F Z X Y f ≫ g) =
      F.scalarTrace X.1 (f ≫ centralTraceProjection F Z Y X g) := by
  change F.scalarTrace X.1 ((centralTraceRetraction F Z X Y f).f ≫ g) =
    F.scalarTrace X.1 (f ≫ (centralTraceRetraction F Z Y X g).f)
  rw [← centralTraceRetraction_pair F Z g, Z.scalarTrace_comp_comm,
    centralTraceRetraction_pair F Z f, F.scalarTrace_comp_comm]

/-- The projection commutes with precomposition by genuine central morphisms. -/
theorem centralTraceRetraction_precomp (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {W X Y : Center C}
    (a : W ⟶ X) (f : X.1 ⟶ Y.1) :
    centralTraceRetraction F Z W Y (a.f ≫ f) = a ≫ centralTraceRetraction F Z X Y f := by
  symm
  apply centralTraceRetraction_unique
  intro g
  have h := centralTraceRetraction_pair F Z f (g ≫ a)
  change Z.scalarTrace Y ((g ≫ a) ≫ _) = F.scalarTrace Y.1 ((g.f ≫ a.f) ≫ f) at h
  simpa only [Category.assoc] using h

/-- The projection also commutes with postcomposition by central morphisms. -/
theorem centralTraceRetraction_postcomp (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {X Y U : Center C}
    (f : X.1 ⟶ Y.1) (b : Y ⟶ U) :
    centralTraceRetraction F Z X U (f ≫ b.f) = centralTraceRetraction F Z X Y f ≫ b := by
  symm
  apply centralTraceRetraction_unique
  intro g
  calc
    _ = Z.scalarTrace Y ((b ≫ g) ≫ centralTraceRetraction F Z X Y f) := by
      simpa only [Category.assoc] using
        Z.scalarTrace_comp_comm (g ≫ centralTraceRetraction F Z X Y f) b
    _ = F.scalarTrace Y.1 ((b.f ≫ g.f) ≫ f) :=
      centralTraceRetraction_pair F Z f (b ≫ g)
    _ = _ := by
      simpa only [Category.assoc] using F.scalarTrace_comp_comm b.f (g.f ≫ f)

/-- The retraction has the expected dual-basis expression using the underlying
categorical trace. The expression is independent of the chosen central basis. -/
theorem centralTraceRetraction_eq_sum (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {X Y : Center C} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (X ⟶ Y)) (f : X.1 ⟶ Y.1) :
    centralTraceRetraction F Z X Y f =
      ∑ i, F.scalarTrace X.1 (f ≫ (Z.traceDualBasis b i).f) • b i := by
  rw [← b.sum_repr (centralTraceRetraction F Z X Y f)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← Z.traceDualBasis_pair b i, Z.scalarTrace_comp_comm,
    centralTraceRetraction_pair, F.scalarTrace_comp_comm]

/-- The kernel is exactly the annihilator of reverse central morphisms.
This characterizes the missing averaging operator without assuming its loop formula. -/
theorem centralTraceRetraction_eq_zero_iff (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {X Y : Center C} (f : X.1 ⟶ Y.1) :
    centralTraceRetraction F Z X Y f = 0 ↔
      ∀ g : Y ⟶ X, F.scalarTrace X.1 (f ≫ g.f) = 0 := by
  constructor
  · intro hf g
    rw [F.scalarTrace_comp_comm, ← centralTraceRetraction_pair F Z f g, hf,
      comp_zero, map_zero]
  · intro hf
    apply (Z.tracePairingEquiv Y X).injective
    ext g
    change Z.scalarTrace Y (g ≫ centralTraceRetraction F Z X Y f) =
      (Z.tracePairingEquiv Y X 0) g
    rw [centralTraceRetraction_pair, F.scalarTrace_comp_comm, hf]
    simp

/-- The central retraction expanded through the actual simple objects of the
center. Only the coefficients use underlying traces; all summands are central. -/
theorem centralTraceRetraction_eq_sum_simpleChannels (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {X Y : Center C} (f : X.1 ⟶ Y.1) :
    centralTraceRetraction F Z X Y f = ∑ i, ∑ a, ∑ d,
      F.scalarTrace X.1
        (f ≫ (Z.traceDualBasis (Z.simpleHomBasis Y i) d ≫ Z.simpleHomBasis X i a).f) •
        (Z.compositionDual (Z.simpleHomBasis X i) a ≫ Z.simpleHomBasis Y i d) := by
  rw [Z.hom_eq_sum_trace_channels (Z.simpleHomBasis X) (Z.simpleHomBasis Y)
    (centralTraceRetraction F Z X Y f)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [Z.scalarTrace_comp_comm, centralTraceRetraction_pair, F.scalarTrace_comp_comm]

open Classical in
/-- On central simples the projector has the expected Schur trace. -/
theorem centralTraceProjection_trace_simples (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z) (i j : Z.Label) :
    LinearMap.trace ℂ ((Z.simple i).1 ⟶ (Z.simple j).1)
      (centralTraceProjection F Z (Z.simple i) (Z.simple j)) = if i = j then 1 else 0 := by
  rw [centralTraceProjection_trace F Z hc, Z.finrank_hom_simple]
  split_ifs <;> simp

end VOA.Huang.NgSchauenburg
