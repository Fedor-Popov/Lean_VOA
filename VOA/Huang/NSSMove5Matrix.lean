import VOA.Huang.NSSMove4Matrix

/-! # S-loop separation with every multiplicity matrix entry retained

These lemmas give Fourier resolution of each matrix entry, including the
entries off the diagonal. They do not evaluate the entries of the local
Müger exchange.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Matrix units in both Hom bases reconstruct the full morphism. -/
theorem hom_eq_sum_channelMatrixEntry (F : SphericalFusion C) (X Y : C) (f : X ⟶ Y) :
    f = ∑ t, ∑ α, ∑ β, channelMatrixEntry F X Y t α β f •
      (F.compositionDual (F.simpleHomBasis X t) α ≫ F.simpleHomBasis Y t β) := by
  have he (t : F.Label) (α : Fin (Module.finrank ℂ (F.simple t ⟶ X)))
      (β : Fin (Module.finrank ℂ (F.simple t ⟶ Y))) :
      F.scalarTrace X (f ≫ F.traceDualBasis (F.simpleHomBasis Y t) β ≫
        F.simpleHomBasis X t α) = channelMatrixEntry F X Y t α β f := by
    rw [← Category.assoc, ← F.scalarTrace_comp_comm (F.simpleHomBasis X t α)
      (f ≫ F.traceDualBasis (F.simpleHomBasis Y t) β),
      ← Category.assoc, F.traceDualBasis_pair]
    rfl
  simpa only [he] using F.hom_eq_sum_trace_channels
    (F.simpleHomBasis X) (F.simpleHomBasis Y) f

/-- A genuine S-loop acts on each entry by its simple-channel eigenvalue. -/
theorem channelMatrixEntry_monodromyLoop (F : SphericalFusion C) (X Y : C)
    (r t : F.Label) (α : Fin (Module.finrank ℂ (F.simple t ⟶ X)))
    (β : Fin (Module.finrank ℂ (F.simple t ⟶ Y))) (f : X ⟶ Y) :
    channelMatrixEntry F X Y t α β
        (monodromyLoop F.toPivotal (F.simple r)ᘁ X ≫ f) =
      (categoricalS F r t / F.dimension (F.simple t)) *
        channelMatrixEntry F X Y t α β f := by
  change (F.simpleHomBasis Y t).repr
    (F.simpleHomBasis X t α ≫ _ ≫ f) β = _
  rw [← Category.assoc, comp_monodromyLoop, Linear.smul_comp, map_smul]
  rfl

open Classical in
/-- Isotypic projection retains the complete multiplicity matrix of that block. -/
theorem channelMatrixEntry_simpleProjector (F : SphericalFusion C) (X Y : C)
    (s t : F.Label) (α : Fin (Module.finrank ℂ (F.simple t ⟶ X)))
    (β : Fin (Module.finrank ℂ (F.simple t ⟶ Y))) (f : X ⟶ Y) :
    channelMatrixEntry F X Y t α β (F.simpleProjector s X ≫ f) =
      if t = s then channelMatrixEntry F X Y t α β f else 0 := by
  change (F.simpleHomBasis Y t).repr (F.simpleHomBasis X t α ≫ _ ≫ f) β = _
  rw [← Category.assoc, F.comp_simpleProjector]
  split_ifs <;> simp_all [channelMatrixEntry]

open Classical in
/-- Fourier inversion separates a channel while keeping both multiplicity indices.
This recovers each individual entry, not merely the trace of its simple block. -/
theorem channelMatrixEntry_eq_sum_loops (F : SphericalFusion C) (M : Modular F)
    (X Y : C) (t : F.Label) (α : Fin (Module.finrank ℂ (F.simple t ⟶ X)))
    (β : Fin (Module.finrank ℂ (F.simple t ⟶ Y))) (f : X ⟶ Y) :
    channelMatrixEntry F X Y t α β f =
      ∑ r, (F.dimension (F.simple t) * (categoricalS F)⁻¹ t r) *
        channelMatrixEntry F X Y t α β
          (monodromyLoop F.toPivotal (F.simple r)ᘁ X ≫ f) := by
  have h := channelMatrixEntry_simpleProjector F X Y t t α β f
  rw [if_pos rfl, simpleProjector_eq_sum_loops F M] at h
  simpa only [Preadditive.sum_comp, Linear.smul_comp, map_sum, map_smul, smul_eq_mul]
    using h.symm

end VOA.Huang.NSCongruence
