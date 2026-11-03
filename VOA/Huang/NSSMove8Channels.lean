import VOA.Huang.NSSMove8Interaction

/-! # The full simple-channel decomposition of the dual interaction

Ribbon balancing makes the actual monodromy scalar on each isotypic channel,
including its multiplicity space. This does not assert that sewing transposes
on each channel separately.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The exact eigenvalue of the interaction on its k-th simple channel. -/
def dualInteractionEigenvalue (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (r b k : F.Label) : ℂ := R.twistScalar k / (R.twistScalar b * R.twistScalar r)

/-- Balancing on every simple-source map into the actual chosen-dual product. -/
theorem dualInteraction_channel (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (r b k : F.Label) (f : F.simple k ⟶ F.simple b ⊗ (F.simple r)ᘁ) :
    f ≫ monodromy (F.simple b) (F.simple r)ᘁ =
      dualInteractionEigenvalue F R r b k • f := by
  have h := R.monodromy_channel b (F.dualLabel r) k
    (f ≫ F.simple b ◁ (F.dualLabelIso r).hom)
  simp only [R.twistScalar_dualLabel] at h
  apply (cancel_mono (F.simple b ◁ (F.dualLabelIso r).hom)).mp
  simpa [dualInteractionEigenvalue, monodromy, Category.assoc] using h

/-- The whole monodromy is the weighted sum of the intrinsic isotypic projectors.
No trace is taken; this retains every multiplicity entry. -/
theorem dualInteraction_eq_sum_projectors (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (r b : F.Label) :
    monodromy (F.simple b) (F.simple r)ᘁ =
      ∑ k, dualInteractionEigenvalue F R r b k •
        F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ) := by
  classical
  apply F.hom_ext_from_simples
  intro k f
  rw [dualInteraction_channel F R]
  simp [Preadditive.comp_sum, F.comp_simpleProjector]

/-- The diagonal entries in any supplied biproduct decomposition, even with
repeated labels, have the prescribed scalar value. -/
theorem dualInteraction_biproduct_block (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (r b : F.Label) {n : ℕ} {a : Fin n → F.Label}
    (e : F.simple b ⊗ (F.simple r)ᘁ ≅ ⨁ fun k => F.simple (a k)) (k l : Fin n) :
    biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv ≫
      monodromy (F.simple b) (F.simple r)ᘁ ≫ e.hom ≫
        biproduct.π (fun k => F.simple (a k)) l =
      dualInteractionEigenvalue F R r b (a k) •
        (biproduct.ι (fun k => F.simple (a k)) k ≫
          biproduct.π (fun k => F.simple (a k)) l) := by
  rw [← Category.assoc (biproduct.ι _ k), ← Category.assoc _ (monodromy _ _),
    dualInteraction_channel F R]
  simp

/-- All off-diagonal entries vanish, including between repeated copies of a
simple. This stronger assertion uses balancing, not just Schur's lemma. -/
theorem dualInteraction_biproduct_offDiagonal (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (r b : F.Label) {n : ℕ} {a : Fin n → F.Label}
    (e : F.simple b ⊗ (F.simple r)ᘁ ≅ ⨁ fun k => F.simple (a k))
    (k l : Fin n) (h : k ≠ l) :
    biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv ≫
      monodromy (F.simple b) (F.simple r)ᘁ ≫ e.hom ≫
        biproduct.π (fun k => F.simple (a k)) l = 0 := by
  classical
  rw [dualInteraction_biproduct_block F R]
  simp [h]

/-- The unweighted sum of the channel defects is zero. It is the proved
identity-insertion transposition, with the identity resolved into channels. -/
theorem sum_interactionTransposeDefect_projectors (F : SphericalFusion C)
    (X Y : C) (i j : F.Label) :
    (∑ k, interactionTransposeDefect F X Y i j
      (F.simpleProjector k (Y ⊗ Xᘁ))) = 0 := by
  rw [← map_sum, F.sum_simpleProjector, interactionTransposeDefect_id]

/-- Exact channel expansion of the original difference of sewn morphisms. -/
theorem loopTranspose_gap_eq_sum_channels (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (r b i j : F.Label) :
    forwardSewingMap F (F.simple r) i j
        (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) -
      inverseSewingMap F (F.simple b) i j
        (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ)) =
      ∑ k, dualInteractionEigenvalue F R r b k •
        interactionTransposeDefect F (F.simple r) (F.simple b) i j
          (F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ)) := by
  rw [← interactionTransposeDefect_monodromy, dualInteraction_eq_sum_projectors F R,
    map_sum]
  simp only [map_smul]

/-- A common scalar part contributes nothing, so only eigenvalue differences
can obstruct the original transposition. -/
theorem loopTranspose_gap_eq_sum_shifted_channels (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (r b i j : F.Label) (z : ℂ) :
    forwardSewingMap F (F.simple r) i j
        (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) -
      inverseSewingMap F (F.simple b) i j
        (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ)) =
      ∑ k, (dualInteractionEigenvalue F R r b k - z) •
        interactionTransposeDefect F (F.simple r) (F.simple b) i j
          (F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ)) := by
  rw [loopTranspose_gap_eq_sum_channels F R]
  simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
    sum_interactionTransposeDefect_projectors, smul_zero, sub_zero]

end VOA.Huang.NSCongruence
