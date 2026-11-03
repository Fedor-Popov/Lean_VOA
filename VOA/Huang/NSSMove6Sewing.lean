import VOA.Huang.NSSMove5Assembly

/-! # Open dual-basis sewing through the left pivotal bend

These identities retain the entire open morphism. They do not assert the
mixed exchange: they evaluate one of the two label sums needed for it.
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

/-- Coordinates in the reverse trace-dual basis are obtained by pairing
with the original basis. -/
theorem traceDualBasis_repr (F : SphericalFusion C) {X Y : C}
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℂ (X ⟶ Y))
    (a : ι) (g : Y ⟶ X) :
    (F.traceDualBasis b).repr g a = F.scalarTrace X (b a ≫ g) := by
  classical
  letI := Fintype.ofFinite ι
  conv_rhs => rw [← (F.traceDualBasis b).sum_repr g]
  simp only [Preadditive.comp_sum, Linear.comp_smul, map_sum, map_smul,
    F.traceDualBasis_pair, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp

/-- The isotypic projector does not depend on the chosen simple-source basis. -/
theorem simpleProjector_eq_sum_basis (F : SphericalFusion C) {Y : C}
    (i : F.Label) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (F.simple i ⟶ Y)) :
    F.simpleProjector i Y = ∑ a, F.compositionDual b a ≫ b a := by
  classical
  apply F.hom_ext_from_simples
  intro j f
  rw [F.comp_simpleProjector]
  by_cases h : j = i
  · subst j
    simp only [ite_true, Preadditive.comp_sum, ← Category.assoc,
      F.comp_compositionDual, Linear.smul_comp, Category.id_comp]
    exact (b.sum_repr f).symm
  · simp only [if_neg h, Preadditive.comp_sum, ← Category.assoc]
    symm
    apply Finset.sum_eq_zero
    intro a _
    rw [F.hom_simple_eq_zero h (f ≫ F.compositionDual b a), zero_comp]

/-- Sewing a basis with simple target against its trace-dual produces the
normalized simple projector on its source. -/
theorem sum_basis_comp_traceDual (F : SphericalFusion C) (X : C)
    (s : F.Label) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (X ⟶ F.simple s)) :
    (∑ a, b a ≫ F.traceDualBasis b a) =
      (F.dimension (F.simple s))⁻¹ • F.simpleProjector s X := by
  have hd (a : ι) : F.compositionDual (F.traceDualBasis b) a =
      F.dimension (F.simple s) • b a := by
    apply F.hom_ext_trace
    intro f
    rw [F.scalarTrace_comp_comm, F.comp_compositionDual]
    simp only [map_smul, F.scalarTrace_id, smul_eq_mul, Linear.smul_comp]
    rw [traceDualBasis_repr]
    ring
  rw [simpleProjector_eq_sum_basis F s (F.traceDualBasis b)]
  simp only [hd, Linear.smul_comp, ← Finset.smul_sum, smul_smul,
    inv_mul_cancel₀ (F.dimension_simple_ne_zero s), one_smul]

/-- Trace-duality commutes with the actual left pivotal bend. -/
theorem traceDualBasis_leftBend (F : SphericalFusion C) (A X Y : C)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℂ (A ⟶ X ⊗ Y)) (a : ι) :
    F.traceDualBasis (b.map (leftDuality A X Y).symm) a =
      leftBendAdjoint F.toPivotal (F.traceDualBasis b a) := by
  apply F.hom_ext_trace
  intro f
  rw [F.scalarTrace_comp_comm, F.traceDualBasis_pair]
  have h := scalarTrace_leftBend F ((leftDuality A X Y) f) (F.traceDualBasis b a)
  simpa [Module.Basis.map_repr] using h

/-- Bending both members of each composition-dual pair changes the
normalization from the source simple dimension to the target one. -/
theorem sum_leftBend_compositionDual (F : SphericalFusion C) (X : C)
    (i s : F.Label) :
    (∑ a, (leftDuality (F.simple i) X (F.simple s)).symm
        (F.simpleHomBasis (X ⊗ F.simple s) i a) ≫
      leftBendAdjoint F.toPivotal
        (F.compositionDual (F.simpleHomBasis (X ⊗ F.simple s) i) a)) =
      (F.dimension (F.simple i) / F.dimension (F.simple s)) •
        F.simpleProjector s (Xᘁ ⊗ F.simple i) := by
  let b := F.simpleHomBasis (X ⊗ F.simple s) i
  have hb (a) : leftBendAdjoint F.toPivotal (F.compositionDual b a) =
      F.dimension (F.simple i) •
        F.traceDualBasis (b.map (leftDuality (F.simple i) X (F.simple s)).symm) a := by
    rw [traceDualBasis_leftBend]
    simp [SphericalFusion.compositionDual, leftBendAdjoint]
  change (∑ a, _ ≫ leftBendAdjoint F.toPivotal (F.compositionDual b a)) = _
  simp only [hb, Linear.comp_smul, ← Finset.smul_sum]
  have h := sum_basis_comp_traceDual F (Xᘁ ⊗ F.simple i) s
    (b.map (leftDuality (F.simple i) X (F.simple s)).symm)
  simp only [Module.Basis.map_apply] at h
  rw [h, smul_smul, div_eq_mul_inv]

/-- The open bent channel used to sew the second mixed-object label. -/
def bentChannelSewing (F : SphericalFusion C) (X : C) (i s : F.Label) :
    Xᘁ ⊗ F.simple i ⟶ Xᘁ ⊗ F.simple i :=
  ∑ a, (leftDuality (F.simple i) X (F.simple s)).symm
      (F.simpleHomBasis (X ⊗ F.simple s) i a) ≫
    leftBendAdjoint F.toPivotal
      (F.compositionDual (F.simpleHomBasis (X ⊗ F.simple s) i) a)

/-- One complete S-weighted sewing sum is a genuine monodromy loop.
No modularity or fusion structure on the center is needed. -/
theorem sum_S_bentChannelSewing (F : SphericalFusion C) (X : C)
    (i r : F.Label) :
    (∑ s, (categoricalS F r s / F.dimension (F.simple i)) •
      bentChannelSewing F X i s) =
      monodromyLoop F.toPivotal (F.simple r)ᘁ (Xᘁ ⊗ F.simple i) := by
  simp only [bentChannelSewing, sum_leftBend_compositionDual, smul_smul]
  rw [monodromyLoop_eq_sum_projectors]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  field_simp [F.dimension_simple_ne_zero]

/-- The same sewing formula with the exact second-factor coefficient in
`mixedExchangeCoefficient`, including its dual-label convention. -/
theorem sum_dual_S_bentChannelSewing (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (X : C) (i b : F.Label) :
    (∑ s, (categoricalS F (F.dualLabel s) b / F.dimension (F.simple i)) •
      bentChannelSewing F X i s) =
      monodromyLoop F.toPivotal (F.simple (F.dualLabel b))ᘁ
        (Xᘁ ⊗ F.simple i) := by
  simp_rw [categoricalS_dual_left F R, categoricalS_symm F R _ (F.dualLabel b)]
  exact sum_S_bentChannelSewing F X i (F.dualLabel b)

end VOA.Huang.NSCongruence
