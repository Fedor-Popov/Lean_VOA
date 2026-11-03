import VOA.Huang.NSSMove2Diagrams

/-! # A diagonal trace contraction of the inverse channel crossing -/
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

/-- Closing one projected inverse half-braiding gives the central curl between
the same inclusion and projection. Neither map need be a central morphism. -/
theorem inverseCrossing_partialTrace (F : SphericalFusion C) (A : Center C)
    (U : C) (q : U ⟶ A.1) (p : A.1 ⟶ U) :
    F.toPivotal.partialTraceLeft U (U ◁ q ≫ (A.2.β U).inv ≫ p ▷ U) =
      q ≫ centralDrinfeldMorphism A ≫ (F.j A.1).inv ≫ p := by
  rw [← Category.assoc, ← F.partialTraceLeft_dinatural p]
  rw [← whisker_exchange_assoc, ← halfBraiding_inv_naturality A p]
  rw [F.toPivotal.partialTraceLeft_precomp, F.toPivotal.partialTraceLeft_postcomp,
    ← centralDrinfeld_comp_j_inv]
  simp only [Category.assoc]

/-- An actual categorical trace of the `NSSMove2` morphism, with the residual
central curl made explicit. -/
theorem inverseChannelCrossing_diagonal_trace (F : SphericalFusion C)
    (A : Center C) (i : F.Label) :
    F.scalarTrace (F.simple i ⊗ F.simple i) (inverseChannelCrossing F A i i) =
      (F.dimension (F.simple i))⁻¹ * ∑ β,
        F.scalarTrace (F.simple i)
          (F.simpleHomBasis A.1 i β ≫ centralDrinfeldMorphism A ≫
            (F.j A.1).inv ≫ F.compositionDual (F.simpleHomBasis A.1 i) β) := by
  simp only [inverseChannelCrossing, map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro β _
  rw [← F.scalarTrace_partialTraceLeft, inverseCrossing_partialTrace]

/-- Exact diagonal contraction for a central object with a pinned twist. -/
theorem inverseChannelCrossing_diagonal_scalar (F : SphericalFusion C)
    (A : Center C) (i : F.Label) {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j A.1).hom = t • centralDrinfeldMorphism A) :
    F.scalarTrace (F.simple i ⊗ F.simple i) (inverseChannelCrossing F A i i) =
      t⁻¹ * (Module.finrank ℂ (F.simple i ⟶ A.1) : ℂ) := by
  have hu : centralDrinfeldMorphism A ≫ (F.j A.1).inv = t⁻¹ • 𝟙 A.1 := by
    have hh : t • (centralDrinfeldMorphism A ≫ (F.j A.1).inv) = 𝟙 A.1 := by
      rw [← Linear.smul_comp, ← hj, Iso.hom_inv_id]
    rw [← hh, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have he (β) :
      F.simpleHomBasis A.1 i β ≫ centralDrinfeldMorphism A ≫
        (F.j A.1).inv ≫ F.compositionDual (F.simpleHomBasis A.1 i) β =
          t⁻¹ • 𝟙 (F.simple i) := by
    rw [← Category.assoc (centralDrinfeldMorphism A) (F.j A.1).inv, hu]
    simp [F.basis_comp_compositionDual]
  rw [inverseChannelCrossing_diagonal_trace]
  simp only [he, map_smul, F.scalarTrace_id, smul_eq_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [F.dimension_simple_ne_zero i]

/-- A genuine degree-one indicator is the diagonal trace of the explicit
inverse crossing for every mixed object. No diagram residual is assumed. -/
theorem mixed_inverseChannelCrossing_diagonal_indicator
    (F : SphericalFusion C) (M : Modular F) (a b i : F.Label) :
    F.scalarTrace (F.simple i ⊗ F.simple i)
        (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i i) =
      generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b))
        (F.simple i) 0 1 := by
  have ht : M.twistScalar a / M.twistScalar b ≠ 0 :=
    div_ne_zero (M.toRibbon.twistScalar_ne_zero a) (M.toRibbon.twistScalar_ne_zero b)
  rw [inverseChannelCrossing_diagonal_scalar F _ i ht (mixedTwistIdentity_holds F M a b),
    generalizedIndicatorInt_one_scalar F _ _ ht (mixedTwistIdentity_holds F M a b) 1,
    F.finrank_hom_symm]
  simp

/-- At block sizes `(1,1)`, the off-diagonal exterior closures vanish. -/
theorem twoBlockClosure_zero_zero_offDiagonal (F : SphericalFusion C) (V : C)
    (i j : F.Label) (hij : i ≠ j)
    (f : F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i) :
    twoBlockClosure F V 0 0 i j f = 0 := by
  have hR : (blockReassociation V 0 0).hom = 𝟙 (V ⊗ V) := by
    simp [blockReassociation, tensorPower]
  simp only [twoBlockClosure, LinearMap.coe_mk, AddHom.coe_mk, hR,
    tensorPower, Category.comp_id]
  apply Finset.sum_eq_zero
  intro α _
  apply Finset.sum_eq_zero
  intro β _
  erw [F.scalarTrace_comp_comm]
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  erw [F.hom_simple_eq_zero (Ne.symm hij)
    (F.simpleHomBasis V j α ≫ F.compositionDual (F.simpleHomBasis V i) β)]
  simp

/-- At block sizes `(1,1)`, each surviving closure counts one copy per
simple-source basis vector, rather than the square of that multiplicity. -/
theorem twoBlockClosure_zero_zero_diagonal (F : SphericalFusion C) (V : C)
    (i : F.Label) (f : F.simple i ⊗ F.simple i ⟶ F.simple i ⊗ F.simple i) :
    twoBlockClosure F V 0 0 i i f =
      (Module.finrank ℂ (F.simple i ⟶ V) : ℂ) *
        F.scalarTrace (F.simple i ⊗ F.simple i) f := by
  have hR : (blockReassociation V 0 0).hom = 𝟙 (V ⊗ V) := by
    simp [blockReassociation, tensorPower]
  simp only [twoBlockClosure, LinearMap.coe_mk, AddHom.coe_mk, hR,
    tensorPower, Category.comp_id]
  have he (α β : Fin (Module.finrank ℂ (F.simple i ⟶ V))) :
      F.scalarTrace (V ⊗ V)
        ((F.compositionDual (F.simpleHomBasis V i) β ⊗ₘ
          F.compositionDual (F.simpleHomBasis V i) α) ≫ f ≫
          (F.simpleHomBasis V i α ⊗ₘ F.simpleHomBasis V i β)) =
        if α = β then F.scalarTrace (F.simple i ⊗ F.simple i) f else 0 := by
    rw [F.scalarTrace_comp_comm]
    simp only [Category.assoc, tensorHom_comp_tensorHom]
    rw [F.basis_comp_compositionDual (F.simpleHomBasis V i) β α,
      F.basis_comp_compositionDual (F.simpleHomBasis V i) α β]
    split_ifs <;> simp_all
  change (∑ α : Fin (Module.finrank ℂ (F.simple i ⟶ V)),
    ∑ β : Fin (Module.finrank ℂ (F.simple i ⟶ V)),
      F.scalarTrace (V ⊗ V)
        ((F.compositionDual (F.simpleHomBasis V i) β ⊗ₘ
          F.compositionDual (F.simpleHomBasis V i) α) ≫ f ≫
          (F.simpleHomBasis V i α ⊗ₘ F.simpleHomBasis V i β))) = _
  simp only [he]
  simp

/-- The positive trace clause at `(m,l)=(1,1)`, for any central source and
any probe object. This is a proved restriction of the two-block obligation. -/
theorem inverseTwoBlockTrace_one_one (F : SphericalFusion C) (A : Center C) (V : C) :
    generalizedIndicatorInt F.toPivotal A V 0 1 =
      ∑ i, ∑ j, twoBlockClosure F V 0 0 i j (inverseChannelCrossing F A i j) := by
  classical
  have hs : (∑ i, ∑ j, twoBlockClosure F V 0 0 i j (inverseChannelCrossing F A i j)) =
      ∑ i, (Module.finrank ℂ (F.simple i ⟶ V) : ℂ) *
        F.scalarTrace (F.simple i ⊗ F.simple i) (inverseChannelCrossing F A i i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i, twoBlockClosure_zero_zero_diagonal]
    · intro j _ hji
      exact twoBlockClosure_zero_zero_offDiagonal F V i j (Ne.symm hji) _
    · simp
  rw [hs, generalizedIndicatorInt_eq_sum_simpleChannels]
  simp only [tensorPower]
  simp_rw [inverseChannelCrossing_diagonal_trace]
  apply Finset.sum_congr rfl
  intro i _
  have he (β : Fin (Module.finrank ℂ (F.simple i ⟶ A.1)))
      (α : Fin (Module.finrank ℂ (F.simple i ⟶ V))) :
      F.scalarTrace A.1
        (generalizedRotation F.toPivotal A V 0
          (F.compositionDual (F.simpleHomBasis A.1 i) β ≫ F.simpleHomBasis V i α) ≫
          F.compositionDual (F.simpleHomBasis V i) α ≫ F.simpleHomBasis A.1 i β) =
      F.scalarTrace (F.simple i)
        (F.simpleHomBasis A.1 i β ≫ centralDrinfeldMorphism A ≫
          (F.j A.1).inv ≫ F.compositionDual (F.simpleHomBasis A.1 i) β) := by
    rw [generalizedRotation_one_centralDrinfeld]
    simp only [Category.assoc]
    rw [← Category.assoc (F.simpleHomBasis V i α)
        (F.compositionDual (F.simpleHomBasis V i) α),
      F.basis_comp_compositionDual]
    simp only [ite_true, Category.id_comp]
    simpa only [Category.assoc] using
      (F.scalarTrace_comp_comm (F.simpleHomBasis A.1 i β)
        (centralDrinfeldMorphism A ≫ (F.j A.1).inv ≫
          F.compositionDual (F.simpleHomBasis A.1 i) β)).symm
  change (∑ β : Fin (Module.finrank ℂ (F.simple i ⟶ A.1)),
    ∑ α : Fin (Module.finrank ℂ (F.simple i ⟶ V)),
      (F.dimension (F.simple i))⁻¹ * F.scalarTrace A.1
        (generalizedRotation F.toPivotal A V 0
          (F.compositionDual (F.simpleHomBasis A.1 i) β ≫ F.simpleHomBasis V i α) ≫
          F.compositionDual (F.simpleHomBasis V i) α ≫ F.simpleHomBasis A.1 i β)) = _
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Finset.mul_sum]

/-- The first conjunct of `MixedTwoBlockTraceFormula` at `n=k=0`. -/
def MixedInverseOneOneTrace (F : SphericalFusion C) : Prop :=
  ∀ (V : C) (a b : F.Label),
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b)) V 0 1 =
      ∑ i, ∑ j, twoBlockClosure F V 0 0 i j
        (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j)

theorem mixedInverseOneOneTrace_holds (F : SphericalFusion C) :
    MixedInverseOneOneTrace F := fun V a b =>
      inverseTwoBlockTrace_one_one F (mixedCenter (F.simple a) (F.simple b)) V

theorem mixedInverseOneOneTrace_of_twoBlock (F : SphericalFusion C)
    (h : MixedTwoBlockTraceFormula F) : MixedInverseOneOneTrace F :=
  fun V a b => (h V 0 0 a b).1

/-- A full turn in degree `n+1` has the same trace as one rotation of the
single object `V^(n+1)`. -/
theorem indicator_fullTurn_eq_one (F : SphericalFusion C) (A : Center C)
    (V : C) (n : ℕ) :
    generalizedIndicatorInt F.toPivotal A V n (n + 1) =
      generalizedIndicatorInt F.toPivotal A (tensorPower V (n + 1)) 0 1 := by
  unfold generalizedIndicatorInt
  congr 1
  ext f
  change ((generalizedRotation F.toPivotal A V n) ^ ((n + 1 : ℕ) : ℤ)) f =
    generalizedRotation F.toPivotal A (tensorPower V (n + 1)) 0 f
  rw [zpow_natCast, LinearEquiv.pow_apply, generalizedRotation_iterate_full,
    generalizedRotation_one_centralDrinfeld]

/-- The positive trace clause on every diagonal, with arbitrary central
source and probe. This does not cover the off-diagonal NS residual. -/
theorem inverseTwoBlockTrace_diagonal (F : SphericalFusion C) (A : Center C)
    (V : C) (n : ℕ) :
    generalizedIndicatorInt F.toPivotal A V n (n + 1) =
      ∑ i, ∑ j, twoBlockClosure F V n n i j (inverseChannelCrossing F A i j) := by
  rw [indicator_fullTurn_eq_one, inverseTwoBlockTrace_one_one]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [twoBlockClosure, blockReassociation, tensorPower]

/-- The first conjunct of `MixedTwoBlockTraceFormula`, restricted to `n=k`. -/
def MixedInverseDiagonalTrace (F : SphericalFusion C) : Prop :=
  ∀ (V : C) (n : ℕ) (a b : F.Label),
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b)) V n
        (n + 1) =
      ∑ i, ∑ j, twoBlockClosure F V n n i j
        (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j)

theorem mixedInverseDiagonalTrace_holds (F : SphericalFusion C) :
    MixedInverseDiagonalTrace F := fun V n a b =>
      inverseTwoBlockTrace_diagonal F (mixedCenter (F.simple a) (F.simple b)) V n

theorem mixedInverseDiagonalTrace_of_twoBlock (F : SphericalFusion C)
    (h : MixedTwoBlockTraceFormula F) : MixedInverseDiagonalTrace F :=
  fun V n a b => (h V n n a b).1

end VOA.Huang.NSCongruence
