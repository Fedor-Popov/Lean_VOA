import VOA.Huang.NSSMoveAssembly

/-! # The remaining S move as an explicit mixed Fourier identity

This exposes the finite sum needed by the dual-basis proof. It uses only the
S matrix of the base modular category; no centre exhaustion is required.
The Fourier identity itself remains an explicit hypothesis.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- At any integer row, the S move is exactly the coefficient identity with
the factorization of the mixed S matrix from NS (6.1). -/
theorem mixedSMove_iff_factorized (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label) (m l : ℤ) :
    (∀ z, mixedRow F a l (-m) z =
      mixedRow F a m l (mixedRepresentation ρ ModularGroup.S⁻¹ z)) ↔
    ∀ i j : F.Label,
      generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) m l =
        ∑ q : F.Label × F.Label,
          (F.globalDimension⁻¹ * categoricalS F q.1 i * categoricalS F (F.dualLabel q.2) j) *
            generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2))
              (F.simple a) l (-m) := by
  have hc (z : F.Label × F.Label → ℂ) :
      mixedRepresentation ρ ModularGroup.S⁻¹ (mixedRepresentation ρ ModularGroup.S z) = z := by
    rw [map_inv]
    exact (mixedRepresentation ρ ModularGroup.S).symm_apply_apply z
  have hd (z : F.Label × F.Label → ℂ) :
      mixedRepresentation ρ ModularGroup.S (mixedRepresentation ρ ModularGroup.S⁻¹ z) = z := by
    rw [map_inv]
    exact (mixedRepresentation ρ ModularGroup.S).apply_symm_apply z
  have hb (i j : F.Label) :
      mixedRow F a l (-m) (mixedRepresentation ρ ModularGroup.S (Pi.single (i,j) 1)) =
        ∑ q : F.Label × F.Label,
          (F.globalDimension⁻¹ * categoricalS F q.1 i * categoricalS F (F.dualLabel q.2) j) *
            generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2))
              (F.simple a) l (-m) := by
    rw [mixedRepresentation_S F M ρ hr, Matrix.mulVec_single_one]
    simp only [mixedRow, equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.col_apply, mixedFamily]
    apply Finset.sum_congr rfl
    intro q _
    rw [show mixedS F M q (i,j) = F.globalDimension⁻¹ * categoricalS F q.1 i *
      categoricalS F (F.dualLabel q.2) j from mixedS_apply F M q.1 q.2 i j]
  constructor
  · intro h i j
    have he := h (mixedRepresentation ρ ModularGroup.S (Pi.single (i,j) 1))
    rw [hc, hb] at he
    simpa only [mixedRow, equivariantIndicator_basis, mixedFamily] using he.symm
  · intro h
    have he : mixedRow F a m l = (mixedRow F a l (-m)).comp
        (mixedRepresentation ρ ModularGroup.S).toLinearMap := by
      apply (Pi.basisFun ℂ (F.Label × F.Label)).ext
      intro p
      simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      change mixedRow F a m l (Pi.single p 1) =
        mixedRow F a l (-m) (mixedRepresentation ρ ModularGroup.S (Pi.single p 1))
      rw [hb p.1 p.2]
      simpa only [mixedRow, equivariantIndicator_basis, mixedFamily] using h p.1 p.2
    intro z
    have hx := congrArg (fun f : (F.Label × F.Label → ℂ) →ₗ[ℂ] ℂ =>
      f (mixedRepresentation ρ ModularGroup.S⁻¹ z)) he
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hd] using hx.symm

/-- An explicit representation-free categorical residual for the positive-product,
off-diagonal rows. This is the finite-sum identity still to be proved. -/
def MixedSameSignOffDiagonalFourier (F : SphericalFusion C) : Prop :=
  ∀ (a : F.Label) (m l : ℤ), 0 < m * l → m ≠ l → IsCoprime m l →
    ∀ i j : F.Label,
      generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) m l =
        ∑ q : F.Label × F.Label,
          (F.globalDimension⁻¹ * categoricalS F q.1 i * categoricalS F (F.dualLabel q.2) j) *
            generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2))
              (F.simple a) l (-m)

/-- The explicit finite-sum identity is sufficient for the entire original target. -/
theorem mixedNonzeroSMove_of_factorized (F : SphericalFusion C) (M : Modular F)
    (h : MixedSameSignOffDiagonalFourier F) : MixedNonzeroSMove F M := by
  apply mixedNonzeroSMove_of_sameSignOffDiagonal F M
  intro ρ hr a m l hp hne hcop
  exact (mixedSMove_iff_factorized F M ρ hr a m l).mpr (h a m l hp hne hcop)

/-- With a supplied modular lift, the finite-sum residual is also necessary. -/
theorem factorized_of_mixedNonzeroSMove (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (h : MixedNonzeroSMove F M) :
    MixedSameSignOffDiagonalFourier F := by
  intro a m l hp _ hcop
  apply (mixedSMove_iff_factorized F M ρ hr a m l).mp
  exact (mixedNonzeroSMove_iff_sameSign F M).mp h ρ hr a m l hp hcop

end VOA.Huang.NSCongruence
