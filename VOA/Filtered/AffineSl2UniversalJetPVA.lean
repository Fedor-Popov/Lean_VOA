import VOA.Filtered.AffineSl2UniversalLiPBW
import VOA.Filtered.LiC2Bridge
import VOA.Commutative.PoissonVertexTransport
import VOA.Commutative.InfiniteJetDifferential
import VOA.Commutative.BoundaryArcHamiltonian
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The unconditional universal sl2 jet Poisson vertex algebra

Universal affine PBW identifies the free polynomial jet algebra with the genuine
universal Li algebra. This construction uses no boundary quotient, character
formula, or classical-freeness assumption. Translation is the actual jet derivative.
-/
namespace VOA.AffineSl2GeneralRigidity
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CurrentLi
open VOA.AffineSl2UniversalC2PBW
open scoped BigOperators
noncomputable section
variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- Reorder jet colors into the geometric coordinate order e,h,f. -/
def paperJetAlgEquiv : InfiniteJet.JetPoly ℂ (Fin 3) ≃ₐ[ℂ]
    liAssociatedGraded (universal k hk) :=
  (MvPolynomial.renameEquiv ℂ (symbolToCurrentColor.prodCongr (Equiv.refl ℕ))).trans
    (universalJetAlgEquiv k hk)

theorem paperJetAlgEquiv_eq_eval : (paperJetAlgEquiv k hk).toAlgHom =
    InfiniteJet.derivationJetEval (liAssociatedGradedTranslation (universal k hk))
      (fun i => affineCurrentLiClass k hk (symbolToCurrentColor i)) := by
  apply MvPolynomial.algHom_ext
  intro q
  simp [paperJetAlgEquiv,universalJetAlgEquiv,universalJetMap,
    InfiniteJet.derivationJetEval]

/-- The independently defined jet translation intertwines the genuine Li translation. -/
theorem paperJetAlgEquiv_translation (f : InfiniteJet.JetPoly ℂ (Fin 3)) :
    paperJetAlgEquiv k hk (InfiniteJet.polynomialTranslation f) =
      liAssociatedGradedDerivation (universal k hk) (paperJetAlgEquiv k hk f) := by
  have he := DFunLike.congr_fun (paperJetAlgEquiv_eq_eval k hk)
  rw [show paperJetAlgEquiv k hk (InfiniteJet.polynomialTranslation f) = _ from
    he (InfiniteJet.polynomialTranslation f),show paperJetAlgEquiv k hk f = _ from he f]
  exact InfiniteJet.derivationJetEval_translation _
    (liAssociatedGradedTranslation_leibniz (universal k hk))
    (liAssociatedGradedTranslation_one (universal k hk)) _ f

/-- A genuine PVA on free sl2 polynomial jets, constructed unconditionally from PBW. -/
def universalJetPVA : PoissonVertexAlgebra (InfiniteJet.JetPoly ℂ (Fin 3)) :=
  PoissonVertexAlgebra.transport (liPoissonVertexAlgebra (universal k hk))
    (paperJetAlgEquiv k hk) InfiniteJet.polynomialTranslation
    (paperJetAlgEquiv_translation k hk)

@[simp] theorem universalJetPVA_translation : (universalJetPVA k hk).translation =
    InfiniteJet.polynomialTranslation := rfl

/-- The PBW algebra equivalence preserves every genuine nonnegative mode. -/
theorem paperJetAlgEquiv_mode (n : ℕ) (f g : InfiniteJet.JetPoly ℂ (Fin 3)) :
    paperJetAlgEquiv k hk ((universalJetPVA k hk).mode n f g) =
      liAssociatedGradedMode (universal k hk) n
        (paperJetAlgEquiv k hk f) (paperJetAlgEquiv k hk g) :=
  PoissonVertexAlgebra.map_transportedMode _ _ _ _ _

@[simp] theorem paperJetAlgEquiv_X (i : Fin 3) (n : ℕ) :
    paperJetAlgEquiv k hk (MvPolynomial.X (i,n)) =
      FiniteJet.dividedIterate (liAssociatedGradedTranslation (universal k hk)) n
        (affineCurrentLiClass k hk (symbolToCurrentColor i)) := by
  have h := DFunLike.congr_fun (paperJetAlgEquiv_eq_eval k hk) (MvPolynomial.X (i,n))
  simpa [InfiniteJet.derivationJetEval] using h

/-- Positive modes of the original polynomial generators vanish. -/
theorem universalJetPVA_base_succ (i j : Fin 3) (n : ℕ) :
    (universalJetPVA k hk).mode (n+1) (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0)) = 0 := by
  apply (paperJetAlgEquiv k hk).injective
  rw [paperJetAlgEquiv_mode,paperJetAlgEquiv_X,paperJetAlgEquiv_X,map_zero]
  simp only [FiniteJet.dividedIterate, pow_zero, Module.End.one_apply,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  exact liDegreeZeroClass_mode_succ (universal k hk) 1 1 n _ _

/-- The universal current bracket is exactly the sl2 structure-constant bracket. -/
theorem universal_current_poissonBracket (a b : Fin 3) :
    poissonBracket (universal k hk) (currentState k a) (currentState k b) =
      ∑ c : Fin 3, fabc a b c • currentState k c := by
  change (affineSl2VOA_closed k hk).smul (currentState k a) 0 (currentState k b) = _
  rw [smul_currentState_eq_J]
  simpa only [currentState_def] using Vir.J0_current k b a

/-- Exact sl2 brackets between the original current classes in the universal Li algebra. -/
theorem affineCurrentLiClass_mode_zero (a b : Fin 3) :
    liAssociatedGradedMode (universal k hk) 0 (affineCurrentLiClass k hk a)
      (affineCurrentLiClass k hk b) =
      ∑ c : Fin 3, fabc a b c • affineCurrentLiClass k hk c := by
  rw [show affineCurrentLiClass k hk = (fun i => liDegreeZeroClass (universal k hk) 1
    ⟨currentState k i,currentState_mem_grading k hk i⟩) from rfl]
  rw [liDegreeZeroClass_mode_zero (universal k hk) 1 1 (by omega)]
  let x (c : Fin 3) : liWeightPiece (universal k hk) 0 1 :=
    ⟨currentState k c, by
      constructor
      · rw [liFiltration_zero_eq_top]; trivial
      · exact currentState_mem_grading k hk c⟩
  change liHomogeneousClassLinear (universal k hk) 0 1 _ =
    ∑ c : Fin 3, fabc a b c • liHomogeneousClassLinear (universal k hk) 0 1 (x c)
  simp only [← map_smul,← map_sum]
  apply congrArg (liHomogeneousClassLinear (universal k hk) 0 1)
  apply Subtype.ext
  simpa only [Submodule.coe_sum,Submodule.coe_smul,x] using
    universal_current_poissonBracket k hk a b

/-- The PVA on free jets has precisely the geometric sl2 Lie--Poisson bracket on its base. -/
theorem universalJetPVA_base_zero (i j : Fin 3) :
    (universalJetPVA k hk).mode 0 (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0)) =
      InfiniteJet.relationCoefficient (BoundaryAuxiliary.currentPoissonBracket i j) 0 := by
  apply (paperJetAlgEquiv k hk).injective
  rw [paperJetAlgEquiv_mode,paperJetAlgEquiv_X,paperJetAlgEquiv_X]
  simp only [FiniteJet.dividedIterate,pow_zero,Module.End.one_apply,
    Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]
  rw [affineCurrentLiClass_mode_zero]
  fin_cases i <;> fin_cases j <;>
    simp [BoundaryAuxiliary.currentPoissonBracket,InfiniteJet.relationCoefficient,
      Fin.sum_univ_succ,fabc,paperJetAlgEquiv_X,FiniteJet.dividedIterate,smul_eq_mul,
      InfiniteJet.generatorSeries,PowerSeries.constantCoeff_mk,
      show PowerSeries.constantCoeff (2 : PowerSeries (InfiniteJet.JetPoly ℂ (Fin 3))) = 2 from map_ofNat _ 2] <;>
    simp only [map_ofNat, two_smul, two_mul]

end
end VOA.AffineSl2GeneralRigidity
