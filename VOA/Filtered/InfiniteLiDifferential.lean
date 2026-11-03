import VOA.Commutative.InfiniteJetDifferential
import VOA.Filtered.InfiniteClassicalFreeness

/-!
# Translation compatibility of the canonical arc-to-Li map

The source translation is constructed from the jet variables and descended through the
proved stable relation ideal. Thus the compatibility below is an identity of independently
constructed operators, not an extra assumption in classical freeness.
-/

namespace VOA

variable {σ V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The canonical arc-to-Li map intertwines the genuine jet translation and Li translation. -/
theorem liInfinitePresentedJetMap_translation (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (a : InfiniteJet.PresentedJet (R := ℂ) I) :
    liInfinitePresentedJetMap W x I hI (InfiniteJet.translation I a) =
      liAssociatedGradedTranslation W (liInfinitePresentedJetMap W x I hI a) :=
  InfiniteJet.presentedJetToDifferentialAlgebra_translation _ _ _ _ _ _ _

/-- Bijective canonical arc-to-Li maps yield algebra equivalences. -/
noncomputable def liArcAlgEquiv (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hfree : LiPresentationClassicallyFree W x I hI) :
    InfiniteJet.PresentedJet (R := ℂ) I ≃ₐ[ℂ] liAssociatedGraded W :=
  AlgEquiv.ofBijective (liInfinitePresentedJetMap W x I hI) hfree

/-- The inverse algebra equivalence also intertwines translation. -/
theorem liArcAlgEquiv_symm_translation (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hfree : LiPresentationClassicallyFree W x I hI) (b : liAssociatedGraded W) :
    (liArcAlgEquiv W x I hI hfree).symm (liAssociatedGradedTranslation W b) =
      InfiniteJet.translation I ((liArcAlgEquiv W x I hI hfree).symm b) := by
  apply (liArcAlgEquiv W x I hI hfree).injective
  rw [AlgEquiv.apply_symm_apply]
  change liAssociatedGradedTranslation W b =
    liInfinitePresentedJetMap W x I hI
      (InfiniteJet.translation I ((liArcAlgEquiv W x I hI hfree).symm b))
  rw [liInfinitePresentedJetMap_translation]
  exact congrArg (liAssociatedGradedTranslation W)
    ((liArcAlgEquiv W x I hI hfree).apply_symm_apply b).symm

end VOA
