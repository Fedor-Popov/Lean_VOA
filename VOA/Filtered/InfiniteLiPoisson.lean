import VOA.Commutative.InfiniteJetPoissonUniqueness
import VOA.Filtered.InfiniteLiDifferential
import VOA.Filtered.LiC2Bridge

/-!
# Poisson vertex compatibility of the canonical arc-to-Li map

A candidate arc Poisson vertex structure is tested only on the original generators:
its zero products are the base Poisson brackets and its positive base products vanish.
All derivative and polynomial products then follow from the intrinsic generator test.
No bijectivity of the canonical map is needed for this compatibility theorem.
-/
namespace VOA
noncomputable section
variable {σ V : Type*} [AddCommGroup V] [Module ℂ V]

@[simp] theorem liInfinitePresentedJetMap_generator_zero (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) (i : σ) :
    liInfinitePresentedJetMap W x I hI (InfiniteJet.generator I i 0) = x i := by
  unfold liInfinitePresentedJetMap InfiniteJet.generator
  rw [InfiniteJet.presentedJetToDifferentialAlgebra_X]
  simp [FiniteJet.dividedIterate]

/-- The canonical arc map restricts to the prescribed polynomial map in order zero. -/
theorem liInfinitePresentedJetMap_basePolynomial (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) (f : MvPolynomial σ ℂ) :
    liInfinitePresentedJetMap W x I hI (MvPolynomial.aeval (fun i => InfiniteJet.generator I i 0) f) =
      MvPolynomial.aeval x f := by
  have h : (liInfinitePresentedJetMap W x I hI).comp
      (MvPolynomial.aeval (fun i => InfiniteJet.generator I i 0)) = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact DFunLike.congr_fun h f

/-- Actual Poisson vertex compatibility follows from the base Poisson normalization.
The only operation assumptions concern order-zero generators. -/
def liInfinitePresentedJetPoissonHom (W : VertexOperatorAlgebra V)
    (weight : σ → ℕ) (a : ∀ i, W.grading (weight i : ℤ))
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval (fun i => liDegreeZeroClass W (weight i) (a i))).toRingHom)
    (P : PoissonVertexAlgebra (InfiniteJet.PresentedJet I))
    (hT : P.translation = InfiniteJet.translation I)
    (r : σ → σ → MvPolynomial σ ℂ)
    (hbase : ∀ i j, P.mode 0 (InfiniteJet.generator I i 0) (InfiniteJet.generator I j 0) =
      MvPolynomial.aeval (fun k => InfiniteJet.generator I k 0) (r i j))
    (hpositive : ∀ i j n, P.mode (n+1) (InfiniteJet.generator I i 0) (InfiniteJet.generator I j 0) = 0)
    (hbracket : ∀ i j, liAssociatedGradedMode W 0 (liDegreeZeroClass W (weight i) (a i))
      (liDegreeZeroClass W (weight j) (a j)) =
      MvPolynomial.aeval (fun k => liDegreeZeroClass W (weight k) (a k)) (r i j)) :
    PoissonVertexAlgebra.Hom P (liPoissonVertexAlgebra W) := by
  let x := fun i => liDegreeZeroClass W (weight i) (a i)
  let F := liInfinitePresentedJetMap W x I hI
  apply InfiniteJet.poissonVertexHomOfBaseGenerators I P (liPoissonVertexAlgebra W) F hT
  · intro y
    rw [hT]
    exact liInfinitePresentedJetMap_translation W x I hI y
  · intro i j n
    change F (P.mode n (InfiniteJet.generator I i 0) (InfiniteJet.generator I j 0)) =
      liAssociatedGradedMode W n (F (InfiniteJet.generator I i 0)) (F (InfiniteJet.generator I j 0))
    change liInfinitePresentedJetMap W x I hI _ = liAssociatedGradedMode W n
      (liInfinitePresentedJetMap W x I hI _) (liInfinitePresentedJetMap W x I hI _)
    rw [liInfinitePresentedJetMap_generator_zero, liInfinitePresentedJetMap_generator_zero]
    cases n with
    | zero => rw [hbase, liInfinitePresentedJetMap_basePolynomial]; exact (hbracket i j).symm
    | succ n =>
        rw [hpositive, map_zero]
        exact (liDegreeZeroClass_mode_succ W (weight i) (weight j) n (a i) (a j)).symm

end
end VOA
