import VOA.Examples.AffineSl2JointPBW
import VOA.Filtered.AffineInfiniteClassicalFreeness
import VOA.Filtered.LiPBWCoordinates
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Unconditional PBW coordinates of the universal affine Li algebra

The all-depth straightening theorem and the proved current PBW basis identify
independent exact-depth classes in the genuine Li associated graded.
-/
namespace VOA.AffineSl2GeneralRigidity
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CurrentLi
open VOA.AffineSl2UniversalC2PBW VOA.AffineSl2PBWWakimotoReduction
open scoped BigOperators DirectSum
noncomputable section
variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The actual PBW basis vectors coincide with the original ordered creation states. -/
theorem currentPBWBasis_eq_orderedCreationState (mu : CurrentIndex) :
    currentPBWBasis k hk mu = orderedCreationState k mu := by
  rw [currentPBWBasis_apply,orderedCreationState_eq_wordStateA]

/-- The exposed PBW depth is exactly the total ordinary jet order in the ordered word. -/
theorem orderedCreationDepth_eq_pairsLevel (mu : CurrentIndex) :
    orderedCreationDepth mu = pairsLevel (orderedPBWColorWord mu) := by
  change ((mu.support.sort (fun a b => a ≤ b)).flatMap
      (fun q => List.replicate (mu q) q) |>.map (fun q => (ofLex q).2)).sum =
    pairsLevel (orderedPBWColorWord mu)
  simp only [orderedPBWColorWord,pairsLevel,List.map_flatMap,List.map_replicate]

/-- The Li filtration is the actual PBW basis span at or above the specified depth. -/
theorem liFiltration_eq_currentPBWDepthSpan (p : ℕ) :
    liFiltration (universal k hk) p = Submodule.span ℂ
      (currentPBWBasis k hk '' {mu | p ≤ orderedCreationDepth mu}) := by
  rw [liFiltration_eq_orderedDepthSpan k hk p]
  congr 1
  ext x
  constructor <;> rintro ⟨mu,hmu,rfl⟩
  · exact ⟨mu,hmu,currentPBWBasis_eq_orderedCreationState k hk mu⟩
  · exact ⟨mu,hmu,(currentPBWBasis_eq_orderedCreationState k hk mu).symm⟩

/-- The nonnegative conformal weight of an ordered current PBW word. -/
def currentPBWConformalWeight (mu : CurrentIndex) : ℕ :=
  wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) (orderedPBWColorWord mu))

/-- Each true PBW basis vector belongs to its exact depth and conformal piece. -/
theorem currentPBWBasis_mem_liWeightPiece (mu : CurrentIndex) :
    currentPBWBasis k hk mu ∈ liWeightPiece (universal k hk)
      (orderedCreationDepth mu) (currentPBWConformalWeight k mu) := by
  rw [currentPBWBasis_apply,orderedCreationDepth_eq_pairsLevel,
    wordStateA_eq_generatorWord k hk]
  exact generatorWord_mem_liWeightPiece (universal k hk) (currentState k)
    (fun _ : Fin 3 => 1) (currentState_mem_grading k hk) _

/-- The homogeneous symbols of all actual current PBW monomials are independent. -/
theorem currentPBWLiClasses_linearIndependent :
    LinearIndependent ℂ (fun mu : CurrentIndex =>
      liHomogeneousClass (universal k hk) (orderedCreationDepth mu) (currentPBWConformalWeight k mu)
        ⟨currentPBWBasis k hk mu,currentPBWBasis_mem_liWeightPiece k hk mu⟩) :=
  liBasisClass_linearIndependent (universal k hk) (currentPBWBasis k hk)
    orderedCreationDepth (liFiltration_eq_currentPBWDepthSpan k hk)
    (currentPBWConformalWeight k) (currentPBWBasis_mem_liWeightPiece k hk)

/-- The free polynomial jet map, indexed in PBW lexicographic coordinates. -/
def universalLexJetMap : MvPolynomial (Fin 3 ×ₗ ℕ) ℂ →ₐ[ℂ] liAssociatedGraded (universal k hk) :=
  MvPolynomial.aeval (fun q => FiniteJet.dividedIterate
    (liAssociatedGradedTranslation (universal k hk)) (ofLex q).2
    (affineCurrentLiClass k hk (ofLex q).1))

private theorem orderedWord_prod (mu : CurrentIndex)
    {A : Type*} [CommMonoid A] (f : Fin 3 × ℕ → A) :
    ((orderedPBWColorWord mu).map f).prod = ∏ q ∈ mu.support, (f (ofLex q))^(mu q) := by
  classical
  have hprod (l : List (Fin 3 ×ₗ ℕ)) :
      ((l.flatMap (fun q => List.replicate (mu q) (ofLex q))).map f).prod =
        (l.map (fun q => f (ofLex q)^mu q)).prod := by
    induction l with
    | nil => simp
    | cons q l ih => simp only [List.flatMap_cons, List.map_append, List.prod_append,
        List.map_replicate, List.prod_replicate, ih, List.map_cons, List.prod_cons]
  rw [show orderedPBWColorWord mu =
    (mu.support.sort (fun a b => a ≤ b)).flatMap
      (fun q => List.replicate (mu q) (ofLex q)) from rfl, hprod]
  rw [← List.prod_toFinset (fun q : Fin 3 ×ₗ ℕ => f (ofLex q)^mu q)
    (Finset.sort_nodup _ _)]
  simp

set_option maxHeartbeats 800000 in
/-- A polynomial monomial maps to the genuine exact-depth class of its PBW basis vector. -/
theorem universalLexJetMap_monomial (mu : CurrentIndex) :
    universalLexJetMap k hk (MvPolynomial.monomial mu 1) =
      liHomogeneousClass (universal k hk) (orderedCreationDepth mu) (currentPBWConformalWeight k mu)
        ⟨currentPBWBasis k hk mu,currentPBWBasis_mem_liWeightPiece k hk mu⟩ := by
  classical
  have heval : universalLexJetMap k hk (MvPolynomial.monomial mu 1) =
      ((orderedPBWColorWord mu).map (fun q => FiniteJet.dividedIterate
        (liAssociatedGradedTranslation (universal k hk)) q.2 (affineCurrentLiClass k hk q.1))).prod := by
    rw [orderedWord_prod]
    simp only [universalLexJetMap, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
  rw [heval]
  rw [show affineCurrentLiClass k hk = (fun i => liDegreeZeroClass (universal k hk) 1
      ⟨currentState k i,currentState_mem_grading k hk i⟩) from rfl]
  rw [prod_dividedIterate_degreeZeroClass_eq_generatorWord (universal k hk)
    (currentState k) (fun _ : Fin 3 => 1) (currentState_mem_grading k hk)]
  have hd := orderedCreationDepth_eq_pairsLevel mu
  simp only [currentPBWBasis_apply, wordStateA_eq_generatorWord k hk]
  exact liHomogeneousClass_reindex (universal k hk) hd.symm rfl _ _

/-- Unconditional injectivity of the universal affine polynomial jet map. -/
theorem universalLexJetMap_injective : Function.Injective (universalLexJetMap k hk) := by
  apply LinearMap.injective_of_linearIndependent
    (f := (universalLexJetMap k hk).toLinearMap)
    (MvPolynomial.basisMonomials (Fin 3 ×ₗ ℕ) ℂ).span_eq
  have h := currentPBWLiClasses_linearIndependent k hk
  convert h using 1
  funext mu
  exact universalLexJetMap_monomial k hk mu

/-- The universal map in ordinary, rather than lexicographic, jet coordinates. -/
def universalJetMap : InfiniteJet.JetPoly ℂ (Fin 3) →ₐ[ℂ]
    liAssociatedGraded (universal k hk) :=
  InfiniteJet.derivationJetEval (liAssociatedGradedTranslation (universal k hk))
    (affineCurrentLiClass k hk)

theorem universalJetMap_eq_lex : universalJetMap k hk =
    (universalLexJetMap k hk).comp (MvPolynomial.rename toLex) := by
  apply MvPolynomial.algHom_ext
  intro q
  simp [universalJetMap, universalLexJetMap, InfiniteJet.derivationJetEval]

/-- The genuine universal affine jet map is injective at every depth. -/
theorem universalJetMap_injective : Function.Injective (universalJetMap k hk) := by
  rw [universalJetMap_eq_lex]
  exact (universalLexJetMap_injective k hk).comp
    (MvPolynomial.rename_injective toLex (fun _ _ h => h))

/-- Current-word generation makes the genuine universal affine jet map surjective. -/
theorem universalJetMap_surjective : Function.Surjective (universalJetMap k hk) := by
  intro z
  obtain ⟨a,ha⟩ := affine_liInfinitePresentedJetMap_surjective k hk ⊥ bot_le z
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨f,ha⟩

/-- Universal affine PBW gives a genuine polynomial-jet/Li algebra equivalence. -/
def universalJetAlgEquiv : InfiniteJet.JetPoly ℂ (Fin 3) ≃ₐ[ℂ]
    liAssociatedGraded (universal k hk) :=
  AlgEquiv.ofBijective (universalJetMap k hk)
    ⟨universalJetMap_injective k hk,universalJetMap_surjective k hk⟩

end
end VOA.AffineSl2GeneralRigidity
