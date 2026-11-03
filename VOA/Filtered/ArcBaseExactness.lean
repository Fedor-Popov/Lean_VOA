import VOA.Filtered.C2LiAlgebra
import VOA.Filtered.InfiniteLiPoisson
import VOA.Commutative.InfiniteJetBaseEmbedding

/-!
# An injective canonical arc map forces the exact actual C2 presentation

The proof uses the genuine zero-jet embedding and the global C2-to-Li algebra map.
Thus exactness of the base presentation is a consequence of arc injectivity;
it is not an extra representation-theoretic hypothesis.
-/
namespace VOA
noncomputable section
variable {σ V : Type*} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) (weight : σ → ℕ)
    (gen : ∀ i, W.grading (weight i : ℤ))
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval (fun i => mk₂ W (gen i).1)).toRingHom)

include hI in
/-- Any actual C2 relation is also a degree-zero Li relation. -/
theorem liRelations_of_c2Relations : I ≤ RingHom.ker
    (MvPolynomial.aeval (fun i => liDegreeZeroClass W (weight i) (gen i))).toRingHom := by
  intro f hf
  change MvPolynomial.aeval (fun i => liDegreeZeroClass W (weight i) (gen i)) f = 0
  rw [← c2ToLiAlgebra_aeval W weight gen]
  have hz : MvPolynomial.aeval (fun i => mk₂ W (gen i).1) f = 0 := hI hf
  rw [hz,map_zero]

/-- The actual base presentation map into the genuine C2 algebra. -/
def baseC2Map : (MvPolynomial σ ℂ ⧸ I) →ₐ[ℂ] A₂ W :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval (fun i => mk₂ W (gen i).1)) (fun _ hf => hI hf)

/-- The base-to-arc-to-Li map factors through actual C2. -/
theorem baseC2Map_li_commutes
    (hLi : I ≤ RingHom.ker (MvPolynomial.aeval
      (fun i => liDegreeZeroClass W (weight i) (gen i))).toRingHom) :
    (liInfinitePresentedJetMap W (fun i => liDegreeZeroClass W (weight i) (gen i)) I hLi).comp
      (InfiniteJet.baseToJet I) = (c2ToLiAlgebra W).comp (baseC2Map W weight gen I hI) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change liInfinitePresentedJetMap W _ I hLi
      (InfiniteJet.baseToJet I (Ideal.Quotient.mkₐ ℂ I (MvPolynomial.X i))) =
    c2ToLiAlgebra W (baseC2Map W weight gen I hI (Ideal.Quotient.mkₐ ℂ I (MvPolynomial.X i)))
  rw [InfiniteJet.baseToJet_mk_X]
  change liInfinitePresentedJetMap W _ I hLi (InfiniteJet.generator I i 0) = _
  rw [liInfinitePresentedJetMap_generator_zero]
  simp [baseC2Map]

/-- Injectivity of the canonical arc-to-Li map proves exactness of the actual C2 presentation. -/
theorem baseC2Map_injective_of_arc_injective
    (hLi : I ≤ RingHom.ker (MvPolynomial.aeval
      (fun i => liDegreeZeroClass W (weight i) (gen i))).toRingHom)
    (hinj : Function.Injective (liInfinitePresentedJetMap W
      (fun i => liDegreeZeroClass W (weight i) (gen i)) I hLi)) :
    Function.Injective (baseC2Map W weight gen I hI) := by
  intro a b hab
  apply InfiniteJet.baseToJet_injective I
  apply hinj
  have h := baseC2Map_li_commutes W weight gen I hI hLi
  have ha := DFunLike.congr_fun h a
  have hb := DFunLike.congr_fun h b
  change liInfinitePresentedJetMap W _ I hLi (InfiniteJet.baseToJet I a) = _ at ha
  change liInfinitePresentedJetMap W _ I hLi (InfiniteJet.baseToJet I b) = _ at hb
  rw [ha,hb,AlgHom.comp_apply,AlgHom.comp_apply,hab]

/-- A surjective actual C2 presentation and an injective canonical arc map identify the base algebra. -/
def baseC2AlgEquiv_of_arc_injective
    (hLi : I ≤ RingHom.ker (MvPolynomial.aeval
      (fun i => liDegreeZeroClass W (weight i) (gen i))).toRingHom)
    (hinj : Function.Injective (liInfinitePresentedJetMap W
      (fun i => liDegreeZeroClass W (weight i) (gen i)) I hLi))
    (hsurj : Function.Surjective (MvPolynomial.aeval (fun i => mk₂ W (gen i).1) :
      MvPolynomial σ ℂ →ₐ[ℂ] A₂ W)) :
    (MvPolynomial σ ℂ ⧸ I) ≃ₐ[ℂ] A₂ W :=
  AlgEquiv.ofBijective (baseC2Map W weight gen I hI)
    ⟨baseC2Map_injective_of_arc_injective W weight gen I hI hLi hinj,fun z => by
      obtain ⟨f,hf⟩ := hsurj z
      exact ⟨Ideal.Quotient.mkₐ ℂ I f,hf⟩⟩

end
end VOA
