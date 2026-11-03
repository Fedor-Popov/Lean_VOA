import VOA.Filtered.BoundaryArcLiPoisson
import VOA.Filtered.BoundaryArcLiMap
import VOA.Filtered.ArcBaseExactness
import VOA.Commutative.PoissonVertexEquiv

/-! # The actual simple boundary arc-to-Li Poisson vertex map -/
namespace VOA.AffineSl2BoundarySingularFamily
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CurrentLi
noncomputable section
variable {k : ℂ} {m : ℕ} (C : Candidate k m)

/-- The canonical map to the actual simple Li algebra is an intrinsic PVA homomorphism.
Every relation and structure obligation is discharged for the actual candidate. -/
def Candidate.arcLiPoissonHom :
    PoissonVertexAlgebra.Hom (BoundaryAuxiliary.arcPVA m)
      (liPoissonVertexAlgebra (BoundaryArcLiMap.simpleVOA C)) :=
  boundaryArcLiPoissonHom k C.noncritical
    (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k C.noncritical))
    (QuotVOA.maxGradedIdeal_isIdeal _) (QuotVOA.maxGradedIdeal_isGradedIdeal _)
    m (BoundaryArcLiMap.baseIdeal_le_kernel C)

/-- This PVA map is exactly the actual canonical jet evaluation used in the Hilbert squeeze. -/
theorem Candidate.arcLiPoissonHom_mk (f : BoundaryAuxiliary.JetPoly ℂ) :
    C.arcLiPoissonHom.toAlgHom (InfiniteJet.presentedJetMk (BoundaryAuxiliary.baseIdeal m) f) =
      BoundaryArcLiMap.polynomialMap C f := rfl

/-- The actual simple arc-to-Li PVA map is unconditionally onto. -/
theorem Candidate.arcLiPoissonHom_surjective : Function.Surjective C.arcLiPoissonHom.toAlgHom := by
  intro z
  obtain ⟨f,hf⟩ := BoundaryArcLiMap.polynomialMap_surjective C z
  exact ⟨InfiniteJet.presentedJetMk (BoundaryAuxiliary.baseIdeal m) f,hf⟩

/-- The actual C2 relation inclusion in the precise source presentation coordinates. -/
theorem Candidate.baseC2Relations : BoundaryAuxiliary.baseIdeal (R := ℂ) m ≤
    RingHom.ker (MvPolynomial.aeval (fun i => mk₂ (BoundaryArcLiMap.simpleVOA C)
      (BoundaryArcLiMap.gen C i))).toRingHom := by
  have he : MvPolynomial.aeval (fun i => mk₂ (BoundaryArcLiMap.simpleVOA C)
      (BoundaryArcLiMap.gen C i)) = simpleSymbol C := BoundaryArcLiMap.c2Eval_eq_simpleSymbol C
  rw [he]
  exact (BoundaryArcLiMap.baseIdeal_le_boundaryIdeal (m := m)).trans C.boundaryIdeal_le_kernel

/-- The actual base presentation map is unconditionally onto C2. -/
theorem Candidate.baseC2Eval_surjective : Function.Surjective
    (MvPolynomial.aeval (fun i => mk₂ (BoundaryArcLiMap.simpleVOA C)
      (BoundaryArcLiMap.gen C i)) : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] A₂ (BoundaryArcLiMap.simpleVOA C)) := by
  have he : MvPolynomial.aeval (fun i => mk₂ (BoundaryArcLiMap.simpleVOA C)
      (BoundaryArcLiMap.gen C i)) = simpleSymbol C := BoundaryArcLiMap.c2Eval_eq_simpleSymbol C
  rw [he]
  exact simpleSymbol_surjective C

/-- Canonical arc injectivity implies the exact actual simple C2 presentation. -/
def Candidate.baseC2AlgEquiv
    (hinj : Function.Injective C.arcLiPoissonHom.toAlgHom) :
    (BoundaryAuxiliary.BasePoly ℂ ⧸ BoundaryAuxiliary.baseIdeal (R := ℂ) m) ≃ₐ[ℂ]
      A₂ (BoundaryArcLiMap.simpleVOA C) :=
  baseC2AlgEquiv_of_arc_injective (BoundaryArcLiMap.simpleVOA C) (fun _ => 1)
    (fun i => ⟨BoundaryArcLiMap.gen C i,BoundaryArcLiMap.gen_mem C i⟩)
    (BoundaryAuxiliary.baseIdeal m) C.baseC2Relations (BoundaryArcLiMap.baseIdeal_le_kernel C)
    hinj C.baseC2Eval_surjective

/-- The actual intrinsic arc-to-Li PVA isomorphism follows from canonical injectivity. -/
def Candidate.arcLiPoissonEquiv
    (hinj : Function.Injective C.arcLiPoissonHom.toAlgHom) :
    PoissonVertexAlgebra.Equiv (BoundaryAuxiliary.arcPVA m)
      (liPoissonVertexAlgebra (BoundaryArcLiMap.simpleVOA C)) :=
  PoissonVertexAlgebra.Equiv.ofBijective C.arcLiPoissonHom ⟨hinj,C.arcLiPoissonHom_surjective⟩

/-- The same source represents the actual simple C2 arc functor, once injectivity is established:
the bijection is natural in the coefficient algebra (`Candidate.actualC2ArcEquiv_natural`). -/
def Candidate.actualC2ArcEquiv {A : Type*} [CommRing A] [Algebra ℂ A]
    (hinj : Function.Injective C.arcLiPoissonHom.toAlgHom) :
    (InfiniteJet.PresentedJet (BoundaryAuxiliary.baseIdeal (R := ℂ) m) →ₐ[ℂ] A) ≃
      (A₂ (BoundaryArcLiMap.simpleVOA C) →ₐ[ℂ] PowerSeries A) :=
  InfiniteJet.arcEquivOfBaseAlgebraEquiv (BoundaryAuxiliary.baseIdeal m) (C.baseC2AlgEquiv hinj)

/-- `Candidate.actualC2ArcEquiv` is natural in the coefficient algebra, so the presented jet
algebra represents the arc functor of the actual simple `C₂` algebra. -/
theorem Candidate.actualC2ArcEquiv_natural {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (hinj : Function.Injective C.arcLiPoissonHom.toAlgHom)
    (f : InfiniteJet.PresentedJet (BoundaryAuxiliary.baseIdeal (R := ℂ) m) →ₐ[ℂ] A)
    (g : A →ₐ[ℂ] B) :
    C.actualC2ArcEquiv hinj (g.comp f) =
      (PowerSeries.mapAlgHom g).comp (C.actualC2ArcEquiv hinj f) :=
  InfiniteJet.arcEquivOfBaseAlgebraEquiv_natural _ _ f g

/-- The actual simple C2 relation ideal is exactly the three stated boundary relations. -/
theorem Candidate.baseIdeal_eq_simpleSymbol_kernel
    (hinj : Function.Injective C.arcLiPoissonHom.toAlgHom) :
    BoundaryAuxiliary.baseIdeal (R := ℂ) m = RingHom.ker (simpleSymbol C) := by
  have he : MvPolynomial.aeval (fun i => mk₂ (BoundaryArcLiMap.simpleVOA C)
      (BoundaryArcLiMap.gen C i)) = simpleSymbol C := BoundaryArcLiMap.c2Eval_eq_simpleSymbol C
  apply le_antisymm
  · simpa only [he] using C.baseC2Relations
  · intro f hf
    have hz : Ideal.Quotient.mkₐ ℂ (BoundaryAuxiliary.baseIdeal m) f = 0 := by
      apply (C.baseC2AlgEquiv hinj).injective
      rw [map_zero]
      change MvPolynomial.aeval (fun i => mk₂ (BoundaryArcLiMap.simpleVOA C)
        (BoundaryArcLiMap.gen C i)) f = 0
      rw [he]
      exact hf
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end
end VOA.AffineSl2BoundarySingularFamily
