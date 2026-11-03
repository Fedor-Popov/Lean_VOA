/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.InfiniteClassicalFreeness

/-!
# Classical freeness for a *containment* ideal determines the `C₂` presentation

The higher-rank Deligne capstone (`DeligneHigherRankConditionalCapstone`) can be stated with an
exact `C₂` presentation (`exact_kernel`) as a hypothesis.  That hypothesis is unnecessary: if the canonical map
from the presented jet algebra of any ideal `I` contained in the kernel is bijective, then `I`
*is* the kernel.  Hence the maximal-ideal / exact-presentation input can be removed from the
input ledger and recovered as a conclusion.

Proof: the order-zero inclusion `MvPolynomial σ ℂ → PresentedJet I` has a retraction onto
`MvPolynomial σ ℂ ⧸ I`, obtained from the universal property with the zero derivation.
-/

namespace VOA

open InfiniteJet

variable {σ : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Order-zero inclusion of coordinates into the presented infinite jet algebra. -/
noncomputable def presentedJetOrderZero (I : Ideal (MvPolynomial σ ℂ)) :
    MvPolynomial σ ℂ →ₐ[ℂ] PresentedJet (R := ℂ) I :=
  (presentedJetMk (R := ℂ) I).comp (MvPolynomial.rename fun i : σ => (i, 0))

/-- The zero derivation on the quotient ring. -/
private noncomputable def zeroDer (I : Ideal (MvPolynomial σ ℂ)) :
    (MvPolynomial σ ℂ ⧸ I) →ₗ[ℂ] (MvPolynomial σ ℂ ⧸ I) := 0

private theorem dividedIterate_zeroDer_succ (I : Ideal (MvPolynomial σ ℂ)) (r : ℕ)
    (a : MvPolynomial σ ℂ ⧸ I) :
    FiniteJet.dividedIterate (zeroDer I) (r + 1) a = 0 := by
  simp [FiniteJet.dividedIterate, zeroDer, pow_succ]

/-- Retraction `PresentedJet I → MvPolynomial σ ℂ ⧸ I` killing all positive-order jets. -/
noncomputable def presentedJetRetraction (I : Ideal (MvPolynomial σ ℂ)) :
    PresentedJet (R := ℂ) I →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ I) :=
  presentedJetToDifferentialAlgebra (zeroDer I) (by intro a b; simp [zeroDer])
    (by simp [zeroDer]) (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) I
    (by
      intro f hf
      rw [RingHom.mem_ker]
      have hext : (MvPolynomial.aeval fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) =
          Ideal.Quotient.mkₐ ℂ I := MvPolynomial.algHom_ext fun i => by simp
      change (MvPolynomial.aeval fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) f = 0
      rw [hext, Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hf)

theorem presentedJetRetraction_orderZero (I : Ideal (MvPolynomial σ ℂ))
    (f : MvPolynomial σ ℂ) :
    presentedJetRetraction I (presentedJetOrderZero I f) = Ideal.Quotient.mk I f := by
  have h : (presentedJetRetraction I).comp (presentedJetOrderZero I) =
      (Ideal.Quotient.mkₐ ℂ I) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [presentedJetOrderZero, presentedJetRetraction, derivationJetEval]
  exact DFunLike.congr_fun h f

/-- The canonical Li map restricted to order zero is evaluation at the degree-zero classes. -/
theorem liInfinitePresentedJetMap_orderZero (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) :
    (liInfinitePresentedJetMap W x I hI).comp (presentedJetOrderZero I) =
      MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [presentedJetOrderZero, liInfinitePresentedJetMap, derivationJetEval]

/-- **Exact presentation from classical freeness.**  If the presented jet map of a
containment ideal is bijective (indeed, injective suffices), the ideal is the full kernel. -/
theorem ker_eq_of_liPresentationClassicallyFree (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hfree : LiPresentationClassicallyFree W x I hI) :
    RingHom.ker (MvPolynomial.aeval x).toRingHom = I := by
  refine le_antisymm ?_ hI
  intro f hf
  have h0 : liInfinitePresentedJetMap W x I hI (presentedJetOrderZero I f) = 0 := by
    have := DFunLike.congr_fun (liInfinitePresentedJetMap_orderZero W x I hI) f
    simpa [RingHom.mem_ker] using this.trans (RingHom.mem_ker.mp hf)
  have hz : presentedJetOrderZero I f = 0 :=
    hfree.1 (by rw [h0, map_zero])
  have := presentedJetRetraction_orderZero I f
  rw [hz, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm

end VOA

section AxiomAudit
#print axioms VOA.ker_eq_of_liPresentationClassicallyFree
end AxiomAudit
