/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.InfiniteJet

/-!
# The presentation-level infinite jet map to the Li associated graded

This file specializes the unbounded finite-support jet construction to the Li associated graded.
It constructs the canonical map from a presented infinite jet algebra and proves that it is
surjective as soon as every homogeneous Li class has a preimage in some included finite-order
presented jet algebra.  Compatibility of the finite and infinite evaluations is proved in the
pure commutative-algebra file `InfiniteJet`.

The second statement deliberately allows the required order to depend on the homogeneous class.
This is the correct interface for affine examples, whose `C₂` algebras need not be finite
dimensional.  No injectivity or comparison with the scheme-theoretic arc functor is asserted.
-/

namespace VOA

open scoped DirectSum

universe uσ uV

variable {σ : Type uσ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The canonical presentation-level infinite jet map to the Li associated graded. -/
noncomputable def liInfinitePresentedJetMap (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) :
    InfiniteJet.PresentedJet (R := ℂ) I →ₐ[ℂ] liAssociatedGraded W :=
  InfiniteJet.presentedJetToDifferentialAlgebra (liAssociatedGradedTranslation W)
    (liAssociatedGradedTranslation_leibniz W) (liAssociatedGradedTranslation_one W) x I hI

/-- Presentation-level classical freeness: the canonical map from the explicitly presented
infinite jet algebra to the Li associated graded is bijective.  This deliberately does not claim
that the source has already been identified with an independently defined scheme-theoretic arc
functor. -/
def LiPresentationClassicallyFree (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) : Prop :=
  Function.Bijective (liInfinitePresentedJetMap W x I hI)

/-- The infinite Li jet map restricts to the finite presentation-level map on every finite jet
order.  Keeping this specialization as a named lemma avoids repeatedly unfolding the two
dependent quotient maps in model-specific surjectivity proofs. -/
@[simp] theorem liInfinitePresentedJetMap_ofFinite (W : VertexOperatorAlgebra V)
    (m : ℕ) (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (y : FiniteJet.PresentedJet (R := ℂ) m I) :
    liInfinitePresentedJetMap W x I hI
        (InfiniteJet.presentedJetOfFinite (R := ℂ) m I y) =
      liPresentedJetMap W m x I hI y := by
  unfold liInfinitePresentedJetMap liPresentedJetMap
  apply InfiniteJet.presentedJetToDifferentialAlgebra_ofFinite

/-- **Variable-order homogeneous surjectivity criterion.**  To prove surjectivity of the
infinite presentation-level jet map, it suffices to hit each homogeneous Li class using some
finite jet order.  The order may depend on the bidegree and on the class itself. -/
theorem liInfinitePresentedJetMap_surjective_of_finite_homogeneous_preimages
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hhom : ∀ p N (z : liWeightLayer W p N),
      ∃ (m : ℕ) (y : FiniteJet.PresentedJet (R := ℂ) m I),
        liInfinitePresentedJetMap W x I hI
            (InfiniteJet.presentedJetOfFinite (R := ℂ) m I y) =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z) :
    Function.Surjective (liInfinitePresentedJetMap W x I hI) := by
  intro a
  induction a using DirectSum.induction_on with
  | zero =>
      exact ⟨0, map_zero _⟩
  | of d z =>
      rcases d with ⟨p, N⟩
      obtain ⟨m, y, hy⟩ := hhom p N z
      exact ⟨InfiniteJet.presentedJetOfFinite (R := ℂ) m I y, hy⟩
  | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      refine ⟨a' + b', ?_⟩
      rw [map_add, ha', hb']

/-- **Finite-stage injectivity criterion.**  If every finite presented-jet map is injective,
then the presentation-level infinite jet map is injective.  Every infinite polynomial uses only
finitely many jet variables, so a kernel element can be represented at one finite stage.  This
argument does not assume that the transition maps between finite presented-jet quotients are
injective. -/
theorem liInfinitePresentedJetMap_injective_of_finite
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hfinite : ∀ m, Function.Injective (liPresentedJetMap W m x I hI)) :
    Function.Injective (liInfinitePresentedJetMap W x I hI) := by
  have hzero : ∀ z : InfiniteJet.PresentedJet (R := ℂ) I,
      liInfinitePresentedJetMap W x I hI z = 0 → z = 0 := by
    intro z
    refine Submodule.Quotient.induction_on _ z fun f hf ↦ ?_
    obtain ⟨m, g, hgf⟩ := InfiniteJet.exists_ofFinite_preimage (R := ℂ) f
    have hfiniteZero :
        liPresentedJetMap W m x I hI
            (FiniteJet.presentedJetMk (R := ℂ) m I g) = 0 := by
      rw [← liInfinitePresentedJetMap_ofFinite W m x I hI]
      rw [InfiniteJet.presentedJetOfFinite_mk, hgf]
      exact hf
    have hgzero : FiniteJet.presentedJetMk (R := ℂ) m I g = 0 := by
      apply hfinite m
      rw [map_zero]
      exact hfiniteZero
    change InfiniteJet.presentedJetMk (R := ℂ) I f = 0
    rw [← hgf, ← InfiniteJet.presentedJetOfFinite_mk, hgzero, map_zero]
  intro a b hab
  apply sub_eq_zero.mp
  apply hzero (a - b)
  rw [map_sub, hab, sub_self]

/-- Bijectivity of the presentation-level infinite jet map from finite-stage injectivity and the
independently proved infinite surjectivity. -/
theorem liInfinitePresentedJetMap_bijective_of_finite
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hsurjective : Function.Surjective (liInfinitePresentedJetMap W x I hI))
    (hfinite : ∀ m, Function.Injective (liPresentedJetMap W m x I hI)) :
    Function.Bijective (liInfinitePresentedJetMap W x I hI) :=
  ⟨liInfinitePresentedJetMap_injective_of_finite W x I hI hfinite, hsurjective⟩

/-- Presentation-level classical freeness follows from finite-stage injectivity and the
independently proved infinite surjectivity. -/
theorem liPresentationClassicallyFree_of_finite
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hsurjective : Function.Surjective (liInfinitePresentedJetMap W x I hI))
    (hfinite : ∀ m, Function.Injective (liPresentedJetMap W m x I hI)) :
    LiPresentationClassicallyFree W x I hI :=
  liInfinitePresentedJetMap_bijective_of_finite W x I hI hsurjective hfinite

/-- Presentation-level classical freeness from the exact polynomial kernel at every finite jet
order.  This is the direct endpoint for differential Gröbner or carrier calculations. -/
theorem liPresentationClassicallyFree_of_finite_kernels
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hsurjective : Function.Surjective (liInfinitePresentedJetMap W x I hI))
    (hkernels : ∀ m,
      RingHom.ker (liFiniteJetPolynomialMap W m x).toRingHom =
        FiniteJet.jetIdeal (R := ℂ) m I) :
    LiPresentationClassicallyFree W x I hI := by
  apply liPresentationClassicallyFree_of_finite W x I hI hsurjective
  intro m
  exact (liPresentedJetMap_injective_iff_polynomial_kernel W m x I hI).mpr (hkernels m)

/-- The presentation-level classical-freeness equivalence obtained from finite-stage
injectivity and infinite surjectivity.  Comparison with an independently defined arc functor is
still a separate identification. -/
noncomputable def liInfinitePresentedJetEquivOfFinite
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hsurjective : Function.Surjective (liInfinitePresentedJetMap W x I hI))
    (hfinite : ∀ m, Function.Injective (liPresentedJetMap W m x I hI)) :
    InfiniteJet.PresentedJet (R := ℂ) I ≃ₐ[ℂ] liAssociatedGraded W :=
  AlgEquiv.ofBijective (liInfinitePresentedJetMap W x I hI)
    (liInfinitePresentedJetMap_bijective_of_finite W x I hI hsurjective hfinite)

/-- The presentation-level algebra equivalence obtained directly from exact polynomial kernels at
all finite jet orders and infinite surjectivity. -/
noncomputable def liInfinitePresentedJetEquivOfFiniteKernels
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hsurjective : Function.Surjective (liInfinitePresentedJetMap W x I hI))
    (hkernels : ∀ m,
      RingHom.ker (liFiniteJetPolynomialMap W m x).toRingHom =
        FiniteJet.jetIdeal (R := ℂ) m I) :
    InfiniteJet.PresentedJet (R := ℂ) I ≃ₐ[ℂ] liAssociatedGraded W :=
  AlgEquiv.ofBijective (liInfinitePresentedJetMap W x I hI)
    (liPresentationClassicallyFree_of_finite_kernels W x I hI hsurjective hkernels)

@[simp] theorem liInfinitePresentedJetEquivOfFiniteKernels_apply
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hsurjective : Function.Surjective (liInfinitePresentedJetMap W x I hI))
    (hkernels : ∀ m,
      RingHom.ker (liFiniteJetPolynomialMap W m x).toRingHom =
        FiniteJet.jetIdeal (R := ℂ) m I)
    (z : InfiniteJet.PresentedJet (R := ℂ) I) :
    liInfinitePresentedJetEquivOfFiniteKernels W x I hI hsurjective hkernels z =
      liInfinitePresentedJetMap W x I hI z := rfl

@[simp] theorem liInfinitePresentedJetEquivOfFinite_apply
    (W : VertexOperatorAlgebra V)
    (x : σ → liAssociatedGraded W) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (hsurjective : Function.Surjective (liInfinitePresentedJetMap W x I hI))
    (hfinite : ∀ m, Function.Injective (liPresentedJetMap W m x I hI))
    (z : InfiniteJet.PresentedJet (R := ℂ) I) :
    liInfinitePresentedJetEquivOfFinite W x I hI hsurjective hfinite z =
      liInfinitePresentedJetMap W x I hI z := rfl

end VOA

section AxiomAudit
#print axioms VOA.liPresentationClassicallyFree_of_finite
#print axioms VOA.liPresentationClassicallyFree_of_finite_kernels
#print axioms VOA.liInfinitePresentedJetEquivOfFiniteKernels
end AxiomAudit
