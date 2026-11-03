/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.FiniteHilbertSqueeze
import VOA.Commutative.FiniteJetLiSupport
import VOA.Filtered.InfiniteLiJetBidegree

/-!
# Weightwise main theorem for the Deligne current presentation

The Deligne character identities are ordinary conformal-weight identities.  The
geometric carrier, by contrast, bounds each Li/conformal bidegree separately.
This file proves once and for all that these are compatible: surjectivity gives
the lower pointwise bound, a source-dual embedding into the carrier gives the
upper pointwise bound, and equality of the ordinary characters forces equality
in every Li degree.

The theorem is deliberately uniform in the vertex operator algebra, its finite
weight-one current basis, the proposed `C₂` ideal, and the concrete carrier.
Thus it does not package the missing Deligne carrier comparison as a literature
hypothesis.  That comparison must supply the displayed source-dual embeddings.
-/

namespace VOA.DeligneWeightwiseHilbertCapstone

open VertexOperatorAlgebra

noncomputable section

universe uV uC

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {g : ℕ}

/-- An ordinary carrier character and bidegreewise source-dual embeddings give
the exact stable Hilbert bound required by the infinite Li-jet theorem.  No
Li-bigraded character identity is assumed. -/
theorem stableBidegreeHilbertBound_of_weightCharacter
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V)
    (hgen : ∀ i, gen i ∈ W.grading (1 : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨gen i, hgen i⟩).toRingHom)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : ∀ p N, Function.Surjective
      (liPresentedJetBidegreeMap W p
        (fun i => liDegreeZeroClass W 1 ⟨gen i, hgen i⟩)
        I hI (fun _ => 1) p N))
    (sourceDualToCarrier : ∀ p N,
      Module.Dual ℂ
        (FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin g => 1) p p N I) →ₗ[ℂ]
          Carrier p N)
    (hcarrier : ∀ p N, Function.Injective (sourceDualToCarrier p N))
    (hcharacter : ∀ N,
      (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) =
        Module.finrank ℂ (W.grading N)) :
    ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin g => 1) p p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N) := by
  intro p N
  by_cases hp : p ≤ N
  · let source : ℕ → Type _ := fun q =>
      FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin g => 1) q q N I
    let carrier : ℕ → Type _ := fun q => Carrier q N
    let actual : ℕ → Type _ := fun q => liWeightLayer W q N
    have hca : ∀ q ∈ Finset.range (N + 1),
        Module.finrank ℂ (actual q) ≤ Module.finrank ℂ (source q) := by
      intro q hq
      letI : FiniteDimensional ℂ (source q) :=
        FiniteJet.finiteDimensional_presentedJetLiBidegreeImage
          (fun _ : Fin g => 1) (fun _ => by simp) q q N I
      letI : FiniteDimensional ℂ (actual q) :=
        liAssociatedGraded_component_finiteDimensional W q N
      exact LinearMap.finrank_le_finrank_of_surjective (hsurj q N)
    have hab : ∀ q ∈ Finset.range (N + 1),
        Module.finrank ℂ (source q) ≤ Module.finrank ℂ (carrier q) := by
      intro q hq
      letI : FiniteDimensional ℂ (source q) :=
        FiniteJet.finiteDimensional_presentedJetLiBidegreeImage
          (fun _ : Fin g => 1) (fun _ => by simp) q q N I
      calc
        Module.finrank ℂ (source q) = Module.finrank ℂ (Module.Dual ℂ (source q)) :=
          (Subspace.dual_finrank_eq).symm
        _ ≤ Module.finrank ℂ (carrier q) :=
          LinearMap.finrank_le_finrank_of_injective (hcarrier q N)
    have hsum :
        (∑ q ∈ Finset.range (N + 1), Module.finrank ℂ (actual q)) =
          ∑ q ∈ Finset.range (N + 1), Module.finrank ℂ (carrier q) := by
      rw [sum_liWeightLayer_finrank_eq_grading W N]
      exact (hcharacter N).symm
    have hsqueeze :=
      VOA.FiniteHilbertSqueeze.pointwise_eq_of_sandwich_of_sum_eq
        (Finset.range (N + 1))
        (fun q => Module.finrank ℂ (actual q))
        (fun q => Module.finrank ℂ (source q))
        (fun q => Module.finrank ℂ (carrier q)) hca hab hsum
    exact (hsqueeze p (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hp))).1.symm.le
  · have hNp : N < p := Nat.lt_of_not_ge hp
    rw [FiniteJet.presentedJetLiBidegreeImage_eq_bot_of_conformalWeight_lt_liDegree
      (R := ℂ) (fun _ : Fin g => 1) p p N hNp I]
    simp

/-- Final current-generated classical-freeness theorem from a concrete
bidegree carrier and its ordinary conformal-weight character. -/
theorem classicallyFree_of_carrier_weightCharacter
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V)
    (hgen : ∀ i, gen i ∈ W.grading (1 : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨gen i, hgen i⟩).toRingHom)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurjBidegree : ∀ p N, Function.Surjective
      (liPresentedJetBidegreeMap W p
        (fun i => liDegreeZeroClass W 1 ⟨gen i, hgen i⟩)
        I hI (fun _ => 1) p N))
    (hsurjInfinite : Function.Surjective
      (liInfinitePresentedJetMap W
        (fun i => liDegreeZeroClass W 1 ⟨gen i, hgen i⟩) I hI))
    (sourceDualToCarrier : ∀ p N,
      Module.Dual ℂ
        (FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin g => 1) p p N I) →ₗ[ℂ]
          Carrier p N)
    (hcarrier : ∀ p N, Function.Injective (sourceDualToCarrier p N))
    (hcharacter : ∀ N,
      (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) =
        Module.finrank ℂ (W.grading N)) :
    LiPresentationClassicallyFree W
      (fun i => liDegreeZeroClass W 1 ⟨gen i, hgen i⟩) I hI := by
  apply liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze_of_surjective
    W gen (fun _ => 1) hgen I hI (fun _ => by simp) hsurjBidegree hsurjInfinite
  exact stableBidegreeHilbertBound_of_weightCharacter W gen hgen I hI Carrier
    hsurjBidegree sourceDualToCarrier hcarrier hcharacter

end


end VOA.DeligneWeightwiseHilbertCapstone

section AxiomAudit
#print axioms
  VOA.DeligneWeightwiseHilbertCapstone.stableBidegreeHilbertBound_of_weightCharacter
#print axioms
  VOA.DeligneWeightwiseHilbertCapstone.classicallyFree_of_carrier_weightCharacter
end AxiomAudit
