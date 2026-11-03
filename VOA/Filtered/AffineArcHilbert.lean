/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Filtered.AffineInfiniteClassicalFreeness
import VOA.Commutative.InfiniteJetArc

/-!
# A conformal-weight Hilbert squeeze for affine arcs

A bound on the sum of stable jet bidegree dimensions is sufficient for the affine Li map.
No equality of bigraded characters is assumed. The source bound remains an explicit
mathematical input; identifying it with a computed Hilbert series is a separate task.
-/

namespace VOA

open scoped BigOperators

namespace FiniteJet

variable {R σ : Type*} [CommRing R]

/-- Li degree cannot exceed conformal weight when base weights are natural numbers. -/
theorem homogeneous_eq_zero_of_conformal_lt_li (w : σ → ℕ) (m p N : ℕ)
    (hNp : N < p) (f : JetPoly R σ m)
    (hf : f.IsWeightedHomogeneous (jetLiBidegree w m) (p, N)) : f = 0 := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_zero]
  by_contra he
  have hdeg := hf he
  have hfst := congrArg Prod.fst hdeg
  have hsnd := congrArg Prod.snd hdeg
  simp [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum, Prod.snd_sum,
    jetLiBidegree] at hfst hsnd
  have hle : (∑ v ∈ e.support, e v * (v.order : ℕ)) ≤
      ∑ v ∈ e.support, e v * (w v.generator + (v.order : ℕ)) := by
    exact Finset.sum_le_sum (fun v _ => Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  omega

/-- Therefore the presented bidegree image is zero above the conformal diagonal. -/
theorem presentedJetLiBidegreeImage_eq_bot_of_lt (w : σ → ℕ) (m p N : ℕ)
    (hNp : N < p) (I : Ideal (MvPolynomial σ R)) :
    PresentedJetLiBidegreeImage w m p N I = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro f
  change presentedJetMk m I f.val = 0
  rw [homogeneous_eq_zero_of_conformal_lt_li w m p N hNp f.val f.property, map_zero]

end FiniteJet

namespace AffineVOA.CurrentLi

open VOA.AffineVOA.Inst

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)
variable (J : Submodule ℂ (WakModule k))
variable (hJ : (affineSl2VOA_closed k hk).IsIdeal J)
variable (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) J)

local notation "QW" => QuotVOA.quotientVOA (affineSl2VOA_closed k hk) J hJ hgr

/-- The ordinary conformal Hilbert bound recovers every needed stable bidegree bound. -/
theorem quotientAffine_stable_bidegree_bound_of_total_bound
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval (quotientAffineCurrentLiClass k hk J hJ hgr)).toRingHom)
    (hbound : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin 3 => 1) p p N B)) ≤
      Module.finrank ℂ ((QW).grading N)) :
    ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin 3 => 1) p p N B) ≤
      Module.finrank ℂ (liWeightLayer QW p N) := by
  intro p N
  by_cases hp : p ≤ N
  · let s := Finset.range (N + 1)
    let a := fun p => Module.finrank ℂ
      (FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin 3 => 1) p p N B)
    let b := fun p => Module.finrank ℂ (liWeightLayer QW p N)
    have hba : ∀ p ∈ s, b p ≤ a p := by
      intro p _
      letI := FiniteJet.finiteDimensional_presentedJetLiBidegreeImage
        (fun _ : Fin 3 => 1) (fun _ => Nat.zero_lt_one) p p N B
      exact LinearMap.finrank_le_finrank_of_surjective
        (quotientAffine_liPresentedJetBidegreeMap_surjective k hk J hJ hgr B hB p N)
    have hsum : (∑ p ∈ s, b p) = ∑ p ∈ s, a p := by
      apply le_antisymm (Finset.sum_le_sum hba)
      calc
        _ ≤ Module.finrank ℂ ((QW).grading N) := hbound N
        _ = _ := (sum_liWeightLayer_finrank_eq_grading QW N).symm
    exact (FiniteHilbertSqueeze.eqOn_of_pointwise_le_of_sum_eq s b a hba hsum p
      (Finset.mem_range.mpr (by omega))).symm.le
  · rw [FiniteJet.presentedJetLiBidegreeImage_eq_bot_of_lt
      (fun _ : Fin 3 => 1) p p N (by omega) B, finrank_bot]
    exact Nat.zero_le _

/-- A univariate Hilbert bound, together with the actual current-word surjection, proves
bijectivity of the canonical presentation-level affine Li map. -/
theorem quotientAffine_liPresentationClassicallyFree_of_total_hilbert_bound
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval (quotientAffineCurrentLiClass k hk J hJ hgr)).toRingHom)
    (hbound : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage (fun _ : Fin 3 => 1) p p N B)) ≤
      Module.finrank ℂ ((QW).grading N)) :
    LiPresentationClassicallyFree QW
      (quotientAffineCurrentLiClass k hk J hJ hgr) B hB :=
  quotientAffine_liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
    k hk J hJ hgr B hB
    (quotientAffine_stable_bidegree_bound_of_total_bound k hk J hJ hgr B hB hbound)

end
end AffineVOA.CurrentLi
end VOA
