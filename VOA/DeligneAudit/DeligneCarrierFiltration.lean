/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierChain
import VOA.Commutative.DeligneCasimirJetFiltration

/-!
# Type-generic version of `A2CarrierFiltration`

Mechanically generalized from the A₂ file `A2CarrierFiltration` to arbitrary type data
`D : DeligneCarrierData` (`Fin 8 ↦ Fin D.n`, `I2ns ↦ D.I`, `casimir ↦ D.Q`, U3 ↦ `D.u3`).
See that file for the mathematical commentary.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial
open VOA.FiniteJet VOA.CasimirCostFiltration VOA.FiniteCostDegeneration
open VOA.DeligneAudit.CarrierEmbedding
open DeligneCarrierData

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable (D : DeligneCarrierData)
include D


/-- The presented jet image of `R̃` in bidegree `(p, N)` at jet order `p`. -/
abbrev bidegreeImage (p N : ℕ) : Submodule ℂ (PresentedJet (R := ℂ) p D.I) :=
  PresentedJetLiBidegreeImage (R := ℂ) (fun _ : Fin D.n => 1) p p N D.I

/-- Conformal-weight-`N` jet polynomials, projected to Li degree `p` and passed to the quotient. -/
def toBidegreeImage (p N : ℕ) :
    VOA.DeligneCasimirJetFiltration.JetWeightSource (K := ℂ) (fun _ : Fin D.n => 1) p N →ₗ[ℂ]
      (bidegreeImage D) p N :=
  LinearMap.codRestrict ((bidegreeImage D) p N)
    ((presentedJetMk (R := ℂ) p D.I).toLinearMap ∘ₗ
      (MvPolynomial.weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin D.n => 1) p) (p, N)) ∘ₗ
      (VOA.DeligneCasimirJetFiltration.JetWeightSource (K := ℂ) (fun _ : Fin D.n => 1) p N).subtype)
    (fun _ => ⟨⟨_, MvPolynomial.weightedHomogeneousComponent_mem _ _ _⟩, rfl⟩)

theorem toBidegreeImage_surjective (p N : ℕ) : Function.Surjective ((toBidegreeImage D) p N) := by
  rintro ⟨y, ⟨g, rfl⟩⟩
  refine ⟨⟨g.1, isWeightedHomogeneous_jetWeight_of_jetLiBidegree _ p p N g.2⟩, ?_⟩
  apply Subtype.ext
  change presentedJetMk (R := ℂ) p D.I
      (MvPolynomial.weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin D.n => 1) p) (p, N)
        g.1) = presentedJetMk (R := ℂ) p D.I g.1
  rw [(g.2 : g.1.IsWeightedHomogeneous _ _).weightedHomogeneousComponent_same]

theorem D.Q_isWeightedHomogeneous : D.Q.IsWeightedHomogeneous (fun _ : Fin D.n => 1) 2 :=
  D.Q_isHomogeneous

/-- The Casimir-adic filtration of the bidegree `(p, N)` piece of `Jet R̃`. -/
def casimirFiltration (p N : ℕ) :
    FiniteCostFiltration ℂ (ModuleCat.of ℂ ((bidegreeImage D) p N)) (maxCost N) :=
  VOA.DeligneCasimirJetFiltration.filtration (fun _ : Fin D.n => 1) p N D.Q
    D.Q_isWeightedHomogeneous ((toBidegreeImage D) p N) ((toBidegreeImage_surjective D) p N)

/-- The `d`-th Casimir layer of the bidegree `(p, N)` piece of `Jet R̃`. -/
abbrev casimirLayer (p N d : ℕ) :=
  FiniteCostFiltration.CostAssociated (K := ℂ) (Source := ModuleCat.of ℂ ((bidegreeImage D) p N))
    ((casimirFiltration D) p N) d

/-- The Casimir layers telescope to the bidegree dimension. -/
theorem sum_casimirLayer_finrank (p N : ℕ) :
    (∑ d ∈ Finset.range (N / 2 + 1), Module.finrank ℂ ((casimirLayer D) p N d)) =
      Module.finrank ℂ ((bidegreeImage D) p N) := by
  have h := VOA.DeligneCasimirJetFiltration.sum_associated_finrank (fun _ : Fin D.n => 1)
    (fun _ => one_ne_zero) p N D.Q D.Q_isWeightedHomogeneous ((toBidegreeImage D) p N)
    ((toBidegreeImage_surjective D) p N)
  rw [← Fin.sum_univ_eq_sum_range (fun d => Module.finrank ℂ ((casimirLayer D) p N d)) (N / 2 + 1)]
  exact h

theorem finrank_carrier_eq_bidegreeImage {p N : ℕ} (h : p ≤ N) :
    Module.finrank ℂ ((Carrier D) p N) = Module.finrank ℂ ((bidegreeImage D) p N) := by
  have := finrank_carrier_eq D.rel h
  exact this

/-- **Named target (second half of B1).**  Each Casimir layer is bounded by the auxiliary sector
carrier with `N - p - 2d` currents and `d` Casimir particles in derivative degree `p`. -/
structure CasimirLayerBound : Prop where
  le : ∀ p N d, Module.finrank ℂ ((casimirLayer D) p N d) ≤
    if p + 2 * d ≤ N then (auxDim D) (N - p - 2 * d) d p else 0

/-- Reindexing `(p, d) ↦ (m, d) = (N - p - 2d, d)`. -/
theorem sum_pd_eq_sum_antidiagonal (N : ℕ) (h : ℕ → ℕ → ℕ) :
    (∑ p ∈ Finset.range (N + 1), ∑ d ∈ Finset.range (N / 2 + 1),
        if p + 2 * d ≤ N then h (N - p - 2 * d) d else 0) =
      ∑ n ∈ Finset.range (N + 1), ∑ x ∈ Finset.antidiagonal n,
        if x.1 + 2 * x.2 ≤ N then h x.1 x.2 else 0 := by
  rw [← Finset.sum_product', Finset.sum_sigma', ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun x _ => (⟨N - x.1 - x.2, (N - x.1 - 2 * x.2, x.2)⟩ :
      Σ _ : ℕ, ℕ × ℕ))
    (fun y _ => (N - y.2.1 - 2 * y.2.2, y.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, d⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
      Finset.mem_antidiagonal]
    omega
  · rintro ⟨n, m, d⟩ hy
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
      Finset.mem_antidiagonal] at hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨p, d⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨-, hpd⟩ := hx
    refine Prod.ext ?_ rfl
    change N - (N - p - 2 * d) - 2 * d = p
    omega
  · rintro ⟨n, m, d⟩ hy
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
      Finset.mem_antidiagonal] at hy
    have h1 : N - (N - m - 2 * d) - d = n := by omega
    have h2 : N - (N - m - 2 * d) - 2 * d = m := by omega
    simp only [h1, h2]
  · rintro ⟨p, d⟩ hx
    rfl

/-- **B1 from the layer bound.** -/
theorem casimirAuxiliaryBound_of_layerBound (hL : (CasimirLayerBound D)) : (CasimirAuxiliaryBound D) := by
  refine ⟨fun N => ?_⟩
  have hsec : ∀ n ∈ Finset.range (N + 1), ∀ x ∈ Finset.antidiagonal n,
      (sectorDim D) N x.1 x.2 =
        if x.1 + 2 * x.2 ≤ N then (fun m d => (auxDim D) m d (N - m - 2 * d)) x.1 x.2 else 0 :=
    fun _ _ _ _ => rfl
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl (hsec n hn),
    ← (sum_pd_eq_sum_antidiagonal D) N (fun m d => (auxDim D) m d (N - m - 2 * d))]
  unfold carrierDim
  apply Finset.sum_le_sum
  intro p hp
  rw [(finrank_carrier_eq_bidegreeImage D) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)),
    ← (sum_casimirLayer_finrank D)]
  apply Finset.sum_le_sum
  intro d _
  refine (hL.le p N d).trans (le_of_eq ?_)
  split_ifs with hpd
  · congr 1
    omega
  · rfl

/-- **(Carrier D) side of the A₂ inequality, with B1 reduced to the layer bound.** -/
theorem carrierDim_le_demazure_of_layerBound (F Dem : ℕ → PowerSeries ℚ) (Dz : ℕ → ℕ)
    (hD : ∀ N, (Dz N : ℚ) = VOA.DeligneAudit.CarrierChain.demazureCoeffOf Dem N)
    (hL : (CasimirLayerBound D)) (hF : (SectorFusionBound D) F) (hU6 : MixedFusionRecursion F Dem)
    (N : ℕ) : (carrierDim D) N ≤ Dz N :=
  (carrierDim_le_demazure D) F Dem Dz hD ((casimirAuxiliaryBound_of_layerBound D) hL) hF hU6 N

end

end VOA.DeligneAudit.DeligneCarrier
