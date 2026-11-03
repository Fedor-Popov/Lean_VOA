/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierChain
import VOA.Commutative.DeligneCasimirJetFiltration

/-!
# The Casimir filtration of `Jet(Sym sl₃ / I₂ⁿˢ)` (first half of step B1)

In every Li/conformal bidegree `(p, N)` the presented jet image of `R̃ = Sym sl₃/I₂ⁿˢ`
(jet order `p`)
carries the Casimir-adic filtration by images of `(Q-jet ideal)^d`, `d ≤ N/2`
(`DeligneCasimirJetFiltration.filtration`, applied to the bidegree projection
`toBidegreeImage p N`).  Its layers telescope to the full dimension (proved).

Hence step B1 (`CasimirAuxiliaryBound`) reduces to a bound on each layer:
`CasimirLayerBound`: the `d`-th layer in bidegree `(p,N)` has dimension at most that of the
auxiliary
sector carrier `degreePiece (auxiliaryCarrier fullMatrix (N-p-2d) d) p`.  This is the dual,
collision-coefficient half of B1 (the auxiliary analogue of `restrictedDualEquivCurrentCarrier`);
its commutative inputs are proved in `A2CarrierCasimir`.  It is a formalization target, not a
literature input.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial
open VOA.FiniteJet VOA.CasimirCostFiltration VOA.FiniteCostDegeneration
open VOA.DeligneAudit.CarrierEmbedding

noncomputable section

/-- The presented jet image of `R̃` in bidegree `(p, N)` at jet order `p`. -/
abbrev bidegreeImage (p N : ℕ) : Submodule ℂ (PresentedJet (R := ℂ) p I2ns) :=
  PresentedJetLiBidegreeImage (R := ℂ) (fun _ : Fin 8 => 1) p p N I2ns

/-- Conformal-weight-`N` jet polynomials, projected to Li degree `p` and passed to the quotient. -/
def toBidegreeImage (p N : ℕ) :
    VOA.DeligneCasimirJetFiltration.JetWeightSource (K := ℂ) (fun _ : Fin 8 => 1) p N →ₗ[ℂ]
      bidegreeImage p N :=
  LinearMap.codRestrict (bidegreeImage p N)
    ((presentedJetMk (R := ℂ) p I2ns).toLinearMap ∘ₗ
      (MvPolynomial.weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin 8 => 1) p) (p, N)) ∘ₗ
      (VOA.DeligneCasimirJetFiltration.JetWeightSource (K := ℂ) (fun _ : Fin 8 => 1) p N).subtype)
    (fun _ => ⟨⟨_, MvPolynomial.weightedHomogeneousComponent_mem _ _ _⟩, rfl⟩)

theorem toBidegreeImage_surjective (p N : ℕ) : Function.Surjective (toBidegreeImage p N) := by
  rintro ⟨y, ⟨g, rfl⟩⟩
  refine ⟨⟨g.1, isWeightedHomogeneous_jetWeight_of_jetLiBidegree _ p p N g.2⟩, ?_⟩
  apply Subtype.ext
  change presentedJetMk (R := ℂ) p I2ns
      (MvPolynomial.weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin 8 => 1) p) (p, N)
        g.1) = presentedJetMk (R := ℂ) p I2ns g.1
  rw [(g.2 : g.1.IsWeightedHomogeneous _ _).weightedHomogeneousComponent_same]

theorem casimir_isWeightedHomogeneous : casimir.IsWeightedHomogeneous (fun _ : Fin 8 => 1) 2 :=
  casimir_isHomogeneous

/-- The Casimir-adic filtration of the bidegree `(p, N)` piece of `Jet R̃`. -/
def casimirFiltration (p N : ℕ) :
    FiniteCostFiltration ℂ (ModuleCat.of ℂ (bidegreeImage p N)) (maxCost N) :=
  VOA.DeligneCasimirJetFiltration.filtration (fun _ : Fin 8 => 1) p N casimir
    casimir_isWeightedHomogeneous (toBidegreeImage p N) (toBidegreeImage_surjective p N)

/-- The `d`-th Casimir layer of the bidegree `(p, N)` piece of `Jet R̃`. -/
abbrev casimirLayer (p N d : ℕ) :=
  FiniteCostFiltration.CostAssociated (K := ℂ) (Source := ModuleCat.of ℂ (bidegreeImage p N))
    (casimirFiltration p N) d

/-- The Casimir layers telescope to the bidegree dimension. -/
theorem sum_casimirLayer_finrank (p N : ℕ) :
    (∑ d ∈ Finset.range (N / 2 + 1), Module.finrank ℂ (casimirLayer p N d)) =
      Module.finrank ℂ (bidegreeImage p N) := by
  have h := VOA.DeligneCasimirJetFiltration.sum_associated_finrank (fun _ : Fin 8 => 1)
    (fun _ => one_ne_zero) p N casimir casimir_isWeightedHomogeneous (toBidegreeImage p N)
    (toBidegreeImage_surjective p N)
  rw [← Fin.sum_univ_eq_sum_range (fun d => Module.finrank ℂ (casimirLayer p N d)) (N / 2 + 1)]
  exact h

theorem finrank_carrier_eq_bidegreeImage {p N : ℕ} (h : p ≤ N) :
    Module.finrank ℂ (Carrier p N) = Module.finrank ℂ (bidegreeImage p N) := by
  have := finrank_carrier_eq relationMatrix h
  rw [← I2ns_eq_quadraticIdeal] at this
  exact this

/-- **Named target (second half of B1).**  Each Casimir layer is bounded by the auxiliary sector
carrier with `N - p - 2d` currents and `d` Casimir particles in derivative degree `p`. -/
structure CasimirLayerBound : Prop where
  le : ∀ p N d, Module.finrank ℂ (casimirLayer p N d) ≤
    if p + 2 * d ≤ N then auxDim (N - p - 2 * d) d p else 0

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
theorem casimirAuxiliaryBound_of_layerBound (hL : CasimirLayerBound) : CasimirAuxiliaryBound := by
  refine ⟨fun N => ?_⟩
  have hsec : ∀ n ∈ Finset.range (N + 1), ∀ x ∈ Finset.antidiagonal n,
      sectorDim N x.1 x.2 =
        if x.1 + 2 * x.2 ≤ N then (fun m d => auxDim m d (N - m - 2 * d)) x.1 x.2 else 0 :=
    fun _ _ _ _ => rfl
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl (hsec n hn),
    ← sum_pd_eq_sum_antidiagonal N (fun m d => auxDim m d (N - m - 2 * d))]
  unfold carrierDim
  apply Finset.sum_le_sum
  intro p hp
  rw [finrank_carrier_eq_bidegreeImage (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)),
    ← sum_casimirLayer_finrank]
  apply Finset.sum_le_sum
  intro d _
  refine (hL.le p N d).trans (le_of_eq ?_)
  split_ifs with hpd
  · congr 1
    omega
  · rfl

/-- **Carrier side of the A₂ inequality, with B1 reduced to the layer bound.** -/
theorem carrierDim_le_demazure_of_layerBound (F Dem : ℕ → PowerSeries ℚ) (D : ℕ → ℕ)
    (hD : ∀ N, (D N : ℚ) = VOA.DeligneAudit.CarrierChain.demazureCoeffOf Dem N)
    (hL : CasimirLayerBound) (hF : SectorFusionBound F) (hU6 : MixedFusionRecursion F Dem)
    (N : ℕ) : carrierDim N ≤ D N :=
  carrierDim_le_demazure F Dem D hD (casimirAuxiliaryBound_of_layerBound hL) hF hU6 N

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms toBidegreeImage_surjective
#print axioms sum_casimirLayer_finrank
#print axioms sum_pd_eq_sum_antidiagonal
#print axioms casimirAuxiliaryBound_of_layerBound
#print axioms carrierDim_le_demazure_of_layerBound
end AxiomAudit
