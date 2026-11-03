import VOA.Huang.LogAssocProductInfinityExpansion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! The actual collision-to-infinity chart has nonzero strict derivative.
Its local image therefore carries an actual neighborhood, and a genuine
Frobenius function vanishing on that chart vanishes on the half-plane. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA.Huang.FrobeniusLog VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open scoped Topology

/-- The literal branch chart from the product overlap to infinity coordinates. -/
noncomputable def productInfinityChart (t : ℂ) : ℂ := -Complex.log (1+Complex.exp t)

/-- The actual product region makes its inverse radial coordinate lie in the half-plane. -/
theorem productInfinityChart_mem_halfPlane {t : ℂ} (ht : t∈overlapDomain) :
    productInfinityChart t∈halfPlane := by
  change -(Complex.log (1+Complex.exp t)).re<0
  rw [Complex.log_re]
  linarith [Real.log_pos (one_lt_norm ht)]

/-- The literal chart has its genuine nonzero strict complex derivative. -/
theorem productInfinityChart_hasStrictDerivAt {t : ℂ} (ht : t∈overlapDomain) :
    HasStrictDerivAt productInfinityChart (-(Complex.exp t/(1+Complex.exp t))) t := by
  have hd : HasStrictDerivAt (fun t => 1+Complex.exp t) (Complex.exp t) t :=
    (Complex.hasStrictDerivAt_exp t).const_add 1
  exact (hd.clog (one_add_exp_mem_slitPlane ht)).neg

/-- No boundary or branch hypothesis is needed beyond the actual overlap. -/
theorem productInfinityChart_deriv_ne_zero {t : ℂ} (ht : t∈overlapDomain) :
    -(Complex.exp t/(1+Complex.exp t))≠0 :=
  neg_ne_zero.mpr (div_ne_zero (Complex.exp_ne_zero t) (one_add_exp_ne_zero ht))

/-- The chart carries the actual local neighborhood exactly to its infinity image. -/
theorem productInfinityChart_map_nhds {t : ℂ} (ht : t∈overlapDomain) :
    Filter.map productInfinityChart (𝓝 t)=𝓝 (productInfinityChart t) :=
  (productInfinityChart_hasStrictDerivAt ht).map_nhds_eq (productInfinityChart_deriv_ne_zero ht)

/-- A genuine Frobenius function that vanishes on the literal overlap chart
vanishes on the whole connected infinity half-plane. -/
theorem infinity_zero_of_chart_zero {F : ℂ → ℂ} (hF : HasLogExp halfPlane F)
    (hzero : ∀ t∈overlapDomain,F (productInfinityChart t)=0) :
    ∀ σ∈halfPlane,F σ=0 := by
  obtain ⟨E,hE⟩ := hF
  obtain ⟨t₀,ht₀⟩ := overlapDomain_nonempty
  have hev : (fun t => E.eval (productInfinityChart t)) =ᶠ[𝓝 t₀] 0 :=
    Filter.eventually_of_mem (isOpen_overlapDomain.mem_nhds ht₀) fun t ht => by
      dsimp only
      rw [← hE (productInfinityChart t) (productInfinityChart_mem_halfPlane ht)]
      exact hzero t ht
  have hev' : E.eval =ᶠ[𝓝 (productInfinityChart t₀)] 0 := by
    rw [← productInfinityChart_map_nhds ht₀]
    exact hev
  have hd : DifferentiableOn ℂ E.eval halfPlane := fun σ hσ =>
    (E.hasDerivAt_eval hσ).differentiableAt.differentiableWithinAt
  have hez := (hd.analyticOnNhd isOpen_halfPlane).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_halfPlane (productInfinityChart_mem_halfPlane ht₀) hev'
  intro σ hσ
  rw [hE σ hσ]
  exact hez hσ

end VOA.Huang.LogAssocExpansion
