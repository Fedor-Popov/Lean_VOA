import VOA.Classification.COne.OrbIcoWJetLimits
import Mathlib.Analysis.Complex.ReImTopology

/-! Nontrivial nonreal approach filters and the actual Fock-square parameter. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open Filter Topology

instance nonrealNhdsOne_neBot : NeBot nonrealNhdsOne := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  change (1 : ℂ)∈closure (Complex.im ⁻¹' ({(0 : ℝ)}ᶜ))
  rw [Complex.closure_preimage_im,closure_compl_singleton]
  simp

/-- The genuine Fock parameter t=s² approaches the same nonreal special fiber. -/
theorem square_tendsto_nonreal :
    Tendsto (fun s : ℂ => s^2) nonrealNhdsOne nonrealNhdsOne := by
  have hc : Tendsto (fun s : ℂ => s^2) nonrealNhdsOne (𝓝 (1 : ℂ)) := by
    have h : ContinuousAt (fun s : ℂ => s^2) 1 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hc
  have hr : ∀ᶠ s in nonrealNhdsOne, s.re≠0 :=
    ((Complex.continuous_re.continuousAt).eventually_ne (by norm_num : (1 : ℂ).re≠0)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hr,self_mem_nhdsWithin] with s hs him
  change (s^2).im≠0
  rw [pow_two,Complex.mul_im]
  have he : s.re*s.im+s.im*s.re=2*s.re*s.im := by ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hs) him

/-- Certified Ward limits pull back to the actual Fock family parameter. -/
theorem genericSymbolCoefficient_square_tendsto (self : Bool) (N n : ℕ)
    (hN : channelBound self≤N) (hn : n≤channelBound self) :
    Tendsto (fun s => OrbIcoV.genericSymbolCoefficient self N (s^2) n) nonrealNhdsOne
      (𝓝 ((((valueJets self n)[0]?).getD 0 : ℚ) : ℂ)) :=
  (genericSymbolCoefficient_tendsto self N n hN hn).comp square_tendsto_nonreal

end VOA.Classification.COne.OrbIcoW
