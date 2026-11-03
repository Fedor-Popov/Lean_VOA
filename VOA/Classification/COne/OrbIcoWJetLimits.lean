import VOA.Classification.COne.OrbIcoWJetSequence
import VOA.Classification.COne.OrbIcoVGenericScalar

/-! Certified limits of the genuine finite Verma Ward coefficient family. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial Filter Topology

abbrev nonrealNhdsOne : Filter ℂ := 𝓝[{t : ℂ | t.im≠0}] (1 : ℂ)

theorem nonrealNhdsOne_le_punctured : nonrealNhdsOne≤𝓝[≠] (1 : ℂ) := by
  apply nhdsWithin_mono
  intro t ht
  change t≠1
  intro he
  subst t
  norm_num at ht

/-- The actual chosen Ward coefficient has the certified jet on the nonreal locus. -/
theorem genericSymbolCoefficient_jetApprox (self : Bool) (N n : ℕ)
    (hN : channelBound self≤N) (hn : n≤channelBound self) :
    JetApproxAlongPL nonrealNhdsOne (precisionAfter self n+1)
      (fun t => OrbIcoV.genericSymbolCoefficient self N t n) (valueJets self n) := by
  apply widthSequence_jetApprox self (fun n t => OrbIcoV.genericSymbolCoefficient self N t n)
    nonrealNhdsOne_le_punctured _ _ n hn
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact OrbIcoV.genericSymbolCoefficient_zero self N t ht
  · intro k hk hkn
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [widthSequenceError_eq_fin]
    exact OrbIcoV.genericSymbolCoefficient_recurrence self N k (hkn.trans hN) t ht

/-- Certified finite-precision specialization determines the actual coefficient limit. -/
theorem genericSymbolCoefficient_tendsto (self : Bool) (N n : ℕ)
    (hN : channelBound self≤N) (hn : n≤channelBound self) :
    Tendsto (fun t => OrbIcoV.genericSymbolCoefficient self N t n) nonrealNhdsOne
      (𝓝 ((((valueJets self n)[0]?).getD 0 : ℚ) : ℂ)) := by
  have h := genericSymbolCoefficient_jetApprox self N n hN hn
  simpa only [← Polynomial.coeff_zero_eq_eval_zero,coeff_zp] using
    h.tendsto (by omega) nonrealNhdsOne_le_punctured

/-- Xu's two vacuum-channel constants are actual limits of normalized Ward coefficients. -/
theorem generic_vac37_tendsto (N : ℕ) (hN : 38≤N) :
    Tendsto (fun t => OrbIcoV.genericSymbolCoefficient false N t 37) nonrealNhdsOne (𝓝 (xuU37 : ℂ)) := by
  simpa only [vac37_value] using genericSymbolCoefficient_tendsto false N 37 hN (by decide)

theorem generic_vac38_tendsto (N : ℕ) (hN : 38≤N) :
    Tendsto (fun t => OrbIcoV.genericSymbolCoefficient false N t 38) nonrealNhdsOne (𝓝 (xuU38 : ℂ)) := by
  simpa only [vac38_value] using genericSymbolCoefficient_tendsto false N 38 hN (by decide)

/-- Xu's two sixth-channel constants are actual limits of normalized Ward coefficients. -/
theorem generic_self19_tendsto (N : ℕ) (hN : 20≤N) :
    Tendsto (fun t => OrbIcoV.genericSymbolCoefficient true N t 19) nonrealNhdsOne (𝓝 (xuV19 : ℂ)) := by
  simpa only [self19_value] using genericSymbolCoefficient_tendsto true N 19 hN (by decide)

theorem generic_self20_tendsto (N : ℕ) (hN : 20≤N) :
    Tendsto (fun t => OrbIcoV.genericSymbolCoefficient true N t 20) nonrealNhdsOne (𝓝 (xuV20 : ℂ)) := by
  simpa only [self20_value] using genericSymbolCoefficient_tendsto true N 20 hN (by decide)

end VOA.Classification.COne.OrbIcoW
