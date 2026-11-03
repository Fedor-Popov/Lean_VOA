/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureCountTypes
import VOA.DeligneAudit.DeligneCharacterDemazureEnergy
import VOA.DeligneAudit.DeligneCharacterG2Energy

/-!
# The unclamped `G₂` route

Sibling of the `G2Fusion.lean` (unchanged), following the `D₄` unclamped route:

* `g2HilbInt m N` (the algorithmic integer coefficients) and `g2FusionFZ := fusionOf g2HilbSeriesZ`;
* `G2DemazureEnergy`: energies `≥ 0` in `demazureChar G₂ m` — **proved** (`g2DemazureEnergy_holds`) by
  the convexity invariant of `DeligneCharacterDemazureEnergy` with `F` the `W`-orbit of `θ^∨`;
* `g2DemazureCountZ`, `g2FusionFZ_count`: the count `15^m` / `14^m` from `g2_demazure_total`
  (proved) and `G2DemazureEnergy`;
* `g2_fusionModuleBoundZ_of_squeeze`: U5 for `g2FusionFZ` from the squeeze inputs;
* `g2HilbInt_nonneg_of_U5Z`, `g2FusionF_eq_Z`: coefficient positivity is derived from U5 (as for `D₄`), so
  `g2FusionF = g2FusionFZ`;
* **`g2_classicallyFree_Z`**: the `G₂` headline with U5 stated for `g2FusionFZ`, and
  **`g2_classicallyFree_Z_of_squeeze`**: the same with U5 replaced by `G2DemazureEnergy` + squeeze inputs.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector SectorWeyl
  VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.DeligneCharacter.DemCount
  VOA.DeligneAudit.DeligneCharacter.D4Wp

noncomputable section

/-- `[q^N] q^{m²} C_m|_{z=1}` for `G₂`, unclamped. -/
def g2HilbInt (m : ℕ) (N : ℤ) : ℤ := hilbIntG cartanG2 thetaG2 wordG2 m N

theorem g2DemazureHilb_eq_toNat (m N : ℕ) : g2DemazureHilb m N = (g2HilbInt m N).toNat := rfl

/-- The unclamped `G₂` Demazure series. -/
def g2HilbSeriesZ (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun N => (g2HilbInt n N : ℚ)

/-- The `G₂` fusion series of the unclamped Demazure series. -/
def g2FusionFZ : ℕ → PowerSeries ℚ := fusionOf g2HilbSeriesZ


theorem g2DemazureCountZ (hE : G2DemazureEnergy) (m : ℕ) :
    ∃ B, (∀ N : ℕ, B ≤ N → g2HilbInt m N = 0) ∧ ∑ N ∈ Finset.range B, g2HilbInt m N = 15 ^ m := by
  obtain ⟨B, h0, hs⟩ := hilbIntG_count cartanG2 thetaG2 wordG2 m (hE m)
  exact ⟨B, h0, hs.trans (g2_demazure_total m)⟩

theorem g2FusionFZ_count (hE : G2DemazureEnergy) (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (g2FusionFZ m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (g2FusionFZ m) = ((14 : ℕ) : ℚ) ^ m := by
  refine fusionOf_count _ 14 (fun n => ?_) m
  obtain ⟨B, hB, hs⟩ := g2DemazureCountZ hE n
  refine ⟨B, fun N hN => ?_, ?_⟩
  · rw [g2HilbSeriesZ, coeff_mk, hB N hN]; simp
  · simp only [g2HilbSeriesZ, coeff_mk]
    rw [← Int.cast_sum, hs]
    norm_num

/-- **U5 for `g2FusionFZ`** from the energy input, the squeeze inputs and the universal bound. -/
theorem g2_fusionModuleBoundZ_of_squeeze (S : DeligneSectorData) (hn : S.n = 14)
    {M : ℕ → ℕ → PowerSeries ℚ} (hE : G2DemazureEnergy)
    (h : FusionSqueezeInputsG g2HilbSeriesZ 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S g2FusionFZ :=
  fusionModuleBoundG_of_squeeze S hn h (g2FusionFZ_count hE) huniv

/-- **Coefficient positivity** from U5 for `g2FusionFZ` (as `D4Wp.hilbInt_nonneg_of_U5Z`). -/
theorem g2HilbInt_nonneg_of_U5Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S g2FusionFZ)
    (m N : ℕ) : 0 ≤ g2HilbInt m N := by
  have hF : ∀ k, NN (g2FusionFZ k) := fun k b => F_coeff_nonneg hU5 k b
  have h := congrArg (coeff N) ((mixedFusionRecursion_fusionOf g2HilbSeriesZ).eq m)
  rw [g2HilbSeriesZ, coeff_mk, VOA.DeligneGaussian.mixed_eq] at h
  have hnn : NN (∑ d ∈ Finset.range (m + 1), X ^ (d * (m + 0)) *
      VOA.DeligneGaussian.qbinom (X : PowerSeries ℚ) m d * g2FusionFZ (m + 0 - d)) :=
    NN_sum _ _ fun d _ => ((NN_X_pow _).mul (NN_qbinom _ _)).mul (hF _)
  have := hnn N
  rw [g2FusionFZ] at this
  rw [← h] at this
  exact_mod_cast this

theorem hilbSeries_g2_eq_Z (hc : ∀ m N : ℕ, 0 ≤ g2HilbInt m N) :
    hilbSeries g2DemazureHilb = g2HilbSeriesZ := by
  funext m
  ext N : 1
  rw [hilbSeries, g2HilbSeriesZ, coeff_mk, coeff_mk, g2DemazureHilb_eq_toNat]
  have := hc m N
  rw [show ((g2HilbInt m N).toNat : ℚ) = (((g2HilbInt m N).toNat : ℤ) : ℚ) by push_cast; rfl,
    Int.toNat_of_nonneg this]

/-- **`g2FusionF = g2FusionFZ`** given U5 for the unclamped series. -/
theorem g2FusionF_eq_Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S g2FusionFZ) :
    g2FusionF = g2FusionFZ := by
  rw [g2FusionF, hilbSeries_g2_eq_Z (g2HilbInt_nonneg_of_U5Z hU5), g2FusionFZ]

/-- **The `G₂` headline, unclamped U5**: sibling of `g2_classicallyFree` with
`hU5 : FusionModuleBoundG S g2FusionFZ` (coefficient positivity is derived). -/
theorem g2_classicallyFree_Z {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (P : CurrentC2Presentation .G2 W) (S : DeligneSectorData)
    (hsurj : CurrentJetSurjectivity .G2 W P)
    (hgeom : GeometricCarrierEmbedding .G2 W P
      (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel))
    (hU5 : FusionModuleBoundG S g2FusionFZ) (hD : DivisorComparisonG S)
    (hc : W.centralCharge = -2 * (((4 : ℕ) : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hrel : DeligneMLDE.VacuumQuarticRelation W κ)
    (hF1 : G2Star.G2DemazureFermionic) (hF2 : G2Star.G2FermionicKW) :
    CaseClassicallyFree .G2 W P ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom = P.ideal :=
  g2_classicallyFree W P S hsurj hgeom ((g2FusionF_eq_Z hU5) ▸ hU5) hD hc hvac hrel hF1 hF2

/-- **The `G₂` headline from the squeeze**: U5 replaced by `G2DemazureEnergy`, the squeeze inputs
for the unclamped series and the universal bound. -/
theorem g2_classicallyFree_Z_of_squeeze {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (P : CurrentC2Presentation .G2 W) (S : DeligneSectorData)
    (hn : S.n = 14) {M : ℕ → ℕ → PowerSeries ℚ}
    (hsurj : CurrentJetSurjectivity .G2 W P)
    (hgeom : GeometricCarrierEmbedding .G2 W P
      (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel))
    (hE : G2DemazureEnergy) (h : FusionSqueezeInputsG g2HilbSeriesZ 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m))
    (hD : DivisorComparisonG S)
    (hc : W.centralCharge = -2 * (((4 : ℕ) : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hrel : DeligneMLDE.VacuumQuarticRelation W κ)
    (hF1 : G2Star.G2DemazureFermionic) (hF2 : G2Star.G2FermionicKW) :
    CaseClassicallyFree .G2 W P ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom = P.ideal :=
  g2_classicallyFree_Z W P S hsurj hgeom (g2_fusionModuleBoundZ_of_squeeze S hn hE h huniv) hD hc
    hvac hrel hF1 hF2

/-! ## Unconditional forms (energy proved) -/

/-- `g2FusionFZ m (1) = 14^m`, unconditionally. -/
theorem g2FusionFZ_count_holds (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (g2FusionFZ m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (g2FusionFZ m) = ((14 : ℕ) : ℚ) ^ m :=
  g2FusionFZ_count g2DemazureEnergy_holds m

/-- **U5 for `g2FusionFZ`** from the squeeze inputs and the universal bound alone. -/
theorem g2_fusionModuleBoundZ_of_squeeze' (S : DeligneSectorData) (hn : S.n = 14)
    {M : ℕ → ℕ → PowerSeries ℚ} (h : FusionSqueezeInputsG g2HilbSeriesZ 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S g2FusionFZ :=
  g2_fusionModuleBoundZ_of_squeeze S hn g2DemazureEnergy_holds h huniv

/-- **The `G₂` headline from the squeeze**, with no Demazure count/energy/positivity input. -/
theorem g2_classicallyFree_Z_of_squeeze' {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (P : CurrentC2Presentation .G2 W) (S : DeligneSectorData)
    (hn : S.n = 14) {M : ℕ → ℕ → PowerSeries ℚ}
    (hsurj : CurrentJetSurjectivity .G2 W P)
    (hgeom : GeometricCarrierEmbedding .G2 W P
      (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel))
    (h : FusionSqueezeInputsG g2HilbSeriesZ 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m))
    (hD : DivisorComparisonG S)
    (hc : W.centralCharge = -2 * (((4 : ℕ) : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hrel : DeligneMLDE.VacuumQuarticRelation W κ)
    (hF1 : G2Star.G2DemazureFermionic) (hF2 : G2Star.G2FermionicKW) :
    CaseClassicallyFree .G2 W P ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom = P.ideal :=
  g2_classicallyFree_Z_of_squeeze W P S hn hsurj hgeom g2DemazureEnergy_holds h huniv hD hc hvac
    hrel hF1 hF2

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.g2DemazureEnergy_small
#print axioms VOA.DeligneAudit.DeligneCarrier.g2FusionFZ_count
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_fusionModuleBoundZ_of_squeeze
#print axioms VOA.DeligneAudit.DeligneCarrier.g2FusionF_eq_Z
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_classicallyFree_Z
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_classicallyFree_Z_of_squeeze
#print axioms VOA.DeligneAudit.DeligneCarrier.g2DemazureEnergy_holds
#print axioms VOA.DeligneAudit.DeligneCarrier.g2FusionFZ_count_holds
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_fusionModuleBoundZ_of_squeeze'
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_classicallyFree_Z_of_squeeze'
end AxiomAudit
