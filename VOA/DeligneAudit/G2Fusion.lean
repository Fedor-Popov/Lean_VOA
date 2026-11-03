/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionSqueezeG
import VOA.DeligneAudit.G2StarFermionic
import VOA.DeligneAudit.G2StarUnconditional
import VOA.DeligneAudit.DeligneMLDETypes

/-!
# The fusion layer for `G₂`, and the `G₂` headline in U5 form

* **Generic capstone without U6** (`classicallyFree_of_sectorFusion`): for any case, VOA `W`,
  presentation `P`, sector data `S` and Demazure data `hilb`, the case is classically free from
  current-jet surjectivity, the geometric carrier embedding, U5 for `fusionOf (hilbSeries hilb)`
  (the unique solution of the mixed recursion), the divisor comparison, and the Demazure bound.
  U6 holds by the choice of `F`.
* `g2FusionF := fusionOf (hilbSeries g2DemazureHilb)`; with the named count `G2DemazureCount`
  (`∑_N g2DemazureHilb n N = 15ⁿ`), `g2FusionF m (1) = 14^m` (`g2FusionF_count`), and U5 for `G₂`
  from the squeeze inputs (`g2_fusionModuleBound_of_squeeze`).
* **The `G₂` headline** (`g2_classicallyFree`): stated against an abstract `G₂` sector `S`
  (`G2LieHeadline` instantiates it with the concrete `G2sector`). It rests on U5 for `g2FusionF`, the divisor comparison, the
  geometric data (`hsurj`, `hgeom`), the vacuum quartic relation at `c = -10`, and the two halves
  `G2DemazureFermionic`, `G2FermionicKW` of the Demazure side. Ramanujan's identities, the level-3
  core and Lorenz's formula are already proved (`G2StarUnconditional`).

Numerical evidence for the `G₂` fusion layer (computed outside Lean): the inverse of the mixed recursion has
nonnegative coefficients, value `14^m` at `q = 1` and `[q⁰] = dim V(mθ)` for `m ≤ 18`; `∑_N
g2DemazureHilb n N = 15ⁿ` for `n ≤ 18`.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneCharacter

open scoped BigOperators

noncomputable section

/-- **Generic capstone with U6 discharged by the choice of `F`.** -/
theorem classicallyFree_of_sectorFusion {case : HigherRankDeligneCase} {V : Type*}
    [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V} (P : CurrentC2Presentation case W)
    (S : DeligneSectorData) (hilb : ℕ → ℕ → ℕ)
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P
      (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel))
    (hU5 : FusionModuleBoundG S (fusionOf (hilbSeries hilb))) (hD : DivisorComparisonG S)
    (hchr : DemazureBoundFor W hilb) :
    CaseClassicallyFree case W P ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom = P.ideal :=
  caseClassicallyFree_of_lowerBound P (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel) hsurj
    hgeom (carrierCharacterLowerBound_of_sector S.toDeligneCarrierData hilb _
      (sectorFusionBoundG S _ hU5 hD) (mixedFusionRecursion_fusionOf _) hchr)

/-! ## `G₂` -/

/-- The `G₂` fusion characters: the unique solution of the mixed recursion. -/
def g2FusionF : ℕ → PowerSeries ℚ := fusionOf (hilbSeries g2DemazureHilb)

theorem mixedFusionRecursion_g2FusionF :
    MixedFusionRecursion g2FusionF (hilbSeries g2DemazureHilb) :=
  mixedFusionRecursion_fusionOf _

/-- **Named input**: `∑_N g2DemazureHilb n N = 15ⁿ` (`dim D(1,nθ) = dim W(θ)^{⊗n}`,
`W(θ) = 𝔤 ⊕ ℂ`; Fourier–Littelmann / Chari–Ion). Checked numerically for `n ≤ 18`. -/
def G2DemazureCount : Prop :=
  ∀ n, ∃ B, (∀ N, B ≤ N → g2DemazureHilb n N = 0) ∧
    ∑ N ∈ Finset.range B, g2DemazureHilb n N = 15 ^ n

theorem g2FusionF_count (hC : G2DemazureCount) (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (g2FusionF m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (g2FusionF m) = ((14 : ℕ) : ℚ) ^ m := by
  refine fusionOf_count _ 14 (fun n => ?_) m
  obtain ⟨B, hB, hs⟩ := hC n
  refine ⟨B, fun N hN => ?_, ?_⟩
  · rw [hilbSeries, coeff_mk, hB N hN]; simp
  · simp only [hilbSeries, coeff_mk]
    rw [← Nat.cast_sum, hs]
    norm_num

open SectorWeyl in
/-- U5 for `G₂` from the count, the squeeze inputs and the universal bound (any `G₂` sector with
`dim 𝔤 = 14`). -/
theorem g2_fusionModuleBound_of_squeeze (S : DeligneSectorData) (hn : S.n = 14)
    {M : ℕ → ℕ → PowerSeries ℚ} (hC : G2DemazureCount)
    (h : FusionSqueezeInputsG (hilbSeries g2DemazureHilb) 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S g2FusionF :=
  fusionModuleBoundG_of_squeeze S hn h (g2FusionF_count hC) huniv

/-- **The `G₂` headline in U5 form**, against an abstract `G₂` sector `S`. -/
theorem g2_classicallyFree {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (P : CurrentC2Presentation .G2 W) (S : DeligneSectorData)
    (hsurj : CurrentJetSurjectivity .G2 W P)
    (hgeom : GeometricCarrierEmbedding .G2 W P
      (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel))
    (hU5 : FusionModuleBoundG S g2FusionF) (hD : DivisorComparisonG S)
    (hc : W.centralCharge = -2 * (((4 : ℕ) : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hrel : DeligneMLDE.VacuumQuarticRelation W κ)
    (hF1 : G2Star.G2DemazureFermionic) (hF2 : G2Star.G2FermionicKW) :
    CaseClassicallyFree .G2 W P ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom = P.ideal :=
  classicallyFree_of_sectorFusion P S g2DemazureHilb hsurj hgeom hU5 hD
    (demazureBoundFor_of_Q
      (G2Star.g2StarIdentity_of_demazure (G2Star.g2DemazureEqKW_of_fermionic hF1 hF2))
      (DeligneMLDE.g2TargetLowerBound_of_quartic W hc hvac hrel))

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.classicallyFree_of_sectorFusion
#print axioms VOA.DeligneAudit.DeligneCarrier.g2FusionF_count
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_fusionModuleBound_of_squeeze
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_classicallyFree
end AxiomAudit
