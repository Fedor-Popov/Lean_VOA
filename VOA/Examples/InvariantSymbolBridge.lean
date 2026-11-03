import VOA.Examples.LeeYangCharacterEndpoint

/-!
# The leading-symbol input only needs an upper bound

`LeadingInvariantSymbolDimension S` asks for the *equality*
`dim H(Q⁻)_{(j,0)} = leadingCoefficient n j`.  Its two uses in the shortcut chain
(`cohom_prefix_bound` inside the image squeeze, and
`integralHarmonicSupport_of_symbols`) only consume the inequality `≤`.  Rather than
re-thread the whole concrete chain, we show the equality is *forced* by the inequality:

* lower half: the PBW piece of `L(-22/5)` is a quotient of the filtered image of the
  universal Virasoro classes, which embeds in the cohomology prefix
  (`piece_finrank_le_cohomFilt`, pure linear algebra);
* upper half: the harmonic bound `finrank_cohomFilt_row_le_lead` plus the hypothesis;
* the refined character `LeeYangPBWCharacter` closes the sandwich, and a sum of
  termwise `≤` with equal totals is termwise `=`.

`leadingInvariantSymbolDimension_of_bound` — `#print axioms`-clean, conditional only on
`character` and `filtered` (both supplied in the concrete chain; `filtered` is proved).

`leeYang_gradedUnitary_of_affine_levelOne_rr_bound` — the current endpoint with `symbols`
replaced by its upper-bound form `LeadingInvariantSymbolBound`.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VirSimple VirGoodFil
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- The upper-bound form of `LeadingInvariantSymbolDimension`: the actual leading
cohomology at ghost number zero is no larger than the gap-two coefficient
(and hence vanishes at odd and negative `j`). -/
def LeadingInvariantSymbolBound (S : ConcreteKahlerGeometry) : Prop :=
  ∀ n (hp : IsPosOn (S.geometry n).P ⊤) j,
    Module.finrank ℂ ((S.model n hp).leadCohom (j, 0)) ≤ leadingCoefficient n j

theorem leadingInvariantSymbolBound_of_dimension (S : ConcreteKahlerGeometry)
    (h : LeadingInvariantSymbolDimension S) : LeadingInvariantSymbolBound S :=
  fun n hp j => (h n hp j).le

/-- Abstract lower half of the squeeze: a filtered class family whose kernel is killed by
`g` makes each target piece no larger than the corresponding cohomology prefix. -/
theorem piece_finrank_le_cohomFilt {K : Type*} [AddCommGroup K] [Module ℂ K]
    [FiniteDimensional ℂ K] {U T : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup T] [Module ℂ T]
    (C : KahlerComplex K) (f : U →ₗ[ℂ] cycleQuotient C.D) (g : U →ₗ[ℂ] T)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) (P : Submodule ℂ U) (Q : Submodule ℂ T)
    (hquotient : P.map g = Q) (F : Submodule ℂ (cycleQuotient C.D))
    (hfiltered : P.map f ≤ F) :
    Module.finrank ℂ Q ≤ Module.finrank ℂ F := by
  have hQ : (P.map f.rangeRestrict).map (rangeFactor f g hker) = Q :=
    rangeFactor_prefix f g hker P Q hquotient
  have hsub : (P.map f.rangeRestrict).map (LinearMap.range f).subtype = P.map f := by
    rw [← Submodule.map_comp]
    rfl
  calc Module.finrank ℂ Q
      = Module.finrank ℂ ((P.map f.rangeRestrict).map (rangeFactor f g hker)) := by rw [hQ]
    _ ≤ Module.finrank ℂ (P.map f.rangeRestrict) := Submodule.finrank_map_le _ _
    _ ≤ Module.finrank ℂ F :=
        finrank_le_of_filtered_injective (LinearMap.range f).subtype Subtype.val_injective
          _ F (by rw [hsub]; exact hfiltered)

/-- Termwise `≤` with equal totals is termwise `=`. -/
theorem eq_of_sum_le_of_le {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    (hle : ∀ i ∈ s, a i ≤ b i) (hsum : ∑ i ∈ s, b i ≤ ∑ i ∈ s, a i) :
    ∀ i ∈ s, a i = b i :=
  (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle) hsum)

/-- **The upper bound forces the leading-symbol equality.** Given the refined character
and the (proved, in the concrete chain) filtration of the universal Virasoro classes, the
inequality `LeadingInvariantSymbolBound` implies `LeadingInvariantSymbolDimension`. -/
theorem leadingInvariantSymbolDimension_of_bound (S : ConcreteKahlerGeometry)
    (character : LeeYangPBWCharacter) (filtered : UniversalClassFiltered S)
    (hb : LeadingInvariantSymbolBound S) : LeadingInvariantSymbolDimension S := by
  intro n hp j
  by_cases hj : 0 ≤ j
  swap
  · have h := hb n hp j
    have h0 : leadingCoefficient n j = 0 := by
      unfold leadingCoefficient; rw [if_neg (by omega)]
    rw [h0] at h ⊢
    omega
  set C := S.model n hp
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = (p : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
  have hmem : (p : ℤ) ∈ Finset.Icc 0 (2 * (p : ℤ)) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  refine eq_of_sum_le_of_le (Finset.Icc 0 (2 * (p : ℤ)))
    (fun j => Module.finrank ℂ (C.leadCohom (j, 0))) (leadingCoefficient n)
    (fun j _ => hb n hp j) ?_ _ hmem
  calc ∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), leadingCoefficient n j
      = Module.finrank ℂ ((virGradedFlag leeYangC).pieceIn p n) := (character n p).symm
    _ ≤ Module.finrank ℂ (C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)) :=
        piece_finrank_le_cohomFilt C (modelUniversalClass S n hp) (simpleWeightProjection n)
          (modelUniversalClass_ker_le S n hp) (universalPrefix p n) _
          (simpleWeightProjection_prefix p n) _ (filtered n hp p)
    _ ≤ _ := C.finrank_cohomFilt_row_le_lead _ 0

/-- The concrete Kähler geometry of the current endpoint. -/
abbrev endpointKahler (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ConcreteKahlerGeometry :=
  sp2Kahler hA LevelOneUnitary.bUnitary bgPG_pos bgGh bgGh_isStd
    ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg
      LevelOneUnitary.bUnitary).sp2

/-- The universal Virasoro classes are filtered in the concrete endpoint geometry
(proved: vacuum and creation-mode generator tests for the standard ghost grading). -/
theorem endpointKahler_filtered (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    UniversalClassFiltered (endpointKahler hA) :=
  have hpAll := concreteKahler_weakGU LevelOneUnitary.bUnitary bgPG_pos _ hA
    auxiliaryGradedUnitary
  universalClassFiltered_of_generators _ hpAll
    (interpretedGenerators_std bgGh hA LevelOneUnitary.bUnitary bgPG_pos _ _ _ bgGh_isStd hpAll)

/-- **Affine GU ⇒ Lee–Yang GU**, with `symbols` weakened to the upper bound
`LeadingInvariantSymbolBound`. `#print axioms`-clean, conditional on `hA` (the hypothesis),
`symbolsLe`, and the classical Rogers–Ramanujan lower bound `lower`. -/
theorem leeYang_gradedUnitary_of_affine_levelOne_rr_bound
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (symbolsLe : LeadingInvariantSymbolBound (endpointKahler hA))
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_levelOne_rr hA
    (leadingInvariantSymbolDimension_of_bound _
      (LeeYangCharacter.leeYangPBWCharacter_iff_lowerBound.mpr lower)
      (endpointKahler_filtered hA) symbolsLe) lower

end

end VOA.ConcreteHodge
