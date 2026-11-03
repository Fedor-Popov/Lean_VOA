/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4Final

/-!
# U6 for `D₄` by the choice of `F`

As for `A₂` (the `DeligneFusionInverse`), Ravinder's mixed recursion
`Dem n = ∑_{d ≤ n} q^{dn} [n,d]_q F_{n-d}` (`MixedFusionRecursion F Dem`) is unitriangular in `F`:
the `d = 0` term is `F n`.  So for **any** `Dem` it has a unique solution `fusionOf Dem`
(`mixedFusionRecursion_fusionOf`, `fusionOf_unique`).  For `D₄`, `d4FusionF := fusionOf (hilbSeries
d4DemazureHilb)`, and the `D₄` headline rests on U5 (for this explicit `F`) and Demazure positivity
alone (`D4Lie.classicallyFree_of_fusionBound`).

The shape of the recursion is the one fixed by `MixedFusionRecursion` (`q^{2a+b+1}` steps, Gaussian
`[n,d]_q`); this shape was also checked numerically for `D₄` outside Lean.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneGaussian

noncomputable section

/-- The unique solution of the mixed recursion for a given Demazure series. -/
def fusionOf (Dem : ℕ → PowerSeries ℚ) : ℕ → PowerSeries ℚ
  | n => Dem n -
      ∑ d : Fin n, X ^ ((d.1 + 1) * n) * qbinom (X : PowerSeries ℚ) n (d.1 + 1) *
        fusionOf Dem (n - (d.1 + 1))
decreasing_by omega

theorem fusionOf_eq (Dem : ℕ → PowerSeries ℚ) (n : ℕ) : fusionOf Dem n = Dem n -
    ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) * qbinom (X : PowerSeries ℚ) n (d + 1) *
      fusionOf Dem (n - (d + 1)) := by
  rw [fusionOf, Fin.sum_univ_eq_sum_range (fun d => X ^ ((d + 1) * n) *
    qbinom (X : PowerSeries ℚ) n (d + 1) * fusionOf Dem (n - (d + 1))) n]

theorem mixed_zero_split (F : ℕ → PowerSeries ℚ) (n : ℕ) :
    mixed (X : PowerSeries ℚ) F n 0 = F n +
      ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) * qbinom (X : PowerSeries ℚ) n (d + 1) *
        F (n - (d + 1)) := by
  rw [mixed_eq, Finset.sum_range_succ']
  simp only [zero_mul, pow_zero, qbinom_zero_right, mul_one, one_mul, add_zero, Nat.sub_zero]
  ring

/-- **U6 holds for `fusionOf Dem`** (by construction). -/
theorem mixedFusionRecursion_fusionOf (Dem : ℕ → PowerSeries ℚ) :
    MixedFusionRecursion (fusionOf Dem) Dem := by
  refine ⟨fun n => ?_⟩
  rw [mixed_zero_split, fusionOf_eq Dem n]
  ring

/-- Uniqueness: any solution of the mixed recursion is `fusionOf Dem`. -/
theorem fusionOf_unique {F Dem : ℕ → PowerSeries ℚ} (h : MixedFusionRecursion F Dem) (n : ℕ) :
    F n = fusionOf Dem n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e := h.eq n
    rw [mixed_zero_split] at e
    rw [fusionOf_eq, e]
    have hs : ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) * qbinom (X : PowerSeries ℚ) n (d + 1) *
        F (n - (d + 1)) = ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) *
          qbinom (X : PowerSeries ℚ) n (d + 1) * fusionOf Dem (n - (d + 1)) :=
      Finset.sum_congr rfl fun d hd => by
        simp only [Finset.mem_range] at hd; rw [ih _ (by omega)]
    rw [hs]; ring

/-- The `D₄` fusion characters: the unique solution of the mixed recursion. -/
def d4FusionF : ℕ → PowerSeries ℚ :=
  fusionOf (hilbSeries VOA.DeligneAudit.DeligneCharacter.d4DemazureHilb)

theorem mixedFusionRecursion_d4FusionF :
    MixedFusionRecursion d4FusionF
      (hilbSeries VOA.DeligneAudit.DeligneCharacter.d4DemazureHilb) :=
  mixedFusionRecursion_fusionOf _

end

end VOA.DeligneAudit.DeligneCarrier

namespace VOA.DeligneAudit.D4Lie

open VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCarrier
  VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.DeligneSector.D4
  VOA.DeligneAudit.DeligneSector

/-- **D₄ Deligne classical freeness from U5 (for `d4FusionF`) and Demazure positivity.** U6 is
discharged by the choice of `F`. -/
theorem classicallyFree_of_fusionBound (hU5 : FusionModuleBoundG D4sector d4FusionF)
    (hpos : D4K.D4DemazurePositivity) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  classicallyFree_of_fusion d4FusionF hU5 mixedFusionRecursion_d4FusionF hpos

end VOA.DeligneAudit.D4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.mixedFusionRecursion_fusionOf
#print axioms VOA.DeligneAudit.DeligneCarrier.fusionOf_unique
#print axioms VOA.DeligneAudit.DeligneCarrier.mixedFusionRecursion_d4FusionF
#print axioms VOA.DeligneAudit.D4Lie.classicallyFree_of_fusionBound
end AxiomAudit
