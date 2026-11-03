import VOA.Classification.COne.OrbIcoWRecVac09
import VOA.Classification.COne.OrbIcoWRecSelf04
import VOA.Classification.COne.OrbIcoWJetAlgebra

/-! Complete finite exact jet certificates for Xu's four symbol coefficients.
The undivided equations retain every cancellation at a simple resonance. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW

def channelBound (self : Bool) : ℕ := if self then 20 else 38

theorem coefficientJets_correct (self : Bool) (n q : ℕ) (hn : n ≤ channelBound self) :
    coefficientJets self n q =
      (((widthCoefficients (precisionBefore self n) self n)[q]?).getD []) := by
  cases self with

  | false =>
    simp only [channelBound,Bool.false_eq_true,if_false,if_true] at hn
    interval_cases n
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac00Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac01Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac02Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac03Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac04Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac05Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac06Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac07Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac08Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac09Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac10Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac11Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac12Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac13Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac14Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac15Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac16Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac17Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac18Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac19Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac20Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac21Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac22Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac23Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac24Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac25Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac26Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac27Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac28Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac29Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac30Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac31Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac32Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac33Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac34Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac35Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac36Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac37Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) vac38Coeffs_correct.symm
      exact h
  | true =>
    simp only [channelBound,Bool.false_eq_true,if_false,if_true] at hn
    interval_cases n
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self00Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self01Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self02Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self03Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self04Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self05Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self06Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self07Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self08Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self09Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self10Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self11Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self12Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self13Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self14Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self15Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self16Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self17Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self18Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self19Coeffs_correct.symm
      exact h
    · have h := congrArg (fun a : List Jet => ((a[q]?).getD [])) self20Coeffs_correct.symm
      exact h

/-- Every exact sequence equation holds at the precision before division. -/
theorem jet_recurrence_holds (self : Bool) (n : ℕ) (hn0 : 1 ≤ n)
    (hn : n ≤ channelBound self) : JetRecurrence self n := by
  cases self with

  | false =>
    simp only [channelBound,Bool.false_eq_true,if_false,if_true] at hn
    interval_cases n
    · exact vac01_jet_recurrence
    · exact vac02_jet_recurrence
    · exact vac03_jet_recurrence
    · exact vac04_jet_recurrence
    · exact vac05_jet_recurrence
    · exact vac06_jet_recurrence
    · exact vac07_jet_recurrence
    · exact vac08_jet_recurrence
    · exact vac09_jet_recurrence
    · exact vac10_jet_recurrence
    · exact vac11_jet_recurrence
    · exact vac12_jet_recurrence
    · exact vac13_jet_recurrence
    · exact vac14_jet_recurrence
    · exact vac15_jet_recurrence
    · exact vac16_jet_recurrence
    · exact vac17_jet_recurrence
    · exact vac18_jet_recurrence
    · exact vac19_jet_recurrence
    · exact vac20_jet_recurrence
    · exact vac21_jet_recurrence
    · exact vac22_jet_recurrence
    · exact vac23_jet_recurrence
    · exact vac24_jet_recurrence
    · exact vac25_jet_recurrence
    · exact vac26_jet_recurrence
    · exact vac27_jet_recurrence
    · exact vac28_jet_recurrence
    · exact vac29_jet_recurrence
    · exact vac30_jet_recurrence
    · exact vac31_jet_recurrence
    · exact vac32_jet_recurrence
    · exact vac33_jet_recurrence
    · exact vac34_jet_recurrence
    · exact vac35_jet_recurrence
    · exact vac36_jet_recurrence
    · exact vac37_jet_recurrence
    · exact vac38_jet_recurrence
  | true =>
    simp only [channelBound,Bool.false_eq_true,if_false,if_true] at hn
    interval_cases n
    · exact self01_jet_recurrence
    · exact self02_jet_recurrence
    · exact self03_jet_recurrence
    · exact self04_jet_recurrence
    · exact self05_jet_recurrence
    · exact self06_jet_recurrence
    · exact self07_jet_recurrence
    · exact self08_jet_recurrence
    · exact self09_jet_recurrence
    · exact self10_jet_recurrence
    · exact self11_jet_recurrence
    · exact self12_jet_recurrence
    · exact self13_jet_recurrence
    · exact self14_jet_recurrence
    · exact self15_jet_recurrence
    · exact self16_jet_recurrence
    · exact self17_jet_recurrence
    · exact self18_jet_recurrence
    · exact self19_jet_recurrence
    · exact self20_jet_recurrence

/-- The five resonant pivots are simple; every other pivot is nonzero at zero. -/
theorem jet_pivot_holds (self : Bool) (n : ℕ) (hn0 : 1 ≤ n)
    (hn : n ≤ channelBound self) : JetPivot self n := by
  cases self with

  | false =>
    simp only [channelBound,Bool.false_eq_true,if_false,if_true] at hn
    interval_cases n
    · exact vac01_jet_pivot
    · exact vac02_jet_pivot
    · exact vac03_jet_pivot
    · exact vac04_jet_pivot
    · exact vac05_jet_pivot
    · exact vac06_jet_pivot
    · exact vac07_jet_pivot
    · exact vac08_jet_pivot
    · exact vac09_jet_pivot
    · exact vac10_jet_pivot
    · exact vac11_jet_pivot
    · exact vac12_jet_pivot
    · exact vac13_jet_pivot
    · exact vac14_jet_pivot
    · exact vac15_jet_pivot
    · exact vac16_jet_pivot
    · exact vac17_jet_pivot
    · exact vac18_jet_pivot
    · exact vac19_jet_pivot
    · exact vac20_jet_pivot
    · exact vac21_jet_pivot
    · exact vac22_jet_pivot
    · exact vac23_jet_pivot
    · exact vac24_jet_pivot
    · exact vac25_jet_pivot
    · exact vac26_jet_pivot
    · exact vac27_jet_pivot
    · exact vac28_jet_pivot
    · exact vac29_jet_pivot
    · exact vac30_jet_pivot
    · exact vac31_jet_pivot
    · exact vac32_jet_pivot
    · exact vac33_jet_pivot
    · exact vac34_jet_pivot
    · exact vac35_jet_pivot
    · exact vac36_jet_pivot
    · exact vac37_jet_pivot
    · exact vac38_jet_pivot
  | true =>
    simp only [channelBound,Bool.false_eq_true,if_false,if_true] at hn
    interval_cases n
    · exact self01_jet_pivot
    · exact self02_jet_pivot
    · exact self03_jet_pivot
    · exact self04_jet_pivot
    · exact self05_jet_pivot
    · exact self06_jet_pivot
    · exact self07_jet_pivot
    · exact self08_jet_pivot
    · exact self09_jet_pivot
    · exact self10_jet_pivot
    · exact self11_jet_pivot
    · exact self12_jet_pivot
    · exact self13_jet_pivot
    · exact self14_jet_pivot
    · exact self15_jet_pivot
    · exact self16_jet_pivot
    · exact self17_jet_pivot
    · exact self18_jet_pivot
    · exact self19_jet_pivot
    · exact self20_jet_pivot
set_option maxHeartbeats 1000000 in
-- Only the literal constant coefficient and the published rational value are compared.
theorem vac37_value : ((valueJets false 37)[0]?).getD 0 = xuU37 := by decide +kernel
set_option maxHeartbeats 1000000 in
-- Only the literal constant coefficient and the published rational value are compared.
theorem vac38_value : ((valueJets false 38)[0]?).getD 0 = xuU38 := by decide +kernel
set_option maxHeartbeats 1000000 in
-- Only the literal constant coefficient and the published rational value are compared.
theorem self19_value : ((valueJets true 19)[0]?).getD 0 = xuV19 := by decide +kernel
set_option maxHeartbeats 1000000 in
-- Only the literal constant coefficient and the published rational value are compared.
theorem self20_value : ((valueJets true 20)[0]?).getD 0 = xuV20 := by decide +kernel

/-- The endpoint jets retain a constant coefficient after all resonances. -/
theorem endpoint_precisions :
    precisionAfter false 37=1 ∧ precisionAfter false 38=1 ∧
      precisionAfter true 19=1 ∧ precisionAfter true 20=1 := by decide +kernel

/-- All four exact scalar limits are nonzero. -/
theorem endpoint_values_positive :
    (0 : ℚ) < ((valueJets false 37)[0]?).getD 0 ∧
    (0 : ℚ) < ((valueJets false 38)[0]?).getD 0 ∧
    (0 : ℚ) < ((valueJets true 19)[0]?).getD 0 ∧
    (0 : ℚ) < ((valueJets true 20)[0]?).getD 0 := by
  rw [vac37_value,vac38_value,self19_value,self20_value]
  norm_num [xuU37,xuU38,xuV19,xuV20]

end VOA.Classification.COne.OrbIcoW
