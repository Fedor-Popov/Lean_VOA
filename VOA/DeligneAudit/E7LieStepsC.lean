import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck018
import VOA.DeligneAudit.E7LieStepCheck019
import VOA.DeligneAudit.E7LieStepCheck020
import VOA.DeligneAudit.E7LieStepCheck021
import VOA.DeligneAudit.E7LieStepCheck022
import VOA.DeligneAudit.E7LieStepCheck023
import VOA.DeligneAudit.E7LieStepCheck024
import VOA.DeligneAudit.E7LieStepCheck025
import VOA.DeligneAudit.E7LieStepCheck026

/-! E₇ propagation steps 387 through 579, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok2 : (List.range' 387 193).all stepOK = true := by
  have h0 := steps_small_018
  have h1 : (List.range' 387 48).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 24) (right := 24) h0
      steps_small_019
  have h2 : (List.range' 387 72).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 48) (right := 24) h1
      steps_small_020
  have h3 : (List.range' 387 96).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 72) (right := 24) h2
      steps_small_021
  have h4 : (List.range' 387 120).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 96) (right := 24) h3
      steps_small_022
  have h5 : (List.range' 387 144).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 120) (right := 24) h4
      steps_small_023
  have h6 : (List.range' 387 168).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 144) (right := 24) h5
      steps_small_024
  have h7 : (List.range' 387 192).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 168) (right := 24) h6
      steps_small_025
  have h8 : (List.range' 387 193).all stepOK = true :=
    stepOK_range_append (start := 387) (left := 192) (right := 1) h7
      steps_small_026
  exact h8

end VOA.DeligneAudit.E7Lie
