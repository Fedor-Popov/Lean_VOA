import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck009
import VOA.DeligneAudit.E7LieStepCheck010
import VOA.DeligneAudit.E7LieStepCheck011
import VOA.DeligneAudit.E7LieStepCheck012
import VOA.DeligneAudit.E7LieStepCheck013
import VOA.DeligneAudit.E7LieStepCheck014
import VOA.DeligneAudit.E7LieStepCheck015
import VOA.DeligneAudit.E7LieStepCheck016
import VOA.DeligneAudit.E7LieStepCheck017

/-! E₇ propagation steps 194 through 386, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok1 : (List.range' 194 193).all stepOK = true := by
  have h0 := steps_small_009
  have h1 : (List.range' 194 48).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 24) (right := 24) h0
      steps_small_010
  have h2 : (List.range' 194 72).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 48) (right := 24) h1
      steps_small_011
  have h3 : (List.range' 194 96).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 72) (right := 24) h2
      steps_small_012
  have h4 : (List.range' 194 120).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 96) (right := 24) h3
      steps_small_013
  have h5 : (List.range' 194 144).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 120) (right := 24) h4
      steps_small_014
  have h6 : (List.range' 194 168).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 144) (right := 24) h5
      steps_small_015
  have h7 : (List.range' 194 192).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 168) (right := 24) h6
      steps_small_016
  have h8 : (List.range' 194 193).all stepOK = true :=
    stepOK_range_append (start := 194) (left := 192) (right := 1) h7
      steps_small_017
  exact h8

end VOA.DeligneAudit.E7Lie
