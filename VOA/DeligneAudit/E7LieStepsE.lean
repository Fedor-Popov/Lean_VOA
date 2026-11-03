import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck036
import VOA.DeligneAudit.E7LieStepCheck037
import VOA.DeligneAudit.E7LieStepCheck038
import VOA.DeligneAudit.E7LieStepCheck039
import VOA.DeligneAudit.E7LieStepCheck040
import VOA.DeligneAudit.E7LieStepCheck041
import VOA.DeligneAudit.E7LieStepCheck042
import VOA.DeligneAudit.E7LieStepCheck043
import VOA.DeligneAudit.E7LieStepCheck044

/-! E₇ propagation steps 773 through 965, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok4 : (List.range' 773 193).all stepOK = true := by
  have h0 := steps_small_036
  have h1 : (List.range' 773 48).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 24) (right := 24) h0
      steps_small_037
  have h2 : (List.range' 773 72).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 48) (right := 24) h1
      steps_small_038
  have h3 : (List.range' 773 96).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 72) (right := 24) h2
      steps_small_039
  have h4 : (List.range' 773 120).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 96) (right := 24) h3
      steps_small_040
  have h5 : (List.range' 773 144).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 120) (right := 24) h4
      steps_small_041
  have h6 : (List.range' 773 168).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 144) (right := 24) h5
      steps_small_042
  have h7 : (List.range' 773 192).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 168) (right := 24) h6
      steps_small_043
  have h8 : (List.range' 773 193).all stepOK = true :=
    stepOK_range_append (start := 773) (left := 192) (right := 1) h7
      steps_small_044
  exact h8

end VOA.DeligneAudit.E7Lie
