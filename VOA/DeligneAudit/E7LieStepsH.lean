import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck063
import VOA.DeligneAudit.E7LieStepCheck064
import VOA.DeligneAudit.E7LieStepCheck065
import VOA.DeligneAudit.E7LieStepCheck066
import VOA.DeligneAudit.E7LieStepCheck067
import VOA.DeligneAudit.E7LieStepCheck068
import VOA.DeligneAudit.E7LieStepCheck069
import VOA.DeligneAudit.E7LieStepCheck070

/-! E₇ propagation steps 1352 through 1538, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok7 : (List.range' 1352 187).all stepOK = true := by
  have h0 := steps_small_063
  have h1 : (List.range' 1352 48).all stepOK = true :=
    stepOK_range_append (start := 1352) (left := 24) (right := 24) h0
      steps_small_064
  have h2 : (List.range' 1352 72).all stepOK = true :=
    stepOK_range_append (start := 1352) (left := 48) (right := 24) h1
      steps_small_065
  have h3 : (List.range' 1352 96).all stepOK = true :=
    stepOK_range_append (start := 1352) (left := 72) (right := 24) h2
      steps_small_066
  have h4 : (List.range' 1352 120).all stepOK = true :=
    stepOK_range_append (start := 1352) (left := 96) (right := 24) h3
      steps_small_067
  have h5 : (List.range' 1352 144).all stepOK = true :=
    stepOK_range_append (start := 1352) (left := 120) (right := 24) h4
      steps_small_068
  have h6 : (List.range' 1352 168).all stepOK = true :=
    stepOK_range_append (start := 1352) (left := 144) (right := 24) h5
      steps_small_069
  have h7 : (List.range' 1352 187).all stepOK = true :=
    stepOK_range_append (start := 1352) (left := 168) (right := 19) h6
      steps_small_070
  exact h7

end VOA.DeligneAudit.E7Lie

#print axioms VOA.DeligneAudit.E7Lie.steps_ok7
