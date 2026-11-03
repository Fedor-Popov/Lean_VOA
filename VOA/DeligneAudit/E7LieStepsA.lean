import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck000
import VOA.DeligneAudit.E7LieStepCheck001
import VOA.DeligneAudit.E7LieStepCheck002
import VOA.DeligneAudit.E7LieStepCheck003
import VOA.DeligneAudit.E7LieStepCheck004
import VOA.DeligneAudit.E7LieStepCheck005
import VOA.DeligneAudit.E7LieStepCheck006
import VOA.DeligneAudit.E7LieStepCheck007
import VOA.DeligneAudit.E7LieStepCheck008

/-! E₇ propagation steps 1 through 193, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok0 : (List.range' 1 193).all stepOK = true := by
  have h0 := steps_small_000
  have h1 : (List.range' 1 48).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 24) (right := 24) h0
      steps_small_001
  have h2 : (List.range' 1 72).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 48) (right := 24) h1
      steps_small_002
  have h3 : (List.range' 1 96).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 72) (right := 24) h2
      steps_small_003
  have h4 : (List.range' 1 120).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 96) (right := 24) h3
      steps_small_004
  have h5 : (List.range' 1 144).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 120) (right := 24) h4
      steps_small_005
  have h6 : (List.range' 1 168).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 144) (right := 24) h5
      steps_small_006
  have h7 : (List.range' 1 192).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 168) (right := 24) h6
      steps_small_007
  have h8 : (List.range' 1 193).all stepOK = true :=
    stepOK_range_append (start := 1) (left := 192) (right := 1) h7
      steps_small_008
  exact h8

end VOA.DeligneAudit.E7Lie

#print axioms VOA.DeligneAudit.E7Lie.steps_ok0
