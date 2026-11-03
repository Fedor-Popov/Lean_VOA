import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck054
import VOA.DeligneAudit.E7LieStepCheck055
import VOA.DeligneAudit.E7LieStepCheck056
import VOA.DeligneAudit.E7LieStepCheck057
import VOA.DeligneAudit.E7LieStepCheck058
import VOA.DeligneAudit.E7LieStepCheck059
import VOA.DeligneAudit.E7LieStepCheck060
import VOA.DeligneAudit.E7LieStepCheck061
import VOA.DeligneAudit.E7LieStepCheck062

/-! E₇ propagation steps 1159 through 1351, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok6 : (List.range' 1159 193).all stepOK = true := by
  have h0 := steps_small_054
  have h1 : (List.range' 1159 48).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 24) (right := 24) h0
      steps_small_055
  have h2 : (List.range' 1159 72).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 48) (right := 24) h1
      steps_small_056
  have h3 : (List.range' 1159 96).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 72) (right := 24) h2
      steps_small_057
  have h4 : (List.range' 1159 120).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 96) (right := 24) h3
      steps_small_058
  have h5 : (List.range' 1159 144).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 120) (right := 24) h4
      steps_small_059
  have h6 : (List.range' 1159 168).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 144) (right := 24) h5
      steps_small_060
  have h7 : (List.range' 1159 192).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 168) (right := 24) h6
      steps_small_061
  have h8 : (List.range' 1159 193).all stepOK = true :=
    stepOK_range_append (start := 1159) (left := 192) (right := 1) h7
      steps_small_062
  exact h8

end VOA.DeligneAudit.E7Lie
