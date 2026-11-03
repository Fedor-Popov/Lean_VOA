import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck027
import VOA.DeligneAudit.E7LieStepCheck028
import VOA.DeligneAudit.E7LieStepCheck029
import VOA.DeligneAudit.E7LieStepCheck030
import VOA.DeligneAudit.E7LieStepCheck031
import VOA.DeligneAudit.E7LieStepCheck032
import VOA.DeligneAudit.E7LieStepCheck033
import VOA.DeligneAudit.E7LieStepCheck034
import VOA.DeligneAudit.E7LieStepCheck035

/-! E₇ propagation steps 580 through 772, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok3 : (List.range' 580 193).all stepOK = true := by
  have h0 := steps_small_027
  have h1 : (List.range' 580 48).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 24) (right := 24) h0
      steps_small_028
  have h2 : (List.range' 580 72).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 48) (right := 24) h1
      steps_small_029
  have h3 : (List.range' 580 96).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 72) (right := 24) h2
      steps_small_030
  have h4 : (List.range' 580 120).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 96) (right := 24) h3
      steps_small_031
  have h5 : (List.range' 580 144).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 120) (right := 24) h4
      steps_small_032
  have h6 : (List.range' 580 168).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 144) (right := 24) h5
      steps_small_033
  have h7 : (List.range' 580 192).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 168) (right := 24) h6
      steps_small_034
  have h8 : (List.range' 580 193).all stepOK = true :=
    stepOK_range_append (start := 580) (left := 192) (right := 1) h7
      steps_small_035
  exact h8

end VOA.DeligneAudit.E7Lie
