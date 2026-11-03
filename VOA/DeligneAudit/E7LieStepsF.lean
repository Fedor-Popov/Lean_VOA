import VOA.DeligneAudit.E7LieStepCheckAssembly
import VOA.DeligneAudit.E7LieStepCheck045
import VOA.DeligneAudit.E7LieStepCheck046
import VOA.DeligneAudit.E7LieStepCheck047
import VOA.DeligneAudit.E7LieStepCheck048
import VOA.DeligneAudit.E7LieStepCheck049
import VOA.DeligneAudit.E7LieStepCheck050
import VOA.DeligneAudit.E7LieStepCheck051
import VOA.DeligneAudit.E7LieStepCheck052
import VOA.DeligneAudit.E7LieStepCheck053

/-! E₇ propagation steps 966 through 1158, assembled from small kernel checks. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_ok5 : (List.range' 966 193).all stepOK = true := by
  have h0 := steps_small_045
  have h1 : (List.range' 966 48).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 24) (right := 24) h0
      steps_small_046
  have h2 : (List.range' 966 72).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 48) (right := 24) h1
      steps_small_047
  have h3 : (List.range' 966 96).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 72) (right := 24) h2
      steps_small_048
  have h4 : (List.range' 966 120).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 96) (right := 24) h3
      steps_small_049
  have h5 : (List.range' 966 144).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 120) (right := 24) h4
      steps_small_050
  have h6 : (List.range' 966 168).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 144) (right := 24) h5
      steps_small_051
  have h7 : (List.range' 966 192).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 168) (right := 24) h6
      steps_small_052
  have h8 : (List.range' 966 193).all stepOK = true :=
    stepOK_range_append (start := 966) (left := 192) (right := 1) h7
      steps_small_053
  exact h8

end VOA.DeligneAudit.E7Lie
