import VOA.Classification.COne.QExpWeightOneRootChange
import VOA.Classification.COne.QExpWeightTwoSturm

/-! # The weight-two reduction with only the theta analytic input and jet matching

The transformation requirement has been discharged conditionally on the single
explicit theta Fourier input. The independent product-jet matching input is
unchanged; neither remaining input is asserted here.
-/

namespace VOA.Classification.COne.SSHecke

theorem qExpPrinciple24Away_two_of_thetaFourier_and_sturmMatching
    (hf : WeightOneThetaFourier24) (hmatch : FullLevelWeightTwoSturmMatching24) :
    QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_slash_and_sturmMatching
    (fullLevelWeightOneSlash24_of_thetaFourier hf) hmatch

end VOA.Classification.COne.SSHecke
