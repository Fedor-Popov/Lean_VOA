import VOA.Classification.COne.OrbOctaRCMeasurements
import VOA.Classification.COne.OrbOctaRCTransport
import VOA.Classification.COne.OrbA4Assembly

/-! The octahedral conformal nilpotence certificate and the final B2 input. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne
open VOA VertexOperatorAlgebra OrbOctaR OrbC2b OrbC2c

namespace OrbOctaRC

theorem candidate_remainder32 :
    W.smul X (-1) X -
      ((candidateA32 : ℂ) • ((W.L (-2)) ^ 16) W.vacuum +
        (candidateB32 : ℂ) • ((W.L (-2)) ^ 8) X) ∈
          virError W W.vacuum ⊔ virError W X := by
  have hz : chargedProbe dualState16 (((W.L (-2)) ^ 16) W.vacuum) = 0 :=
    charged_vacuum_tower _ _
  have hx : chargedProbe dualState16 (((W.L (-2)) ^ 8) X) = 2 :=
    charged_X_tower _ _ charged_norm16
  apply mode_remainder_of_measurements 16 (by decide) (by decide)
    (candidateA32 : ℂ) (candidateB32 : ℂ) octaProbe (chargedProbe dualState16)
    errors_le_ker_octaProbe chargedProbe16_errors
  · rw [hz, hx, octaProbe_L_pow, octaProbe_vacuum]
    norm_num
  · rw [octaProbe_L_pow, octaProbe_L_pow, octaProbe_vacuum, octaProbe_X, mul_one]
    simpa only [mul_assoc] using neutral_mode32
  · rw [hz, hx, mul_zero, zero_add]
    exact charged_mode32.trans (mul_comm _ _)

theorem candidate_remainder34 :
    W.smul X (-3) X -
      ((candidateA34 : ℂ) • ((W.L (-2)) ^ 17) W.vacuum +
        (candidateB34 : ℂ) • ((W.L (-2)) ^ 9) X) ∈
          virError W W.vacuum ⊔ virError W X := by
  have hz : chargedProbe dualState18 (((W.L (-2)) ^ 17) W.vacuum) = 0 :=
    charged_vacuum_tower _ _
  have hx : chargedProbe dualState18 (((W.L (-2)) ^ 9) X) = 2 :=
    charged_X_tower _ _ charged_norm18
  apply mode_remainder_of_measurements 17 (by decide) (by decide)
    (candidateA34 : ℂ) (candidateB34 : ℂ) octaProbe (chargedProbe dualState18)
    errors_le_ker_octaProbe chargedProbe18_errors
  · rw [hz, hx, octaProbe_L_pow, octaProbe_vacuum]
    norm_num
  · rw [octaProbe_L_pow, octaProbe_L_pow, octaProbe_vacuum, octaProbe_X, mul_one]
    simpa only [mul_assoc] using neutral_mode34
  · rw [hz, hx, mul_zero, zero_add]
    exact charged_mode34.trans (mul_comm _ _)

theorem conformal_power25_zero :
    (exceptionalConformalEnd W ^ 25) (mk₂ W W.vacuum) = 0 :=
  nilpotent_of_candidate_remainders candidate_remainder32 candidate_remainder34

end OrbOctaRC

namespace OrbOcta

theorem octahedralConformalNilpotent_holds : OctahedralConformalNilpotent :=
  ⟨25, OrbOctaRC.conformal_power25_zero⟩

theorem involutionMovingPairSpan_holds : OrbC2b.InvolutionMovingPairSpan :=
  involutionMovingPairSpan_of_octahedralConformalNilpotent octahedralConformalNilpotent_holds

end OrbOcta

theorem solvableExceptionalOrbifoldC2Fact_holds : SolvableExceptionalOrbifoldC2Fact :=
  OrbA4.solvableExceptionalOrbifoldC2Fact_of_octaNilpotent
    OrbOcta.octahedralConformalNilpotent_holds

end VOA.Classification.COne
