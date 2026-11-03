import VOA.DeligneAudit.D4LeviKSPairSpectatorSources
import VOA.DeligneAudit.D4LeviKSPairModuleInterface

/-! Assemble spectator transfer with the PAIR restriction cancellation. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The remaining fixed-shape evaluation identity in the PAIR assembly. -/
def PairYEvaluationBridge
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) : Prop :=
  ∀ (d : Fin b →₀ ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ),
    xyzEvaluation ρ w (pairSourceShape a b c)
        (pairYFinsuppMonomial a b c d *
          rename (pairXZSource a b c) Q) =
      pairXZRecolourOperator ρ a b c 0 Q
        (pairRadicalOp ρ
          (yModeWord ((List.range b).map (pairYExponent b d))) w)

/-- Once the fixed-shape evaluation identity is supplied, the verified
    all-b spectator transfer and restriction cancellation prove PAIR. -/
theorem pairKernelPrefix_of_sat_of_evalBridge
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (hEval : PairYEvaluationBridge ρ w a b c) :
    PairKernelPrefix ρ w m i a b c := by
  intro P hP
  let T := (pairSplitAlgebra a b c P).support
  let Q (d : Fin b →₀ ℕ) := coeff d (pairSplitAlgebra a b c P)
  let rs (d : Fin b →₀ ℕ) :=
    (List.range b).map (pairYExponent b d)
  let B := pairRadicalOp ρ (uZeroWord b) w
  let A (d : Fin b →₀ ℕ) := pairXZRecolourOperator ρ a b c 0 (Q d)
  have htrans (d : Fin b →₀ ℕ) :
      (Nat.factorial b : ℂ) • A d
          (pairRadicalOp ρ (yModeWord (rs d)) w) -
        pairAdjoint (ρ.op (17 : Fin 28)) (rs d) (A d) B ∈
          keyPrefix ρ w m i := by
    exact pairXZ_spectator_transfer ρ w m i a b c deg h hi hkey
      (Q d) (rs d) (by simp [rs])
  have hsum :
      (∑ d ∈ T, ((Nat.factorial b : ℂ) • A d
          (pairRadicalOp ρ (yModeWord (rs d)) w) -
        pairAdjoint (ρ.op (17 : Fin 28)) (rs d) (A d) B)) ∈
          keyPrefix ρ w m i := by
    apply (keyPrefix ρ w m i).sum_mem
    intro d hd
    exact htrans d
  have hzero :
      (∑ d ∈ T,
        pairAdjoint (ρ.op (17 : Fin 28)) (rs d) (A d) B) = 0 := by
    have hh := congrArg (fun F : Module.End ℂ V => F B)
      (pairXZCoeff_adjoint_sum_operator_zero ρ a b c P hP)
    simpa only [T, Q, rs, A, LinearMap.sum_apply,
      LinearMap.zero_apply] using hh
  have hfact :
      (Nat.factorial b : ℂ) •
        (∑ d ∈ T,
          A d (pairRadicalOp ρ (yModeWord (rs d)) w)) ∈
            keyPrefix ρ w m i := by
    simpa only [Finset.sum_sub_distrib, ← Finset.smul_sum,
      hzero, sub_zero] using hsum
  have heval :
      xyzEvaluation ρ w (pairSourceShape a b c) P =
        ∑ d ∈ T,
          A d (pairRadicalOp ρ (yModeWord (rs d)) w) := by
    conv_lhs => rw [pairY_decomposition a b c P]
    simp only [map_sum, T, Q, A, rs]
    apply Finset.sum_congr rfl
    intro d hd
    exact hEval d (Q d)
  rw [← heval] at hfact
  have hf : (Nat.factorial b : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero b
  have hscaled := (keyPrefix ρ w m i).smul_mem
    (Nat.factorial b : ℂ)⁻¹ hfact
  simpa only [smul_smul, inv_mul_cancel₀ hf, one_smul]
    using hscaled

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairKernelPrefix_of_sat_of_evalBridge
