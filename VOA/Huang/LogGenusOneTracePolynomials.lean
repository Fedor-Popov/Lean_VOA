import VOA.Huang.LogGenusOneTraceRealization

/-! Honest traces retain the actual nilpotent transport, but their coefficient
polynomials are constant by proved cyclic nilpotent trace identities. This
is proved for the actual scalar trace realization, not assumed semisimplicity. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogGenusOne
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open Module (End)
open scoped BigOperators
universe u

/-- Every positive Jordan power has zero honest trace against an actual
commuting insertion. -/
theorem trace_mul_nilpow {X : Type u} [AddCommGroup X] [Module ℂ X]
    (E J : End ℂ X) (hJ : IsNilpotent J) (hE : Commute E J) (k : ℕ) (hk : 0 < k) :
    LinearMap.trace ℂ X (E*J^k)=0 := by
  have hp : IsNilpotent (J^k) := by
    obtain ⟨q,hq⟩ := hJ
    refine ⟨q,?_⟩
    rw [← pow_mul]
    exact pow_eq_zero_of_le (by nlinarith) hq
  exact (LinearMap.isNilpotent_trace_of_isNilpotent ((hE.pow_right k).isNilpotent_mul_left hp)).eq_zero

/-- The scalar coefficient polynomial of the actual nilpotent exponential
is exactly the ordinary trace, even with nonzero Jordan blocks. -/
theorem scalarTracePolynomial_eq_constant {X : Type u} [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (E J : End ℂ X) (r : ℕ) (hr : J^r=0) (hE : Commute E J) :
    pseudoTraceExpPolynomial X (idSymmetric ℂ) E J r=
      Polynomial.C (LinearMap.trace ℂ X E) := by
  classical
  ext k
  rw [pseudoTraceExpPolynomial_coeff,Polynomial.coeff_C]
  by_cases hk : k=0
  · subst k
    rw [if_pos rfl]
    by_cases hr0 : 0 < r
    · rw [if_pos hr0,pow_zero,mul_one,pseudoTrace_idSymmetric_eq_trace]
      simp [logExpCoeff]
    · have hrz : r=0 := by omega
      subst r
      have he : E=0 := by simpa using congrArg (fun T : End ℂ X => E*T) hr
      rw [if_neg (by omega),he,map_zero]
  · rw [if_neg hk]
    by_cases hkr : k < r
    · rw [if_pos hkr,pseudoTrace_idSymmetric_eq_trace,
        trace_mul_nilpow E J ⟨r,hr⟩ hE k (by omega),mul_zero]
    · rw [if_neg hkr]

variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The scalar realization's nilpotent block is the literal Jordan block. -/
theorem actualTraceData_nilpotentPiece (N : LogVModule W M) (b : ℂ) :
    (actualTraceData N).nilpotentPiece b=weightNil N b := by
  ext y
  rw [LogPseudoTraceCommutantData.nilpotentPiece_coe]
  rfl

/-- The actual global zero-mode block commutes with the true target Jordan block. -/
theorem moduleZeroModeLinear_commute_nil (N : LogVModule W M) (b : ℂ) (v : V) :
    Commute (moduleZeroModeLinear N b v) (weightNil N b) := by
  ext y
  change logOMod N v (N.L0nil y)=N.L0nil (logOMod N v y)
  exact DFunLike.congr_fun (logOMod_commute_nil N v).eq y.val

/-- The genuine trace realization has exactly its actual ordinary trace at
every exponent; no Jordan semisimplicity hypothesis is needed. -/
theorem actualTrace_polynomial_eq_constant (N : LogVModule W M) (v : V) (e : ℂ) :
    (actualTraceData N).logPseudoTraceOnePoint v e=
      Polynomial.C (LinearMap.trace ℂ (N.weight (e+W.centralCharge/24))
        (moduleZeroModeLinear N (e+W.centralCharge/24) v)) := by
  let b := e+W.centralCharge/24
  haveI := N.finrank b
  have hr := (actualTraceData N).nilpotentPiece_pow_cutoff b
  rw [actualTraceData_nilpotentPiece] at hr
  change pseudoTraceExpPolynomial (N.weight b) (idSymmetric ℂ)
    (moduleZeroModeLinear N b v) ((actualTraceData N).nilpotentPiece b)
    ((actualTraceData N).nilpotentCutoff b)=_
  rw [actualTraceData_nilpotentPiece]
  exact scalarTracePolynomial_eq_constant _ _ _ hr (moduleZeroModeLinear_commute_nil N b v)

end VOA.Huang.LogGenusOne
