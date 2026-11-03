import VOA.DeligneAudit.D4LeviKSPairUnconditional

/-! Linear extension of the positional power-sum intertwining identity. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

variable {σ V : Type*} [Fintype σ] [AddCommGroup V] [Module ℂ V]

/-- A positional power-sum identity on basis words extends to every linear
    combination of mode words. -/
theorem modeWordEvaluation_psum_intertwine
    (f : (σ →₀ ℕ) → V) (H : Module.End ℂ V) (c : ℂ) (r : ℕ)
    (hmono : ∀ a : σ →₀ ℕ,
      H (f a) = c • ∑ i : σ, f (Finsupp.single i r + a))
    (W : MvPolynomial σ ℂ) :
    H (modeWordEvaluation σ f W) =
      c • modeWordEvaluation σ f
        (symmetricShiftAction σ (psum σ ℂ r) W) := by
  induction W using MvPolynomial.induction_on' with
  | monomial a t =>
      have hm : (monomial a t : MvPolynomial σ ℂ) =
          t • modeMonomial σ a := by
        simp only [modeMonomial, smul_monomial, smul_eq_mul, mul_one]
      have hbase : H (modeWordEvaluation σ f (modeMonomial σ a)) =
          c • modeWordEvaluation σ f
            (symmetricShiftAction σ (psum σ ℂ r) (modeMonomial σ a)) := by
        rw [modeWordEvaluation_monomial, symmetricShiftAction_psum]
        simp only [map_sum, modeWordEvaluation_monomial]
        exact hmono a
      rw [hm, map_smul, map_smul, map_smul, hbase]
      rw [map_smul]
      exact smul_comm t c
        (modeWordEvaluation σ f
          (symmetricShiftAction σ (psum σ ℂ r) (modeMonomial σ a)))
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, smul_add]

/-- Positional Cartan identities and invariant prefixes suffice to close
    evaluated word relations under every symmetric mode polynomial. -/
theorem symmetricShiftAction_mem_of_intertwine
    (f : (σ →₀ ℕ) → V) (N : Submodule ℂ V)
    (H : ℕ → Module.End ℂ V) (c : ℕ → ℂ)
    (hmono : ∀ r a,
      H r (f a) = c r • ∑ i : σ, f (Finsupp.single i r + a))
    (hc : ∀ r, c r ≠ 0)
    (hInv : ∀ r x, x ∈ N → H r x ∈ N)
    (P : MvPolynomial σ ℂ) (hP : P ∈ symmetricSubalgebra σ ℂ)
    (W : MvPolynomial σ ℂ) (hW : modeWordEvaluation σ f W ∈ N) :
    modeWordEvaluation σ f (symmetricShiftAction σ P W) ∈ N := by
  apply symmetricShiftAction_evaluation_mem σ f N _ P hP W hW
  intro r U hU
  have hh := hInv r _ hU
  rw [modeWordEvaluation_psum_intertwine f (H r) (c r) r (hmono r) U] at hh
  have hscaled := N.smul_mem (c r)⁻¹ hh
  simpa only [smul_smul, inv_mul_cancel₀ (hc r), one_smul] using hscaled

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.modeWordEvaluation_psum_intertwine
#print axioms VOA.DeligneAudit.D4Levi.symmetricShiftAction_mem_of_intertwine
